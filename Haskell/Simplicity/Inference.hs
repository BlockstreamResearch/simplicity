{-# LANGUAGE DeriveTraversable, FlexibleInstances, GADTs, MultiParamTypeClasses, ScopedTypeVariables #-}
-- | This module defines a type for untyped Simplicity DAGs as well as a type checking function to convert such a DAG into a well-typed Simplicity expression.
module Simplicity.Inference
  (
  -- * Type checking untyped Simplicity
    typeCheckDag
  -- * Untyped Simplicity
  , UntypedTermF
  , UntypedSimplicityDag
  , WitnessData, witnessData
  -- ** Constructors for untyped Simplicity
  , uIden, uUnit, uInjl, uInjr
  , uTake, uDrop, uComp, uCase, uPair, uDisconnect
  , uHidden, uWitness, uPrim, uJet, uFail
  -- ** Match expressions for untyped Simplicity
  , isUIden, isUUnit, isUInjl, isUInjr
  , isUTake, isUDrop, isUComp, isUCase, isUPair, isUDisconnect
  , isUHidden, isUWitness, isUPrim
  ) where

import Prelude hiding (fail, take, drop)

import Control.Arrow ((+++), left)
import Control.Monad (foldM)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Except (ExceptT, runExceptT, throwE)
import Control.Unification (Fallible(..), UTerm(..), (=:=), applyBindingsAll, freeVar, unfreeze)
import Control.Unification.STVar (STBinding, STVar, runSTBinding)
import Control.Unification.Types (UFailure)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Fixedpoint (Fix(..))
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq, (|>), (!?), empty, index, mapWithIndex, ViewR(..), viewr)
import Data.Traversable (foldMapDefault, fmapDefault)
import Data.Type.Equality ((:~:)(Refl))
import qualified Data.Vector.Unboxed as UV

import Simplicity.Digest
import Simplicity.Primitive
import Simplicity.MerkleRoot
import Simplicity.Serialization
import Simplicity.Term
import Simplicity.Ty
import Simplicity.Ty.Word

-- (UTy a) is the type of Simplicity types augmented with unification variables, a.
type UTy v = UTerm TyF v

-- Convert a Simplicity type with unification variables into a regular Ty.
-- Any remaining unification variables are turned into unit types, hence the name 'unital'.
unital :: UTy v -> Ty
unital (UVar _) = one
unital (UTerm t) = Fix (unital <$> t)

{- Consider replacing with Vector Bit from https://github.com/mokus0/bitvec when issues are resolved.
   see https://github.com/mokus0/bitvec/issues/3 & https://github.com/mokus0/bitvec/issues/4. -}
-- | Untyped witness data is an unstructured block of bits.
-- The data cannot be interpreted without first knowing its Simplicity type.
-- After type inference, this block of data can be parsed into a value for a Simplicity type.
--
-- We represent this block of bits as a unboxed vector of 'Bool's.
type WitnessData = UV.Vector Bool

witnessData :: TyC a => a -> WitnessData
witnessData = UV.fromList . putValue

-- An open recursive type for untyped Simplicity terms with type annotations.
-- The 'ty' parameter holds the typing annotations, which can be 'UTy v', or 'Ty', etc.
-- The 'a' parameter holds the (open) recursive subexpressions.
data TermF a ty = Iden ty
                | Unit ty
                | Injl ty ty ty a
                | Injr ty ty ty a
                | Take ty ty ty a
                | Drop ty ty ty a
                | Comp ty ty ty a a
                | Case ty ty ty ty a a
                | Pair ty ty ty a a
                | Disconnect ty ty ty ty a a
                | Hidden ty ty Hash256
                | Witness ty ty WitnessData
                | Prim (SomeArrow Prim)
--              | Jet JetID
  deriving (Functor, Foldable, Traversable)

instance (Eq a, Eq ty) => Eq (TermF a ty) where
  (Iden a0) == (Iden a1) = a0 == a1
  (Unit a0) == (Unit a1) = a0 == a1
  (Injl a0 b0 c0 t0) == (Injl a1 b1 c1 t1) = [a0,b0,c0] == [a1,b1,c1] && t0 == t1
  (Injr a0 b0 c0 t0) == (Injr a1 b1 c1 t1) = [a0,b0,c0] == [a1,b1,c1] && t0 == t1
  (Take a0 b0 c0 t0) == (Take a1 b1 c1 t1) = [a0,b0,c0] == [a1,b1,c1] && t0 == t1
  (Drop a0 b0 c0 t0) == (Drop a1 b1 c1 t1) = [a0,b0,c0] == [a1,b1,c1] && t0 == t1
  (Comp a0 b0 c0 s0 t0) == (Comp a1 b1 c1 s1 t1) = [a0,b0,c0] == [a1,b1,c1] && [s0,t0] == [s1,t1]
  (Case a0 b0 c0 d0 s0 t0) == (Case a1 b1 c1 d1 s1 t1) = [a0,b0,c0,d0] == [a1,b1,c1,d1] && [s0,t0] == [s1,t1]
  (Pair a0 b0 c0 s0 t0) == (Pair a1 b1 c1 s1 t1) = [a0,b0,c0] == [a1,b1,c1] && [s0,t0] == [s1,t1]
  (Disconnect a0 b0 c0 d0 s0 t0) == (Disconnect a1 b1 c1 d1 s1 t1) = [a0,b0,c0,d0] == [a1,b1,c1,d1] && [s0,t0] == [s1,t1]
  (Hidden a0 b0 h0) == (Hidden a1 b1 h1) = [a0,b0] == [a1,b1] && h0 == h1
  (Witness a0 b0 w0) == (Witness a1 b1 w1) = [a0,b0] == [a1,b1] && w0 == w1
  (Prim (SomeArrow p0 ra0 rb0)) == (Prim (SomeArrow p1 ra1 rb1)) = fromMaybe False $ do
    Refl <- equalTyReflect ra0 ra1
    Refl <- equalTyReflect rb0 rb1
    return $ p0 == p1
  _ == _ = False

instance (Show a, Show ty) => Show (TermF a ty) where
  showsPrec p (Iden a) = showParen (10 < p) $ showString "Iden " . showsPrec 11 a
  showsPrec p (Unit a) = showParen (10 < p) $ showString "Unit " . showsPrec 11 a
  showsPrec p (Injl a b c t) = showParen (10 < p)
                             $ showString "Injl " . showsPrec 11 a
                             . showString " " . showsPrec 11 b
                             . showString " " . showsPrec 11 c
                             . showString " " . showsPrec 11 t
  showsPrec p (Injr a b c t) = showParen (10 < p)
                             $ showString "Injr " . showsPrec 11 a
                             . showString " " . showsPrec 11 b
                             . showString " " . showsPrec 11 c
                             . showString " " . showsPrec 11 t
  showsPrec p (Take a b c t) = showParen (10 < p)
                             $ showString "Take " . showsPrec 11 a
                             . showString " " . showsPrec 11 b
                             . showString " " . showsPrec 11 c
                             . showString " " . showsPrec 11 t
  showsPrec p (Drop a b c t) = showParen (10 < p)
                             $ showString "Drop " . showsPrec 11 a
                             . showString " " . showsPrec 11 b
                             . showString " " . showsPrec 11 c
                             . showString " " . showsPrec 11 t
  showsPrec p (Comp a b c s t) = showParen (10 < p)
                               $ showString "Comp " . showsPrec 11 a
                               . showString " " . showsPrec 11 b
                               . showString " " . showsPrec 11 c
                               . showString " " . showsPrec 11 s
                               . showString " " . showsPrec 11 t
  showsPrec p (Case a b c d s t) = showParen (10 < p)
                                 $ showString "Case " . showsPrec 11 a
                                 . showString " " . showsPrec 11 b
                                 . showString " " . showsPrec 11 c
                                 . showString " " . showsPrec 11 d
                                 . showString " " . showsPrec 11 s
                                 . showString " " . showsPrec 11 t
  showsPrec p (Pair a b c s t) = showParen (10 < p)
                               $ showString "Pair " . showsPrec 11 a
                               . showString " " . showsPrec 11 b
                               . showString " " . showsPrec 11 c
                               . showString " " . showsPrec 11 s
                               . showString " " . showsPrec 11 t
  showsPrec p (Disconnect a b c d s t) = showParen (10 < p)
                                       $ showString "Disconnect " . showsPrec 11 a
                                       . showString " " . showsPrec 11 b
                                       . showString " " . showsPrec 11 c
                                       . showString " " . showsPrec 11 d
                                       . showString " " . showsPrec 11 s
                                       . showString " " . showsPrec 11 t
  showsPrec p (Hidden a b h) = showParen (10 < p)
                             $ showString "Hidden " . showsPrec 11 a
                             . showString " " . showsPrec 11 b
                             . showString " " . showsPrec 11 h
  showsPrec p (Witness a b w) = showParen (10 < p)
                              $ showString "Witness " . showsPrec 11 a
                              . showString " " . showsPrec 11 b
                              . showString " " . showsPrec 11 w
  showsPrec p (Prim (SomeArrow prim _ _)) = showParen (10 < p)
                                          $ showString "Prim "
                                          . (showParen True $ showString "someArrow " . showString (primName prim))

-- Given a 'UTy v' annonated Simplicity 'TermF', return the implied input and output types given the annotations.
termFArrow :: TermF a (UTy v) -> (UTy v, UTy v)
termFArrow (Iden a) = (a, a)
termFArrow (Unit a) = (a, UTerm One)
termFArrow (Injl a b c _) = (a, UTerm (Sum b c))
termFArrow (Injr a b c _) = (a, UTerm (Sum b c))
termFArrow (Take a b c _) = (UTerm (Prod a b), c)
termFArrow (Drop a b c _) = (UTerm (Prod a b), c)
termFArrow (Comp a b c _ _) = (a, c)
termFArrow (Case a b c d _ _) = (UTerm (Prod (UTerm (Sum a b)) c), d)
termFArrow (Pair a b c _ _) = (a, UTerm (Prod b c))
termFArrow (Disconnect a b c d _ _) = (a, UTerm (Prod b d))
termFArrow (Hidden a b _) = (a, b)
termFArrow (Witness a b _) = (a, b)
termFArrow (Prim (SomeArrow p ra rb)) = (unfreeze (unreflect ra), unfreeze (unreflect rb))

-- | An open recursive type for untyped Simplicity expressions.
newtype UntypedTermF a = Untyped (TermF a ())
  deriving Eq

instance Show a => Show (UntypedTermF a) where
  showsPrec p (Untyped (Iden _)) = showString "uIden"
  showsPrec p (Untyped (Unit _)) = showString "uUnit"
  showsPrec p (Untyped (Injl _ _ _ t)) = showParen (10 < p)
                                       $ showString "uInjl " . showsPrec 11 t
  showsPrec p (Untyped (Injr _ _ _ t)) = showParen (10 < p)
                                       $ showString "uInjr " . showsPrec 11 t
  showsPrec p (Untyped (Take _ _ _ t)) = showParen (10 < p)
                                       $ showString "uTake " . showsPrec 11 t
  showsPrec p (Untyped (Drop _ _ _ t)) = showParen (10 < p)
                                       $ showString "uDrop " . showsPrec 11 t
  showsPrec p (Untyped (Comp _ _ _ s t)) = showParen (10 < p)
                                         $ showString "uComp " . showsPrec 11 s
                                         . showString " " . showsPrec 11 t
  showsPrec p (Untyped (Case _ _ _ _ s t)) = showParen (10 < p)
                                           $ showString "uCase " . showsPrec 11 s
                                           . showString " " . showsPrec 11 t
  showsPrec p (Untyped (Pair _ _ _ s t)) = showParen (10 < p)
                                         $ showString "uPair " . showsPrec 11 s
                                         . showString " " . showsPrec 11 t
  showsPrec p (Untyped (Disconnect _ _ _ _ s t)) = showParen (10 < p)
                                                 $ showString "uDisconnect " . showsPrec 11 s
                                                 . showString " " . showsPrec 11 t
  showsPrec p (Untyped (Hidden _ _ h)) = showParen (10 < p)
                                       $ showString "Hidden " . showsPrec 11 h
  showsPrec p (Untyped (Witness _ _ w)) = showParen (10 < p)
                                        $ showString "Witness " . showsPrec 11 w
  showsPrec p (Untyped (Prim (SomeArrow prim _ _))) = showParen (10 < p)
                                                    $ showString "uPrim "
                                                    . (showParen True $ showString "someArrow " . showString (primName prim))

instance Functor UntypedTermF where
  fmap = fmapDefault

instance Foldable UntypedTermF where
  foldMap = foldMapDefault

instance Traversable UntypedTermF where
  traverse f (Untyped (Iden a)) = pure (Untyped (Iden a))
  traverse f (Untyped (Unit a)) = pure (Untyped (Unit a))
  traverse f (Untyped (Injl a b c x)) = Untyped <$> (Injl a b c <$> f x)
  traverse f (Untyped (Injr a b c x)) = Untyped <$> (Injr a b c <$> f x)
  traverse f (Untyped (Take a b c x)) = Untyped <$> (Take a b c <$> f x)
  traverse f (Untyped (Drop a b c x)) = Untyped <$> (Drop a b c <$> f x)
  traverse f (Untyped (Comp a b c x y)) = Untyped <$> (Comp a b c <$> f x <*> f y)
  traverse f (Untyped (Case a b c d x y)) = Untyped <$> (Case a b c d <$> f x <*> f y)
  traverse f (Untyped (Pair a b c x y)) = Untyped <$> (Pair a b c <$> f x <*> f y)
  traverse f (Untyped (Disconnect a b c d x y)) = Untyped <$> (Disconnect a b c d <$> f x <*> f y)
  traverse f (Untyped (Hidden a b x)) = pure (Untyped (Hidden a b x))
  traverse f (Untyped (Witness a b x)) = pure (Untyped (Witness a b x))
  traverse f (Untyped (Prim p)) = pure (Untyped (Prim p))

-- Constructors for 'UntypedTermF a'.
uIden = Untyped (Iden ())
uUnit = Untyped (Unit ())
uInjl x = Untyped (Injl () () () x)
uInjr x = Untyped (Injr () () () x)
uTake x = Untyped (Take () () () x)
uDrop x = Untyped (Drop () () () x)
uComp x y = Untyped (Comp () () () x y)
uCase x y = Untyped (Case () () () () x y)
uPair x y = Untyped (Pair () () () x y)
uDisconnect x y = Untyped (Disconnect () () () () x y)

-- | Assertions are not directly represented in 'UntypedSimplicityDag'.
-- Instead assertions are represented by a 'uCase' node where the missing branch is replaced with a 'uHidden' node.
uHidden x = Untyped (Hidden () () x)
uWitness x = Untyped (Witness () () x)
uPrim p = Untyped (Prim p)
-- | :TODO: NOT YET IMPLEMENTED
uJet = error ":TODO: deserialization of jet nodes not yet implemented"
-- | :TODO: NOT YET IMPLEMENTED
uFail b = error ":TODO: deserialization of fail nodes not yet implemented"

-- Matches for 'UntypedTermF a'.
isUIden (Untyped (Iden _)) = Just ()
isUIden _ = Nothing
isUUnit (Untyped (Unit _)) = Just ()
isUUnit _ = Nothing
isUInjl (Untyped (Injl _ _ _ x)) = Just x
isUInjl _ = Nothing
isUInjr (Untyped (Injr _ _ _ x)) = Just x
isUInjr _ = Nothing
isUTake (Untyped (Take _ _ _ x)) = Just x
isUTake _ = Nothing
isUDrop (Untyped (Drop _ _ _ x)) = Just x
isUDrop _ = Nothing
isUComp (Untyped (Comp _ _ _ x y)) = Just (x,y)
isUComp _ = Nothing
isUCase (Untyped (Case _ _ _ _ x y)) = Just (x,y)
isUCase _ = Nothing
isUPair (Untyped (Pair _ _ _ x y)) = Just (x,y)
isUPair _ = Nothing
isUDisconnect (Untyped (Disconnect _ _ _ _ x y)) = Just (x,y)
isUDisconnect _ = Nothing
isUHidden (Untyped (Hidden _ _ x)) = Just x
isUHidden _ = Nothing
isUWitness (Untyped (Witness _ _ x)) = Just x
isUWitness _ = Nothing
isUPrim (Untyped (Prim p)) = Just p
isUPrim _ = Nothing

-- InferenceError holds the possible errors that can occur during the 'inference' step.
data InferenceError s = UnificationFailure (UFailure TyF (STVar s TyF))
                      | IndexError Int Integer
                      | Overflow
                      deriving Show

instance Fallible TyF (STVar s TyF) (InferenceError s) where
  occursFailure v t = UnificationFailure (occursFailure v t)
  mismatchFailure t1 t2 = UnificationFailure (mismatchFailure t1 t2)

-- | Untyped Simplicity expressions with explicit sharing of subexpressions.
--
-- Every node in an Simplicity expression is an element of a vector with indices that reference the relative locations of their immediate subexpressions within that vector.
-- This reference is the difference in positions between refering node's position and the referred node's position.
-- The number @1@ is a reference to the immediately preciding node and the number @0@ is not allowed as it would imply a node is refering to itself.
--
-- The last element of the vector is the root of the Simplicity expression DAG.
--
-- Invariant:
--
-- @
--     0 \<= /i/ && /i/ \< 'length' /v/ ==> 'Foldable.all' (\\x -> 0 < x && x <= /i/) (/v/ '!!' /i/)
-- @
type UntypedSimplicityDag = [UntypedTermF Integer]

-- 'inference' takes an 'UntypedSimplicityDag' and adds suitiable type annotations to the nodes in the DAG as well as unification constraints.
-- This can cause unification failures, however the occurs check isn't performed in this step.
-- This function also checks that the provided DAG is sorted in topological order.
inference :: UntypedSimplicityDag ->
             ExceptT (InferenceError s) (STBinding s) (Seq (TermF Int (UTy (STVar s TyF))))
inference = foldM loop empty
 where
  tyWord256 = unreflect (reify :: TyReflect Word256)
  loop :: Seq (TermF Int (UTy (STVar s TyF)))
       -> UntypedTermF Integer
       -> ExceptT (InferenceError s) (STBinding s) (Seq (TermF Int (UTy (STVar s TyF))))
  loop output node = (output |>) <$> go node
   where
    fresh :: ExceptT (InferenceError s) (STBinding s) (UTy (STVar s TyF))
    fresh = UVar <$> lift freeVar
    lenOutput = length output
    offsetToIndex i = lenOutput - fromInteger i
    lookup i | i <= toInteger (maxBound :: Int) = maybe (throwE (IndexError lenOutput i)) return (output !? offsetToIndex i)
             | otherwise = throwE Overflow
    go (Untyped (Iden _)) = Iden <$> fresh
    go (Untyped (Unit _)) = Unit <$> fresh
    go (Untyped (Injl _ _ _ it)) = do
      (a,b) <- termFArrow <$> lookup it
      c <- fresh
      return (Injl a b c (offsetToIndex it))
    go (Untyped (Injr _ _ _ it)) = do
      (a,c) <- termFArrow <$> lookup it
      b <- fresh
      return (Injr a b c (offsetToIndex it))
    go (Untyped (Take _ _ _ it)) = do
      (a,c) <- termFArrow <$> lookup it
      b <- fresh
      return (Take a b c (offsetToIndex it))
    go (Untyped (Drop _ _ _ it)) = do
      (b,c) <- termFArrow <$> lookup it
      a <- fresh
      return (Drop a b c (offsetToIndex it))
    go (Untyped (Comp _ _ _ is it)) = do
      (a,b0) <- termFArrow <$> lookup is
      (b1,c) <- termFArrow <$> lookup it
      b <- b0 =:= b1
      return (Comp a b c (offsetToIndex is) (offsetToIndex it))
    go (Untyped (Case _ _ _ _ is it)) = do
      (ac,d0) <- termFArrow <$> lookup is
      (bc,d1) <- termFArrow <$> lookup it
      a <- fresh
      b <- fresh
      c <- fresh
      _ <- UTerm (Prod a c) =:= ac
      _ <- UTerm (Prod b c) =:= bc
      d <- d0 =:= d1
      return (Case a b c d (offsetToIndex is) (offsetToIndex it))
    go (Untyped (Pair _ _ _ is it)) = do
      (a0,b) <- termFArrow <$> lookup is
      (a1,c) <- termFArrow <$> lookup it
      a <- a0 =:= a1
      return (Pair a b c (offsetToIndex is) (offsetToIndex it))
    go (Untyped (Disconnect _ _ _ _ is it)) = do
      (aw,bc) <- termFArrow <$> lookup is
      (c,d) <- termFArrow <$> lookup it
      a <- fresh
      b <- fresh
      _ <- UTerm (Prod a (unfreeze tyWord256)) =:= aw
      _ <- UTerm (Prod b c) =:= bc
      return (Disconnect a b c d (offsetToIndex is) (offsetToIndex it))
    go (Untyped (Hidden _ _ h)) = Hidden <$> fresh <*> fresh <*> pure h
    go (Untyped (Witness _ _ w)) = Witness <$> fresh <*> fresh <*> pure w
    go (Untyped (Prim p)) = pure (Prim p)

-- :TODO: It should be possible to make a streamable variant of this (a la pipes) with type (MonadFail m) => m (Maybe (UntypedSimplicityF Integer)) -> m (term a b)
-- | Transform a 'UntypedSimplicityDag' with explicit sharing into a well-typed Simplicity expression of a specified type.
-- Various errors can occur if the input DAG isn't well-typed or well-formed.
-- In such cases a 'String' describing the error is returned.
--
-- Note: the one calling 'typeCheckDag' determines the input and output Simplicity types of the resulting Simplicity expression.
-- It is *not* inferered from the DAG input.
typeCheckDag :: forall term a b. (Simplicity term, TyC a, TyC b) => UntypedSimplicityDag -> Either String (term a b)
typeCheckDag v = typeCheckTerm =<< annotated
 where
   a0 :: TyReflect a
   a0 = reify
   b0 :: TyReflect b
   b0 = reify
   inferenced :: forall s. ExceptT (InferenceError s) (STBinding s) (Seq (TermF Int (UTy (STVar s TyF))))
   inferenced = do
     ev <- inference v
     _ <- case viewr ev of
         EmptyR -> return ()
         _ :> end -> do
           let (a1, b1) = termFArrow end
           _ <- a1 =:= unfreeze (unreflect a0)
           _ <- b1 =:= unfreeze (unreflect b0)
           return ()
     return ev
   annotated :: Either String (Seq (TermF Int Ty))
   annotated = runSTBinding ((show +++ (getCompose . fmap unital)) <$> runExceptT ((Compose <$> inferenced) >>= applyBindingsAll))
   typeCheckTerm s = case viewr typeCheckedDag of
     _ :> Right (SomeArrow t ra rb) -> maybe (error "Simplicity.Inference.typeCheckDag: unexpect mismatched type at end.") return $ do
                                         Refl <- equalTyReflect ra a0
                                         Refl <- equalTyReflect rb b0
                                         return t
     _ :> Left s -> Left s
     EmptyR -> Left "Simplicity.Inference.typeCheckDag: empty vector input."
    where
     assertEqualTyReflect a b = maybe err Right (equalTyReflect a b)
      where
       err = Left "Simplicity.Inference.typeCheckDag: unexpected mismatched type"
     typeCheckedDag = mapWithIndex (\i -> left (++ " at index " ++ show i ++ ".") . typeCheck) s
     typeCheck :: TermF Int Ty -> Either String (SomeArrow term)
     typeCheck (Iden a) = case reflect a of
                            SomeTy ra -> return (SomeArrow iden ra ra)
     typeCheck (Unit a) = case reflect a of
                            SomeTy ra -> return (SomeArrow unit ra OneR)
     typeCheck (Injl a b c it) = case reflect c of
                                  SomeTy rc -> do
                                    SomeArrow t ra rb <- index typeCheckedDag it
                                    return (SomeArrow (injl t) ra (SumR rb rc))
     typeCheck (Injr a b c it) = case reflect b of
                                  SomeTy rb -> do
                                    SomeArrow t ra rc <- index typeCheckedDag it
                                    return (SomeArrow (injr t) ra (SumR rb rc))
     typeCheck (Take a b c it) = case reflect b of
                                  SomeTy rb -> do
                                    SomeArrow t ra rc <- index typeCheckedDag it
                                    return (SomeArrow (take t) (ProdR ra rb) rc)
     typeCheck (Drop a b c it) = case reflect a of
                                  SomeTy ra -> do
                                    SomeArrow t rb rc <- index typeCheckedDag it
                                    return (SomeArrow (drop t) (ProdR ra rb) rc)
     typeCheck (Comp a b c is it) = do
                                      SomeArrow s ra rb0 <- index typeCheckedDag is
                                      SomeArrow t rb1 rc <- index typeCheckedDag it
                                      Refl <- assertEqualTyReflect rb0 rb1
                                      return (SomeArrow (comp s t) ra rc)
     typeCheck (Case a b c d is it) | (Hidden _ _ hs) <- index s is = case reflect a of
                                                                        SomeTy ra -> do
                                                                          SomeArrow t (ProdR rb rc) rd <- index typeCheckedDag it
                                                                          return (SomeArrow (assertr hs t) (ProdR (SumR ra rb) rc) rd)
                                    | (Hidden _ _ ht) <- index s is = case reflect b of
                                                                        SomeTy rb -> do
                                                                          SomeArrow s (ProdR ra rc) rd <- index typeCheckedDag is
                                                                          return (SomeArrow (assertl s ht) (ProdR (SumR ra rb) rc) rd)
                                    | otherwise = do
                                                    SomeArrow s (ProdR ra rc0) rd0 <- index typeCheckedDag is
                                                    SomeArrow t (ProdR rb rc1) rd1 <- index typeCheckedDag it
                                                    Refl <- assertEqualTyReflect rc0 rc1
                                                    Refl <- assertEqualTyReflect rd0 rd1
                                                    return (SomeArrow (match s t) (ProdR (SumR ra rb) rc0) rd0)
     typeCheck (Pair a b c is it) = do SomeArrow s ra0 rb <- index typeCheckedDag is
                                       SomeArrow t ra1 rc <- index typeCheckedDag it
                                       Refl <- assertEqualTyReflect ra0 ra1
                                       return (SomeArrow (pair s t) ra0 (ProdR rb rc))
     typeCheck (Disconnect a b c d is it) = do
                                              SomeArrow s (ProdR ra rw) (ProdR rb rc0) <- index typeCheckedDag is
                                              SomeArrow t rc1 rd <- index typeCheckedDag it
                                              Refl <- assertEqualTyReflect rw (reify :: TyReflect Word256)
                                              Refl <- assertEqualTyReflect rc0 rc1
                                              return (SomeArrow (disconnect s t) ra (ProdR rb rd))
     typeCheck (Hidden _ _ _) = Left "Simplicity.Inference.typeCheckDag: encountered illegal use of Hidden node"
     typeCheck (Witness a b w) = case (reflect a, reflect b) of
                                   (SomeTy ra, SomeTy rb) -> do
                                      vb <- maybe err return $ evalExactVector (getValueR rb) w
                                      return (SomeArrow (witness vb) ra rb)
      where
       err = Left "Simplicity.Inference.typeCheckDag: decode error in Witness value"
     typeCheck (Prim (SomeArrow p ra rb)) = return (SomeArrow (primitive p) ra rb)
