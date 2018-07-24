{-# LANGUAGE DeriveTraversable, FlexibleInstances, GADTs, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables #-}
-- | This module defines a type for Simplicity DAGs (directed acyclic graph) as well as a type checking function to convert such a DAG into a well-typed Simplicity expression.
module Simplicity.Inference
  (
  -- * Type checking untyped Simplicity
    typeInference
  , typeCheck
  -- * Simplicity with type annotations
  , TermF(..)
  , UntypedTermF
  , SimplicityDag
  , WitnessData(..), getWitnessData
  -- * Constructors for 'UntypedTermF'.
  -- | There is no @uPrim@.  You must use 'Simplicity.Inference.Prim' instead.
  , uIden, uUnit, uInjl, uInjr
  , uTake, uDrop, uComp, uCase, uPair, uDisconnect
  , uHidden, uWitness, uJet, uFail
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

{- Consider replacing @UV.Vector Bool@ with @Vector Bit@ from https://github.com/mokus0/bitvec when issues are resolved.
   see https://github.com/mokus0/bitvec/issues/3 & https://github.com/mokus0/bitvec/issues/4. -}
-- | Untyped witness data is a (partially) unstructured value that may be interpreted as a Simplicity value for an appropriately given type.
--
-- Because the Simplicity type of witness data is not explicitly serialized, 'WitnessData' cannot be interpreted until after type inference determines its Simplicity type.
data WitnessData = WitnessValue UntypedValue
                 | WitnessData (UV.Vector Bool)
                 deriving Show

-- | Interpret 'WitnessData' at a the given Simplicity type.
-- This may fail if the data isn't interpretable at the given Simplicity type.
getWitnessData :: TyC a => WitnessData -> Maybe a
getWitnessData (WitnessValue v) = castUntypedValue v
getWitnessData (WitnessData v) = evalExactVector getValue v

-- | An open recursive type for untyped Simplicity terms with type annotations.
-- The 'ty' parameter holds the typing annotations, which can be, for example, 'Ty', or @()@ for untyped Simplicity terms without annotations.
-- The 'a' parameter holds the (open) recursive subexpressions.
data TermF ty a = Iden ty
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

instance (Show ty, Show a) => Show (TermF ty a) where
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
  showsPrec p (Prim (SomeArrow prim)) = showParen (10 < p)
                                      $ showString "Prim "
                                      . (showParen True $ showString "someArrow " . showString (primName prim))

-- Given a @'UTy' v@ annonated Simplicity 'TermF', return the implied input and output types given the annotations.
termFArrow :: TermF (UTy v) a -> (UTy v, UTy v)
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
termFArrow (Prim (SomeArrow p)) = (unfreeze (unreflect ra), unfreeze (unreflect rb))
 where
  (ra, rb) = reifyArrow p

-- 'FocusTy a ty' is isomorphic to 'TermF ty a'.  Its purpose is to provide functor instances to 'TermF's ty parameter.
newtype FocusTy a ty = FocusTy { unFocusTy :: TermF ty a }

instance Functor (FocusTy a)  where
  fmap = fmapDefault

instance Foldable (FocusTy a) where
  foldMap = foldMapDefault

instance Traversable (FocusTy a)  where
  traverse f (FocusTy (Iden a)) = FocusTy . Iden <$> f a
  traverse f (FocusTy (Unit a)) = FocusTy . Unit <$> f a
  traverse f (FocusTy (Injl a b c x)) = fmap FocusTy $ Injl <$> f a <*> f b <*> f c <*> pure x
  traverse f (FocusTy (Injr a b c x)) = fmap FocusTy $ Injr <$> f a <*> f b <*> f c <*> pure x
  traverse f (FocusTy (Take a b c x)) = fmap FocusTy $ Take <$> f a <*> f b <*> f c <*> pure x
  traverse f (FocusTy (Drop a b c x)) = fmap FocusTy $ Drop <$> f a <*> f b <*> f c <*> pure x
  traverse f (FocusTy (Comp a b c x y)) = fmap FocusTy $ Comp <$> f a <*> f b <*> f c <*> pure x <*> pure y
  traverse f (FocusTy (Case a b c d x y)) = fmap FocusTy $ Case <$> f a <*> f b <*> f c <*> f d <*> pure x <*> pure y
  traverse f (FocusTy (Pair a b c x y)) = fmap FocusTy $ Pair <$> f a <*> f b <*> f c <*> pure x <*> pure y
  traverse f (FocusTy (Disconnect a b c d x y)) = fmap FocusTy $ Disconnect <$> f a <*> f b <*> f c <*> f d <*> pure x <*> pure y
  traverse f (FocusTy (Hidden a b x)) = fmap FocusTy $ Hidden <$> f a <*> f b <*> pure x
  traverse f (FocusTy (Witness a b x)) = fmap FocusTy $ Witness <$> f a <*> f b <*> pure x
  traverse f (FocusTy (Prim p)) = pure (FocusTy (Prim p))

-- InferenceError holds the possible errors that can occur during the 'inference' step.
data InferenceError s = UnificationFailure (UFailure TyF (STVar s TyF))
                      | IndexError Int Integer
                      | Overflow
                      deriving Show

instance Fallible TyF (STVar s TyF) (InferenceError s) where
  occursFailure v t = UnificationFailure (occursFailure v t)
  mismatchFailure t1 t2 = UnificationFailure (mismatchFailure t1 t2)

-- | A type synonym for Simplicity terms without type annotations.
type UntypedTermF a = TermF () a

-- Constructors for untyped 'TermF'.
uIden :: UntypedTermF a
uIden = Iden ()

uUnit :: UntypedTermF a
uUnit = Unit ()

uInjl :: a -> UntypedTermF a
uInjl = Injl () () ()

uInjr :: a -> UntypedTermF a
uInjr = Injr () () ()

uTake :: a -> UntypedTermF a
uTake = Take () () ()

uDrop :: a -> UntypedTermF a
uDrop = Drop () () ()

uComp :: a -> a -> UntypedTermF a
uComp = Comp () () ()

uCase :: a -> a -> UntypedTermF a
uCase = Case () () () ()

uPair :: a -> a -> UntypedTermF a
uPair = Pair () () ()

uDisconnect :: a -> a -> UntypedTermF a
uDisconnect = Disconnect () () () ()

uHidden :: Hash256 -> UntypedTermF a
uHidden = Hidden () ()

uWitness :: WitnessData -> UntypedTermF a
uWitness = Witness () ()

-- | :TODO: NOT YET IMPLEMENTED
uJet = error "uJet: :TODO: NOT YET IMPLEMENTED"

-- | :TODO: NOT YET IMPLEMENTED
uFail :: Block512 -> UntypedTermF a
uFail = error "uFail: :TODO: NOT YET IMPLEMENTED"

-- | Simplicity terms with explicit sharing of subexpressions to form a topologically sorted DAG (directed acyclic graph).
--
-- Every node in an Simplicity expression is an element of a finitary container with indices that reference the relative locations of their child subexpressions within that container.
-- This reference is the difference in positions between refering node's position and the referred node's position.
-- The number @1@ is a reference to the immediately preciding node. The number @0@ is not allowed as it would imply a node is refering to itself.
--
-- The last element of the vector is the root of the Simplicity expression DAG.
--
-- Invariant:
--
-- @
--     0 \<= /i/ && /i/ \< 'Foldable.length' /v/ ==> 'Foldable.all' (\\x -> 0 < x && x <= /i/) ('Foldable.toList' /v/ '!!' /i/)
-- @
type SimplicityDag f ty = f (TermF ty Integer)

-- 'inference' takes an 'SimplicityDag' and adds suitiable type annotations to the nodes in the DAG as well as unification constraints.
-- This can cause unification failures, however the occurs check isn't performed in this step.
-- This function also checks that the provided DAG is sorted in topological order.
inference :: Foldable f => SimplicityDag f x ->
             ExceptT (InferenceError s) (STBinding s) (Seq (TermF (UTy (STVar s TyF)) Int))
inference = foldM loop empty
 where
  tyWord256 = unreflect (reify :: TyReflect Word256)
  loop :: Seq (TermF (UTy (STVar s TyF)) Int)
       -> TermF x Integer
       -> ExceptT (InferenceError s) (STBinding s) (Seq (TermF (UTy (STVar s TyF)) Int))
  loop output node = (output |>) <$> go node
   where
    fresh :: ExceptT (InferenceError s) (STBinding s) (UTy (STVar s TyF))
    fresh = UVar <$> lift freeVar
    lenOutput = length output
    lookup i | i <= toInteger (maxBound :: Int) = maybe (throwE (IndexError lenOutput i)) return (output !? (lenOutput - fromInteger i))
             | otherwise = throwE Overflow
    go (Iden _) = Iden <$> fresh
    go (Unit _) = Unit <$> fresh
    go (Injl _ _ _ it) = do
      (a,b) <- termFArrow <$> lookup it
      c <- fresh
      return (Injl a b c (fromInteger it))
    go (Injr _ _ _ it) = do
      (a,c) <- termFArrow <$> lookup it
      b <- fresh
      return (Injr a b c (fromInteger it))
    go (Take _ _ _ it) = do
      (a,c) <- termFArrow <$> lookup it
      b <- fresh
      return (Take a b c (fromInteger it))
    go (Drop _ _ _ it) = do
      (b,c) <- termFArrow <$> lookup it
      a <- fresh
      return (Drop a b c (fromInteger it))
    go (Comp _ _ _ is it) = do
      (a,b0) <- termFArrow <$> lookup is
      (b1,c) <- termFArrow <$> lookup it
      b <- b0 =:= b1
      return (Comp a b c (fromInteger is) (fromInteger it))
    go (Case _ _ _ _ is it) = do
      (ac,d0) <- termFArrow <$> lookup is
      (bc,d1) <- termFArrow <$> lookup it
      a <- fresh
      b <- fresh
      c <- fresh
      _ <- UTerm (Prod a c) =:= ac
      _ <- UTerm (Prod b c) =:= bc
      d <- d0 =:= d1
      return (Case a b c d (fromInteger is) (fromInteger it))
    go (Pair _ _ _ is it) = do
      (a0,b) <- termFArrow <$> lookup is
      (a1,c) <- termFArrow <$> lookup it
      a <- a0 =:= a1
      return (Pair a b c (fromInteger is) (fromInteger it))
    go (Disconnect _ _ _ _ is it) = do
      (aw,bc) <- termFArrow <$> lookup is
      (c,d) <- termFArrow <$> lookup it
      a <- fresh
      b <- fresh
      _ <- UTerm (Prod a (unfreeze tyWord256)) =:= aw
      _ <- UTerm (Prod b c) =:= bc
      return (Disconnect a b c d (fromInteger is) (fromInteger it))
    go (Hidden _ _ h) = Hidden <$> fresh <*> fresh <*> pure h
    go (Witness _ _ w) = Witness <$> fresh <*> fresh <*> pure w
    go (Prim p) = pure (Prim p)

-- Given the output of 'inference', execute unification and return the container of type annotated Simplicity nodes.
-- Any free type variables left over after unification are instantiated at the unit type.
-- Errors, such as unification errors or occurs errors are retuned as 'String's.
runUnification :: Traversable t => (forall s. ExceptT (InferenceError s) (STBinding s) (t (TermF (UTy (STVar s TyF)) i))) -> Either String (t (TermF Ty i))
runUnification mv = runSTBinding $ left show <$> runExceptT (bindV mv)
 where
  bindV :: Traversable t => ExceptT (InferenceError s) (STBinding s) (t (TermF (UTy (STVar s TyF)) i)) -> ExceptT (InferenceError s) (STBinding s) (t (TermF Ty i))
  bindV mv = do
    v <- mv
    bv <- applyBindingsAll (Compose (FocusTy <$> v))
    return . fmap unFocusTy . getCompose $ unital <$> bv

-- | Given a 'SimplicityDag', throw away the existing type annotations, if any, and run type inference to compute a new set of type annotations.
-- If type inference fails, such as a unification error or an occurs error, return an error message.
typeInference :: Foldable f => SimplicityDag f x -> Either String (SimplicityDag Seq Ty)
typeInference v = fmap (fmap toInteger) <$> runUnification (inference v)

-- | Transform a 'SimplicityDag' into a well-typed Simplicity expression of a specified type.
-- If type inference fails, such as a unification error or an occurs error, return an error message.
--
-- Note: The one calling 'typeCheck' determines the input and output Simplicity types of the resulting Simplicity expression.
-- They are __not__ inferered from the DAG input.
-- Instead the types @a@ and @b@ are used as constraints during type inference.
typeCheck :: forall f x term a b. (Foldable f, Simplicity term, TyC a, TyC b) => SimplicityDag f x -> Either String (term a b)
typeCheck v = typeCheckTerm =<< runUnification inferenced
 where
   a0 :: TyReflect a
   a0 = reify
   b0 :: TyReflect b
   b0 = reify
   inferenced :: forall s. ExceptT (InferenceError s) (STBinding s) (Seq (TermF (UTy (STVar s TyF)) Int))
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
   typeCheckTerm s = case viewr typeCheckedDag of
     _ :> Right (SomeArrow t) -> maybe (error "Simplicity.Inference.typeCheck: unexpect mismatched type at end.") return $ do
                                  let (ra, rb) = reifyArrow t
                                  Refl <- equalTyReflect ra a0
                                  Refl <- equalTyReflect rb b0
                                  return t
     _ :> Left s -> Left s
     EmptyR -> Left "Simplicity.Inference.typeCheck: empty vector input."
    where
     assertEqualTyReflect a b = maybe err Right (equalTyReflect a b)
      where
       err = Left "Simplicity.Inference.typeCheck: unexpected mismatched type"
     typeCheckedDag = mapWithIndex (\i -> left (++ " at index " ++ show i ++ ".") . typeCheckTermIx i) s
     typeCheckTermIx :: Int -> TermF Ty Int -> Either String (SomeArrow term)
     typeCheckTermIx i = typeCheckTerm
      where
       lookup j = index typeCheckedDag (i - j)
       typeCheckTerm (Iden a) = case reflect a of
                                  SomeTy ra -> return (someArrowR ra ra iden)
       typeCheckTerm (Unit a) = case reflect a of
                                  SomeTy ra -> return (someArrowR ra OneR unit)
       typeCheckTerm (Injl a b c it) = case reflect c of
                                        SomeTy rc -> do
                                          SomeArrow t <- lookup it
                                          let (ra, rb) = reifyArrow t
                                          return (someArrowR ra (SumR rb rc) (injl t))
       typeCheckTerm (Injr a b c it) = case reflect b of
                                        SomeTy rb -> do
                                          SomeArrow t <- lookup it
                                          let (ra, rc) = reifyArrow t
                                          return (someArrowR ra (SumR rb rc) (injr t))
       typeCheckTerm (Take a b c it) = case reflect b of
                                        SomeTy rb -> do
                                          SomeArrow t <- lookup it
                                          let (ra, rc) = reifyArrow t
                                          return (someArrowR (ProdR ra rb) rc (take t))
       typeCheckTerm (Drop a b c it) = case reflect a of
                                        SomeTy ra -> do
                                          SomeArrow t <- lookup it
                                          let (rb, rc) = reifyArrow t
                                          return (someArrowR (ProdR ra rb) rc (drop t))
       typeCheckTerm (Comp a b c is it) = do SomeArrow s <- lookup is
                                             SomeArrow t <- lookup it
                                             let (ra, rb0) = reifyArrow s
                                             let (rb1, rc) = reifyArrow t
                                             Refl <- assertEqualTyReflect rb0 rb1
                                             return (someArrowR ra rc (comp s t))
       typeCheckTerm (Case a b c d is it) | (Hidden _ _ hs) <- index s is = case reflect a of
                                                                              SomeTy ra -> do
                                                                                SomeArrow t <- lookup it
                                                                                ((ProdR rb rc), rd) <- return $ reifyArrow t
                                                                                return (someArrowR (ProdR (SumR ra rb) rc) rd (assertr hs t))
                                          | (Hidden _ _ ht) <- index s is = case reflect b of
                                                                              SomeTy rb -> do
                                                                                SomeArrow s <- lookup is
                                                                                ((ProdR ra rc), rd) <- return $ reifyArrow s
                                                                                return (someArrowR (ProdR (SumR ra rb) rc) rd (assertl s ht))
                                          | otherwise = do SomeArrow s <- lookup is
                                                           SomeArrow t <- lookup it
                                                           ((ProdR ra rc0), rd0) <- return $ reifyArrow s
                                                           ((ProdR rb rc1), rd1) <- return $ reifyArrow t
                                                           Refl <- assertEqualTyReflect rc0 rc1
                                                           Refl <- assertEqualTyReflect rd0 rd1
                                                           return (someArrowR (ProdR (SumR ra rb) rc0) rd0 (match s t))
       typeCheckTerm (Pair a b c is it) = do SomeArrow s <- lookup is
                                             SomeArrow t <- lookup it
                                             let (ra0, rb) = reifyArrow s
                                             let (ra1, rc) = reifyArrow t
                                             Refl <- assertEqualTyReflect ra0 ra1
                                             return (someArrowR ra0 (ProdR rb rc) (pair s t))
       typeCheckTerm (Disconnect a b c d is it) = do SomeArrow s <- lookup is
                                                     SomeArrow t <- lookup it
                                                     ((ProdR ra rw), (ProdR rb rc0)) <- return $ reifyArrow s
                                                     let (rc1, rd) = reifyArrow t
                                                     Refl <- assertEqualTyReflect rw (reify :: TyReflect Word256)
                                                     Refl <- assertEqualTyReflect rc0 rc1
                                                     return (someArrowR ra (ProdR rb rd) (disconnect s t))
       typeCheckTerm (Hidden _ _ _) = Left "Simplicity.Inference.typeCheck: encountered illegal use of Hidden node"
       typeCheckTerm (Witness a b w) = case (reflect a, reflect b) of
                                        (SomeTy ra, SomeTy rb) -> do
                                         vb <- maybe err return $ getWitnessData w
                                         return (someArrowR ra rb (witness vb))
        where
         err = Left "Simplicity.Inference.typeCheck: decode error in Witness value"
       typeCheckTerm (Prim (SomeArrow p)) = return (SomeArrow (primitive p))
