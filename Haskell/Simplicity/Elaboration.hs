{-# LANGUAGE DeriveTraversable, FlexibleInstances, GADTs, MultiParamTypeClasses, ScopedTypeVariables #-}
-- | This module defines a type for untyped Simplicity DAGs as well as a type checking function to convert such a DAG into a well-typed Simplicity expression.
module Simplicity.Elaboration
  (
  -- * Untyped Simplicity
    UntypedTermF
  , UntypedSimplicityDag
  , WitnessData
  -- ** Constructors for untyped Simplicity
  , uIden, uUnit, uInjl, uInjr
  , uTake, uDrop, uComp, uCase, uPair, uDisconnect
  , uHidden, uWitness, uPrim
  -- * Type checking untyped Simplicity
  , typeCheckDag
  ) where

import Prelude hiding (fail, take, drop)

import Control.Arrow ((+++), left)
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
import Data.Vector (Vector, unfoldrM, foldM)
import qualified Data.Vector.Unboxed as UV

import Simplicity.Digest
import Simplicity.Primitive
import Simplicity.MerkleRoot
import Simplicity.Serialization
import Simplicity.Term
import Simplicity.Ty
import Simplicity.Ty.Word

-- SomeTy is isomorphic to Ty.
data SomeTy = forall a. TyC a => SomeTy (TyReflect a)

-- Convert a Ty to SomeTy.
reflect :: Ty -> SomeTy
reflect (Fix One) = SomeTy OneR
reflect (Fix (Sum a b)) = case (reflect a, reflect b) of
                            (SomeTy ra, SomeTy rb) -> SomeTy $ SumR ra rb
reflect (Fix (Prod a b)) = case (reflect a, reflect b) of
                             (SomeTy ra, SomeTy rb) -> SomeTy $ ProdR ra rb

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
{-
             | Jet JetID
-}
  deriving (Functor, Foldable, Traversable)

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

-- ElaborateError holds the possible errors that can occur during the 'elaborate' step.
data ElaborateError s = UnificationFailure (UFailure TyF (STVar s TyF))
                      | IndexError Int Int
                      | Overflow
                      deriving Show

instance Fallible TyF (STVar s TyF) (ElaborateError s) where
  occursFailure v t = UnificationFailure (occursFailure v t)
  mismatchFailure t1 t2 = UnificationFailure (mismatchFailure t1 t2)

-- | Untyped Simplicity expressions with explicit sharing of subexpressions.
--
-- Every node in an Simplicity expression is an element of a vector with indices that reference the relative locations of their immediate subexpressions within that vector.
-- This reference is indicated by a number that counts backwards from the refering node's position in the vector to the position in the vector wher ethe referred node is found.
-- The number @0@ is a reference to the immediately preciding node (as a node is not allowed to refer to itself).
--
-- The last element of the vector is the root of the Simplicity expression DAG.
-- To be a valid DAG, we require that the subexpression references all come before the node itself
-- (i.e. the Vector must be topologically sorted).
type UntypedSimplicityDag = Vector (UntypedTermF Integer)

-- 'elaborate' takes an 'UntypedSimplicityDag' and adds suitiable type annotations to the nodes in the DAG as well as unification constraints.
-- This can cause unification failures, however the occurs check isn't performed in this step.
-- This function also checks that the provided DAG is sorted in topological order.
elaborate :: UntypedSimplicityDag ->
             ExceptT (ElaborateError s) (STBinding s) (Seq (TermF Int (UTy (STVar s TyF))))
elaborate = foldM loop empty
 where
  tyWord256 = unreflect (reify :: TyReflect Word256)
  loop :: Seq (TermF Int (UTy (STVar s TyF)))
       -> UntypedTermF Integer
       -> ExceptT (ElaborateError s) (STBinding s) (Seq (TermF Int (UTy (STVar s TyF))))
  loop output node = (output |>) <$> go node
   where
    lenOutput = length output
    fresh :: ExceptT (ElaborateError s) (STBinding s) (UTy (STVar s TyF))
    fresh = UVar <$> lift freeVar
    lookup i | i <= toInteger (maxBound :: Int) = maybe (throwE (IndexError lenOutput i')) return (output !? (lenOutput - i'))
             | otherwise = throwE Overflow
     where
      i' = fromInteger i
    go (Untyped (Iden _)) = Iden <$> fresh
    go (Untyped (Unit _)) = Unit <$> fresh
    go (Untyped (Injl _ _ _ it)) = do
      (a,b) <- termFArrow <$> lookup it
      c <- fresh
      return (Injl a b c (fromInteger it))
    go (Untyped (Injr _ _ _ it)) = do
      (a,c) <- termFArrow <$> lookup it
      b <- fresh
      return (Injr a b c (fromInteger it))
    go (Untyped (Take _ _ _ it)) = do
      (a,c) <- termFArrow <$> lookup it
      b <- fresh
      return (Take a b c (fromInteger it))
    go (Untyped (Drop _ _ _ it)) = do
      (b,c) <- termFArrow <$> lookup it
      a <- fresh
      return (Drop a b c (fromInteger it))
    go (Untyped (Comp _ _ _ is it)) = do
      (a,b0) <- termFArrow <$> lookup is
      (b1,c) <- termFArrow <$> lookup it
      b <- b0 =:= b1
      return (Comp a b c (fromInteger is) (fromInteger it))
    go (Untyped (Case _ _ _ _ is it)) = do
      (ac,d0) <- termFArrow <$> lookup is
      (bc,d1) <- termFArrow <$> lookup it
      a <- fresh
      b <- fresh
      c <- fresh
      _ <- UTerm (Prod a c) =:= ac
      _ <- UTerm (Prod b c) =:= bc
      d <- d0 =:= d1
      return (Case a b c d (fromInteger is) (fromInteger it))
    go (Untyped (Pair _ _ _ is it)) = do
      (a0,b) <- termFArrow <$> lookup is
      (a1,c) <- termFArrow <$> lookup it
      a <- a0 =:= a1
      return (Pair a b c (fromInteger is) (fromInteger it))
    go (Untyped (Disconnect _ _ _ _ is it)) = do
      (aw,bc) <- termFArrow <$> lookup is
      (c,d) <- termFArrow <$> lookup it
      a <- fresh
      b <- fresh
      _ <- UTerm (Prod a (unfreeze tyWord256)) =:= aw
      _ <- UTerm (Prod b c) =:= bc
      return (Disconnect a b c d (fromInteger is) (fromInteger it))
    go (Untyped (Hidden _ _ h)) = Hidden <$> fresh <*> fresh <*> pure h
    go (Untyped (Witness _ _ w)) = Witness <$> fresh <*> fresh <*> pure w
    go (Untyped (Prim p)) = pure (Prim p)

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
   elaborated :: forall s. ExceptT (ElaborateError s) (STBinding s) (Seq (TermF Int (UTy (STVar s TyF))))
   elaborated = do
     ev <- elaborate v
     _ <- case viewr ev of
         EmptyR -> return ()
         _ :> end -> do
           let (a1, b1) = termFArrow end
           _ <- a1 =:= unfreeze (unreflect a0)
           _ <- b1 =:= unfreeze (unreflect b0)
           return ()
     return ev
   annotated :: Either String (Seq (TermF Int Ty))
   annotated = runSTBinding ((show +++ (getCompose . fmap unital)) <$> runExceptT ((Compose <$> elaborated) >>= applyBindingsAll))
   typeCheckTerm s = case viewr typeCheckedDag of
     _ :> Right (SomeArrow t ra rb) -> maybe (error "Simplicity.Elaboration.typeCheckDag: unexpect mismatched type at end.") return $ do
                                         Refl <- equalTyReflect ra a0
                                         Refl <- equalTyReflect rb b0
                                         return t
     _ :> Left s -> Left s
     EmptyR -> Left "Simplicity.Elaboration.typeCheckDag: empty vector input."
    where
     assertEqualTyReflect a b = maybe err Right (equalTyReflect a b)
      where
       err = Left "Simplicity.Elaboration.typeCheckDag: unexpected mismatched type"
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
     typeCheck (Hidden _ _ _) = Left "Simplicity.Elaboration.typeCheckDag: encountered illegal use of Hidden node"
     typeCheck (Witness a b w) = case (reflect a, reflect b) of
                                   (SomeTy ra, SomeTy rb) -> do
                                      vb <- maybe err return $ evalExactVector (getValueR rb) w
                                      return (SomeArrow (witness vb) ra rb)
      where
       err = Left "Simplicity.Elaboration.typeCheckDag: decode error in Witness value"
     typeCheck (Prim (SomeArrow p ra rb)) = return (SomeArrow (primitive p) ra rb)
