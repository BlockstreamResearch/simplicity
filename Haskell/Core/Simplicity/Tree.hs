-- | This modules provides custom binary trees ('BinTree') and rose trees ('Catalogue') for use in Simplicity.
module Simplicity.Tree
  ( BinTree(..), branch, traverseWithPath, foldMapWithPath
  , Catalogue(..), book
  ) where

import Data.Functor.Const (Const(Const), getConst)
import Data.Traversable (fmapDefault, foldMapDefault)
import Data.Void (Void, vacuous)

-- | A rose tree type.  This type includes 'Missing' leaves that contain no value.
data Catalogue a = Missing | Item a | Shelf [Catalogue a]

instance Functor Catalogue where
  fmap = fmapDefault

instance Foldable Catalogue where
  foldMap = foldMapDefault

instance Traversable Catalogue where
  traverse f Missing = pure Missing
  traverse f (Item a) = Item <$> f a
  traverse f (Shelf l) = Shelf <$> traverse (traverse f) l

instance Applicative Catalogue where
  pure = Item
  bf <*> bx = bf >>= \f -> bx >>= \x -> return (f x)

instance Monad Catalogue where
  return = pure
  Missing >>= f = Missing
  (Item a) >>= f = f a
  (Shelf l) >>= f = Shelf $ map (>>= f) l

-- | Builds a depth 1 'Catalog' from a list.
book :: [a] -> Catalogue a
book = Shelf . fmap Item

-- | A binary tree type.  This type includes 'Dead' leaves that contain no value.
data BinTree a = Dead | Leaf a | Branch (BinTree a) (BinTree a)

instance Functor BinTree where
  fmap = fmapDefault

instance Foldable BinTree where
  foldMap = foldMapDefault

instance Traversable BinTree where
  traverse f Dead = pure Dead
  traverse f (Leaf a) = Leaf <$> f a
  traverse f (Branch l r) = Branch <$> traverse f l <*> traverse f r

instance Applicative BinTree where
  pure = Leaf
  bf <*> bx = bf >>= \f -> bx >>= \x -> return (f x)

instance Monad BinTree where
  return = pure
  Dead >>= f = Dead
  (Leaf a) >>= f = f a
  (Branch l r) >>= f = Branch (l >>= f) (r >>= f)

-- | An optimized 'Branch' that collapses 'Dead' leaves into one.
branch :: BinTree a -> BinTree a -> BinTree a
branch Dead Dead = Dead
branch l r = Branch l r

-- | Similar to 'traverse' but additionally provides the operation with the path from the root to the 'Leaf'.
traverseWithPath :: Applicative f => ([Bool] -> a -> f b) -> BinTree a -> f (BinTree b)
traverseWithPath f = go id
 where
  go ctx (Branch l r) = Branch <$> go (ctx . (False:)) l <*> go (ctx . (True:)) r
  go ctx (Leaf a) = Leaf <$> f (ctx []) a
  go ctx Dead = pure Dead

-- | Similar to 'foldMap' but additionally provides the operation with the path from the root to the 'Leaf'.
foldMapWithPath :: Monoid m => ([Bool] -> a -> m) -> BinTree a -> m
foldMapWithPath f = getConst . traverseWithPath (\p -> Const . f p)
