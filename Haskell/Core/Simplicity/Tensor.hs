-- | This module provides a product for computing multiple interpretations of Simplicity simutaneously.
-- Other tensors can be added when they are needed.
module Simplicity.Tensor
  ( Product(..)
  ) where

data Product p q a b = Product { fstProduct :: p a b
                               , sndProduct :: q a b
                               }
                       deriving Show
