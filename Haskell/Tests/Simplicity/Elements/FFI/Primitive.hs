{-# LANGUAGE ForeignFunctionInterface #-}
module Simplicity.Elements.FFI.Primitive
  ( decodeJetCMR
  , ErrorCode(..)
  ) where

import Foreign.C.Types (CInt(..))
import Foreign.Ptr (Ptr)
import Foreign.Marshal.Unsafe (unsafeLocalState)

import Simplicity.Digest
import Simplicity.FFI.Bitstream
import Simplicity.FFI.Dag

data ErrorCode = BitstreamEof | DataOutOfRange deriving (Eq, Show)

decodeError :: CInt -> Either ErrorCode ()
decodeError 0 = Right ()
decodeError (-2) = Left BitstreamEof
decodeError (-4) = Left DataOutOfRange
decodeError err = error $ "Simplicity.Elements.FFI.Primitive.decodeError: Unexpected error code " ++ show err

foreign import ccall unsafe "" simplicity_decodeJet :: Ptr DagNode -> Ptr Bitstream -> IO CInt

decodeJetNode :: Ptr Bitstream -> (Either ErrorCode (Ptr DagNode) -> IO a) -> IO a
decodeJetNode pstream k =
  withDagNode $ \pnode -> do
  error <- simplicity_decodeJet pnode pstream
  k (decodeError error >> return pnode)

decodeJetCMR :: [Bool] -> Either ErrorCode Hash256
decodeJetCMR codeWord = unsafeLocalState $
  initializeBitstream codeWord $ \pstream ->
  decodeJetNode pstream $ \result ->
  case result of
    Left err -> return $ Left err
    Right pnode -> Right <$> dagNodeGetCMR pnode
