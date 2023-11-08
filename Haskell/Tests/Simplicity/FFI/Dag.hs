{-# LANGUAGE ForeignFunctionInterface #-}
module Simplicity.FFI.Dag
  ( DagNode
  , dagNodeGetCMR
  , withDagNode
  ) where

import qualified Data.ByteString as BS
import Data.Serialize (decode)
import Data.Serialize.Put (runPut)
import Foreign.C.Types (CSize(..), CChar(..))
import Foreign.Ptr (Ptr)
import Foreign.Marshal.Alloc (allocaBytes)
import Foreign.Marshal.Array (allocaArray)
import Foreign.Marshal.Unsafe (unsafeLocalState)
import Foreign.Storable (Storable(..))

import Simplicity.Digest
import Simplicity.FFI.Bitstream

-- Abstract representative for our C structures.
newtype DagNode = DagNode DagNode

foreign import ccall unsafe "&" c_sizeof_dag_node :: Ptr CSize

foreign import ccall unsafe "" c_dag_node_get_cmr :: Ptr CChar -> Ptr DagNode -> IO ()

sizeof_dag_node :: Int
sizeof_dag_node = fromIntegral . unsafeLocalState $ peek c_sizeof_dag_node

withDagNode :: (Ptr DagNode -> IO a) -> IO a
withDagNode = allocaBytes sizeof_dag_node

dagNodeGetCMR :: Ptr DagNode -> IO Hash256
dagNodeGetCMR pnode =
  allocaArray 32 $ \buf -> do
  c_dag_node_get_cmr buf pnode
  Right hash <- decode <$> BS.packCStringLen (buf, 32)
  return hash
