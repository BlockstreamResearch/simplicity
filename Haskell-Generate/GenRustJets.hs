{-# LANGUAGE OverloadedStrings #-}
module GenRustJets where

import Data.Char (toLower)
import Data.Foldable (toList)
import Data.Function (on)
import Data.Functor.Fixedpoint (Fix(..))
import Data.List (sortBy)
import Data.List.Split (chunksOf)
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import Numeric (showHex)
import Prettyprinter ( Doc, (<+>), braces, comma, dquotes, fillSep, line, nest, parens, pretty, punctuate, semi, tupled, vsep
                     , SimpleDocStream, LayoutOptions(..), PageWidth(..), defaultLayoutOptions, layoutPretty
                     )
import Prettyprinter.Render.Text (renderIO)
import System.IO (IOMode(WriteMode), withFile)

import NameWrangler
import qualified Simplicity.Bitcoin.Jets as Bitcoin
import qualified Simplicity.Bitcoin.Term as Bitcoin
import qualified Simplicity.CoreJets as Core
import Simplicity.CoreJets (CoreJet)
import Simplicity.Digest
import qualified Simplicity.Elements.Jets as Elements
import qualified Simplicity.Elements.Term as Elements
import Simplicity.MerkleRoot
import Simplicity.Serialization
import Simplicity.Tree
import Simplicity.Ty
import Simplicity.Weight

x <-> y = x <> line <> y

nestBraces x = braces (nest 4 (line <> x) <> line)

data JetModule = CoreModule | BitcoinModule | ElementsModule
  deriving Eq

data JetData x y = JetData { jetName :: String
                           , jetCMR :: CommitmentRoot x y
                           , jetModule :: JetModule
                           , jetCost :: Weight
                           }

sortJetName = sortBy (compare `on` name)
 where
  name (SomeArrow j) = jetName j

cJetName = lowerSnakeCase . jetName

coreJetData :: (TyC x, TyC y) => CoreJet x y -> JetData x y
coreJetData jet = JetData { jetName = mkName jet
                          , jetCMR = cmr
                          , jetModule = CoreModule
                          , jetCost = Core.jetCost jet
                          }
  where
    cmr | result == Elements.asJet (Elements.CoreJet jet) = result
      where
       result = Bitcoin.asJet (Bitcoin.CoreJet jet)

elementsJetData :: (TyC x, TyC y) => Elements.JetType x y -> JetData x y
elementsJetData jet = JetData { jetName = mkName jet
                              , jetCMR = Elements.asJet jet
                              , jetModule = jetModule
                              , jetCost = Elements.jetCost jet
                              }
 where
  jetModule | Elements.CoreJet _ <- jet = CoreModule
            | otherwise = ElementsModule

bitcoinJetData :: (TyC x, TyC y) => Bitcoin.JetType x y -> JetData x y
bitcoinJetData jet = JetData { jetName = mkName jet
                             , jetCMR = Bitcoin.asJet jet
                             , jetModule = jetModule
                             , jetCost = Bitcoin.jetCost jet
                             }
 where
  jetModule | Bitcoin.CoreJet _ <- jet = CoreModule
            | otherwise = BitcoinModule

data Module = Module { moduleName :: Maybe String
                     , moduleCodes :: BinTree (SomeArrow JetData)
                     }
moduleJets :: Module -> [SomeArrow JetData]
moduleJets = sortJetName . toList . moduleCodes

rustModuleName = fromMaybe "Core" . moduleName
lowerRustModuleName = map toLower . rustModuleName

coreModule :: Module
coreModule = Module Nothing (someArrowMap coreJetData <$> (treeEvalBitStream Core.getJetBit))

-- Take Right is used to drop the (infinite) branch of constant word jets.
takeRight (Branch _ r) = r

elementsModule :: Module
elementsModule = Module (Just "Elements") (someArrowMap elementsJetData <$> takeRight (treeEvalBitStream Elements.getJetBit))

bitcoinModule :: Module
bitcoinModule = Module (Just "Bitcoin") (someArrowMap bitcoinJetData <$> takeRight (treeEvalBitStream Bitcoin.getJetBit))

data CompactTy = CTyOne
               | CTyWord Int
               | CTyMaybe CompactTy
               | CTySum CompactTy CompactTy
               | CTyProd CompactTy CompactTy
     deriving (Eq, Ord)

compactTy :: Ty -> CompactTy
compactTy = memoCataTy go
 where
  go One = CTyOne
  go (Sum CTyOne CTyOne) = CTyWord 1
  go (Sum CTyOne y) = CTyMaybe y
  go (Sum x y) = CTySum x y
  go (Prod (CTyWord wx) (CTyWord wy)) | wx == wy = CTyWord (wx + wy)
  go (Prod x y) = CTyProd x y

compactRustName :: CompactTy -> ShowS
compactRustName s = showString "b\"" . go s . showString "\""
 where
  go CTyOne = showString "1"
  go (CTyWord 1) = showString "2"
  go (CTyWord 32) = showString "i"
  go (CTyWord 64) = showString "l"
  go (CTyWord 256) = showString "h"
  go (CTyWord n) | even n = let rec = go (CTyWord (n `div` 2)) in showString "*" . rec . rec
  go (CTyMaybe x) = showString "+1" . go x
  go (CTySum x y) = showString "+" . go x . go y
  go (CTyProd x y) = showString "*" . go x . go y

showRustHash :: Hash256 -> Doc a
showRustHash h = fillSep $ ((<> comma) . format <$> chunksOf 2 str_h)
 where
  format x = pretty $ "0x" ++ x
  str_h = padding ++ text
   where
    padding = replicate (64 - length text) '0'
    text = showHex (integerHash256 h) ""

rustJetCmr :: Module -> Doc a
rustJetCmr mod = vsep $
  [ nest 4 (vsep ("fn cmr(&self) -> Cmr {" :
-- Temporarily if statment until Bitcoin Jets have weight costs assigned to them
-- See Haskell/Simplicity/Bitcoin/Jets.hs:  jetCost (BitcoinJet jt) = error "Simplicity.Bitcoin.Jets.jetCost: :TODO: Implement jets for Bitcoin and benchmark them."
   if Just "Bitcoin" == moduleName mod
   then ["unimplemented!(\"Bitcoin jet CMRs weights have not yet been implemented.\")"]
   else
    [ nest 4 (vsep ("let bytes = match self {" :
        map (<>comma)
        [ nest 4 (vsep
          [ pretty modname <> "::" <> pretty (jetName jet) <+> "=> ["
          , showRustHash (commitmentRoot (jetCMR jet))
          ]) <-> "]"
        | (SomeArrow jet) <- moduleJets mod
        ]))
    , "};"
    , mempty
    , "Cmr(Midstate(bytes))"
    ]))
  , "}"
  ]
 where
  modname = rustModuleName mod

rustJetTy fname getTy mod = vsep $
  [ nest 4 (vsep (pretty ("fn "++fname++"(&self) -> TypeName {") :
    [ nest 4 (vsep ("let name: &'static [u8] = match self {" :
        map (<>comma)
        [ pretty modname <> "::" <> pretty (jetName jet) <+> "=>" <+>
          pretty (compactRustName (compactTy (getTy j)) "")
        | j@(SomeArrow jet) <- moduleJets mod
        ]))
    , "};"
    , mempty
    , "TypeName(name)"
    ]))
  , "}"
  ]
 where
  modname = rustModuleName mod

rustJetSourceTy :: Module -> Doc a
rustJetSourceTy = rustJetTy "source_ty" (\(SomeArrow jet) -> unreflect (fst (reifyArrow jet)))

rustJetTargetTy :: Module -> Doc a
rustJetTargetTy = rustJetTy "target_ty" (\(SomeArrow jet) -> unreflect (snd (reifyArrow jet)))

rustJetPtr :: Module -> Doc a
rustJetPtr mod = vsep $
  [ nest 4 (vsep ("fn c_jet_ptr(&self) -> &dyn Fn(&mut CFrameItem, CFrameItem, &Self::CJetEnvironment) -> bool {" :
    if modname == "Bitcoin"
    then ["unimplemented!(\"Bitcoin jets have not yet been implemented.\")"]
    else [ nest 4 (vsep ("match self {" :
        map (<>comma)
        [ pretty modname <> "::" <> pretty (jetName jet) <+> "=>" <+>
          pretty ("&simplicity_sys::c_jets::jets_wrapper::"++cJetName jet)
        | SomeArrow jet <- moduleJets mod
        ]))
    , "}"
    ]))
  , "}"
  ]
 where
  modname = rustModuleName mod

rustJetEncode :: Module -> Doc a
rustJetEncode mod =
  "fn encode<W: Write>(&self, w: &mut BitWriter<W>) -> std::io::Result<usize>" <+>
  nestBraces ("let (n, len) = match self" <+>
    nestBraces (vsep (foldMapWithPath item (moduleCodes mod))) <> semi <-> line <> "w.write_bits_be(n, len)")
 where
  item path (SomeArrow jet) = [pretty (rustModuleName mod ++ "::" ++ jetName jet) <+> "=>"
                          <+> tupled [pretty (code path 0 :: Int), pretty (length path)] <> comma]
  code [] n = n
  code (b : l) n = code l (2*n + if b then 1 else 0)

rustJetDecode :: Module -> Doc a
rustJetDecode mod =
  "fn decode<I: Iterator<Item = u8>>(bits: &mut BitIter<I>) -> Result<Self, decode::Error>" <+>
  nestBraces ("decode_bits!(bits," <+> braces (docTree (moduleCodes mod)) <> ")")
 where
  docTree Dead = mempty
  docTree (Leaf (SomeArrow jet)) = pretty (rustModuleName mod ++ "::" ++ jetName jet)
  docTree (Branch l r) = nest 4
                       ( line <> ("0" <+> "=>" <+> braces (docTree l)) <> comma
                     <-> ("1" <+> "=>" <+> braces (docTree r))
                       ) <> line

rustJetCost :: Module -> Doc a
rustJetCost mod = vsep $
  [ nest 4 (vsep ("fn cost(&self) -> Cost {" :
    if modname == "Bitcoin"
    then ["unimplemented!(\"Unspecified cost of Bitcoin jets\")"]
    else [ nest 4 (vsep ("match self {" :
        map (<>comma)
        [ pretty modname <> "::" <> pretty (jetName jet) <+> "=>" <+>
          "Cost::from_milliweight(" <> (pretty . milliWeight $ jetCost jet) <> ")"
        | SomeArrow jet <- moduleJets mod
        ]))
    , "}"
    ]))
  , "}"
  ]
 where
  modname = rustModuleName mod

rustJetImpl :: Module -> Doc a
rustJetImpl mod = vsep $
  [ nest 4 (vsep $ punctuate line
    ["impl Jet for" <+> pretty modname <+> "{"
    , env
    , rustJetCmr mod
    , rustJetSourceTy mod
    , rustJetTargetTy mod
    , rustJetEncode mod
    , rustJetDecode mod
    , rustJetPtr mod
    , rustJetCost mod
    ])
  , "}"
  ]
 where
  modname = rustModuleName mod
  env = vsep
    [ pretty $ "type Environment = "++env++";"
    , pretty $ "type CJetEnvironment = "++cEnv++";"
    , ""
    , pretty $ "fn c_jet_env<'env>(&self, "++envArg++": &'env Self::Environment) -> &'env Self::CJetEnvironment {"
    , pretty $ "    "++envBody
    , "}"
    ]
   where
    env | Nothing <- moduleName mod = "()"
        | Just "Elements" == moduleName mod = "ElementsEnv<std::sync::Arc<elements::Transaction>>"
        | Just name <- moduleName mod = name ++ "Env"
    cEnv | Just "Elements" == moduleName mod = "CElementsTxEnv"
         | otherwise = "()"
    envArg | Just "Bitcoin" == moduleName mod = "_env"
           | otherwise = "env"
    envBody | Nothing == moduleName mod = "env"
            | Just "Bitcoin" == moduleName mod = "unimplemented!(\"Unspecified CJetEnvironment for Bitcoin jets\")"
            | otherwise = "env.c_tx_env()"

rustJetEnum :: Module -> Doc a
rustJetEnum mod = vsep
 [ pretty $ "/// " ++ rustModuleName mod ++ " jet family"
 , "#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]"
 , nest 4 (vsep (pretty ("pub enum " ++ rustModuleName mod ++ " {")
   : [pretty (jetName jet) <> comma | (SomeArrow jet) <- moduleJets mod]))
 , "}"
 ]

rustJetDisplay :: Module -> Doc a
rustJetDisplay mod =
  "impl fmt::Display for" <+> pretty modname <+>
    nestBraces ("fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result" <+>
      nestBraces ("match self" <+>
        nestBraces (vsep (
          map (<>comma)
            [ pretty modname <> "::" <> pretty (jetName jet) <+> "=> f.write_str" <> (parens . dquotes . pretty $ cJetName jet)
            | SomeArrow jet <- moduleJets mod
            ]))
      )
    )
 where
  modname = rustModuleName mod

rustJetFromStr :: Module -> Doc a
rustJetFromStr mod =
  "impl str::FromStr for" <+> pretty modname <+>
    nestBraces (vsep
    [ "type Err = crate::Error;"
    , mempty
    , ("fn from_str(s: &str) -> Result<Self, Self::Err>" <+>
        nestBraces ("match s" <+>
          nestBraces (vsep (
            map (<> comma)
              ([ dquotes (pretty (cJetName jet)) <+> "=> Ok" <> parens (pretty modname <> "::" <> pretty (jetName jet))
               | SomeArrow jet <- moduleJets mod
               ] ++ [ "x => Err(crate::Error::InvalidJetName(x.to_owned()))" ]
              )))
      ))
    ])
 where
  modname = rustModuleName mod

rustHeader :: Doc a
rustHeader = "/* This file has been automatically generated. */"

rustImports :: Module -> Doc a
rustImports mod = vsep (map (<> semi)
  ([ "use crate::jet::type_name::TypeName"
  , "use crate::jet::Jet"
  , "use crate::merkle::cmr::Cmr"
  , "use crate::decode_bits"
  , "use crate::{decode, BitIter, BitWriter}"
  , "use crate::analysis::Cost"
  , "use hashes::sha256::Midstate"
  , "use simplicity_sys::CFrameItem"
  , "use std::io::Write"
  , "use std::{fmt, str}"
  ] ++ envImports))
 where
  envImports | Nothing == moduleName mod = []
             | Just "Bitcoin" == moduleName mod = ["use crate::jet::bitcoin::BitcoinEnv"]
             | Just name <- moduleName mod =
             [ pretty $ "use crate::jet::"++map toLower name++"::"++name++"Env"
             , pretty $ "use simplicity_sys::C"++name++"TxEnv"
             ]

rustJetDoc :: Module -> SimpleDocStream a
rustJetDoc mod = layoutPretty layoutOptions $ vsep (map (<> line)
  [ rustHeader
  , rustImports mod
  , rustJetEnum mod
  , rustJetImpl mod
  , rustJetDisplay mod
  , rustJetFromStr mod
  ])

rustFFIImports :: Doc a
rustFFIImports = vsep (map (<> semi)
  [ "use std::ffi::c_void"
  , "use super::c_env::CElementsTxEnv"
  , "use super::frame_ffi::CFrameItem"
  ])

rustFFISigs :: Module -> Doc a
rustFFISigs mod = vsep
  [ nest 4 $ vsep $
    "extern \"C\" {" :
    (declaration <$> moduleJets mod)
  , "}"
  ]
 where
  declaration (SomeArrow jet) = (<> semi) . vsep $ pretty <$>
    [ linkName
    , signature
    ]
   where
    linkName = "#[link_name = \"c_"++cJetName jet++"\"]"
    signature = "pub fn "++cJetName jet++"(dst: *mut CFrameItem, src: *const CFrameItem, env: *const "++envType++") -> bool"
    envType | CoreModule <- jetModule jet = "c_void"
            | ElementsModule <- jetModule jet = "CElementsTxEnv"

rustFFIDoc :: Module -> SimpleDocStream a
rustFFIDoc mod = layoutPretty layoutOptions $ vsep (map (<> line)
  [ rustHeader
  , rustFFIImports
  , rustFFISigs mod
  ])

rustWrapperImports :: Doc a
rustWrapperImports = vsep (map (<> semi)
  [ "use crate::CElementsTxEnv"
  , "use super::{frame_ffi::CFrameItem, elements_ffi}"
  ])

rustWrappers :: Module -> Doc a
rustWrappers mod = vsep ((<> line) . wrapper <$> moduleJets mod)
 where
  wrapper (SomeArrow jet) = vsep
   [ nest 4 $ vsep
     [ pretty $ "pub fn "++cJetName jet++templateParam++"(dst: &mut CFrameItem, src: CFrameItem, "++envParam++") -> bool {"
     , pretty $ "unsafe { "++lowerRustModuleName mod++"_ffi::"++cJetName jet++"(dst, &src, "++envArg++") }"
     ]
   , "}"
   ]
   where
    templateParam | CoreModule <- jetModule jet = "<T>"
                  | otherwise = ""
    envParam | CoreModule <- jetModule jet = "_env: &T"
             | ElementsModule <- jetModule jet = "env: &CElementsTxEnv"
    envArg | CoreModule <- jetModule jet = "std::ptr::null()"
           | ElementsModule <- jetModule jet = "env"

rustWrapperDoc :: Module -> SimpleDocStream a
rustWrapperDoc mod = layoutPretty layoutOptions $ vsep (map (<> line)
  [ rustHeader
  , rustWrapperImports
  , rustWrappers mod
  ])

renderFile name doc = withFile name WriteMode (\h -> renderIO h doc)

main = do
  renderFile "core.rs" (rustJetDoc coreModule)
  renderFile "elements.rs" (rustJetDoc elementsModule)
  renderFile "bitcoin.rs" (rustJetDoc bitcoinModule)
  renderFile "jets_ffi.rs" (rustFFIDoc elementsModule)
  renderFile "jets_wrapper.rs" (rustWrapperDoc elementsModule)

layoutOptions = LayoutOptions { layoutPageWidth = AvailablePerLine 100 1 }
