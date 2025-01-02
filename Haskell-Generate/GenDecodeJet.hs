{-# LANGUAGE OverloadedStrings, QuantifiedConstraints, RankNTypes, ScopedTypeVariables #-}
module GenDecodeJet where

import Data.Maybe (catMaybes)
import Prettyprinter ( Doc, (<+>), braces, colon, line, nest, pretty, semi, vsep
                     , SimpleDocStream, LayoutOptions(..), PageWidth(..), defaultLayoutOptions, layoutPretty
                     )
import Prettyprinter.Render.Text (renderIO)
import System.IO (IOMode(WriteMode), withFile)

import NameWrangler
import Simplicity.CoreJets (coreCatalogue)
import Simplicity.Elements.Jets (elementsCatalogue)
import Simplicity.Ty
import Simplicity.Tree

x <-> y = x <> line <> y

nestBraces x = braces (nest 2 (line <> x) <> line)

labelCase ix = "case" <+> pretty ix <> colon

decodeCatalogue :: Catalogue String -> Doc a
decodeCatalogue Missing = mempty
decodeCatalogue (Item name) =
  "*result =" <+> pretty (upperSnakeCase name) <> semi <+>
  "return SIMPLICITY_NO_ERROR" <> semi
decodeCatalogue (Shelf l) = vsep
  [ "code = simplicity_decodeUptoMaxInt(stream)" <> semi
  , "if (code < 0) return (simplicity_err)code" <> semi
  , "switch (code)" <+> nestBraces (vsep cases)
  ]
 where
   cases = catMaybes $ zipWith f [(1::Int)..] l
   f _ Missing = Nothing
   f ix cat@(Item _) = Just . nest 2 $ labelCase ix <+> decodeCatalogue cat
   f ix cat@(Shelf _) = Just . nest 2 $ labelCase ix <-> decodeCatalogue cat <-> "break" <> semi

renderFile name doc = withFile name WriteMode (\h -> renderIO h (layoutPretty layoutOptions (header <-> doc)))
 where
  header = "/* This file has been automatically generated. */\n"

main = do
  renderFile "decodeCoreJets.inc" (wrap (decodeCatalogue (mkName <$> coreCatalogue)))
  renderFile "decodeElementsJets.inc" (wrap (decodeCatalogue (mkName <$> elementsCatalogue)))
 where
  wrap doc = nestBraces ("int32_t code;" <-> doc)

layoutOptions = LayoutOptions { layoutPageWidth = AvailablePerLine 100 1 }
