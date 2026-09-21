#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

echo "==> Running GenPrimitive (elements)..."
cabal run GenPrimitive
mv -v primitiveEnumTy.inc  C/elements/
mv -v primitiveInitTy.inc  C/elements/
mv -v primitiveEnumJet.inc C/elements/
mv -v primitiveJetNode.inc C/elements/

echo "==> Running GenDecodeJet..."
cabal run GenDecodeJet
mv -v decodeCoreJets.inc    C/
mv -v decodeElementsJets.inc C/elements/
mv -v decodeBitcoinJets.inc  C/bitcoin/

echo "==> Touching C sources to force recompilation..."
grep -rl "decodeElementsJets\|primitiveEnumJet\|primitiveJetNode" C/ --include="*.c" | xargs touch

echo "Done."
