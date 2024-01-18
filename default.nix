{ nixpkgs ? import <nixpkgs> {}
, ghc ? "ghc94"
, coqPackages ? "coqPackages_8_16"
, production ? false
, secp256k1git ? null
, wideMultiply ? null
, withCoverage ? false
, withProfiler ? false
, withTiming ? true
, doCheck ? true
, env ? "stdenv"
}:
let hp = nixpkgs.haskell.packages.${ghc};
    cp = nixpkgs.${coqPackages};
 in rec
{
  haskell = haskellPackages.callPackage ./Simplicity.Haskell.nix {};

  haskellPackages = hp.override {
    overrides = self: super: {
      Simplicity = haskell;

      # Temporary work around for compiling hlint and hasktags in ghc94.
      microlens = self.microlens_0_4_13_1 or super.microlens;
      microlens-ghc = self.microlens-ghc_0_4_14_1 or super.microlens-ghc;
      microlens-platform = self.microlens-platform_0_4_3_3 or super.microlens-platform;
      hlint = self.hlint_3_5 or super.hlint;
    };
  };

  coq = nixpkgs.callPackage ./Simplicity.Coq.nix {
    inherit (cp) coq;
    inherit vst;
  };

  c = nixpkgs.callPackage ./Simplicity.C.nix {
    inherit doCheck production wideMultiply withCoverage withProfiler withTiming;
    stdenv = nixpkgs.${env};
  };

  compcert = nixpkgs.callPackage ./compcert-opensource.nix {
    inherit (cp) coq flocq;
    inherit (cp.coq.ocamlPackages) ocaml menhir menhirLib findlib;
    ccomp-platform = "x86_64-linux";
  };

  pdf = nixpkgs.runCommand "Simplicity-TR" {} ''
    export TEXMACS_HOME_PATH=$NIX_BUILD_TOP
    mkdir -p $out/share/

    cp ${./Simplicity-TR.tm} Simplicity-TR.tm
    cp ${./Simplicity.bib} Simplicity.bib

    mkdir -p $TEXMACS_HOME_PATH/progs
    cat <<EOF > $TEXMACS_HOME_PATH/progs/my-init-buffer.scm
    ; inspired by http://savannah.gnu.org/bugs/?32944
    (generate-all-aux) (print-to-file "Simplicity-TR.pdf") (style-clear-cache)
    EOF

    ${nixpkgs.xvfb-run}/bin/xvfb-run ${nixpkgs.texmacs}/bin/texmacs -c Simplicity-TR.tm $out/share/Simplicity-TR.pdf -q
  '';

  vst = nixpkgs.callPackage ./vst.nix {
    inherit (cp) coq;
    inherit compcert;
  };

  # $ nix-build -A inheritance -o inheritance.Coq.eps
  inheritance = nixpkgs.runCommand "inheritance.Coq.eps" { buildInputs = [ nixpkgs.graphviz ]; } "dot ${./inheritance.Coq.dot} -Teps -o $out";
}
