{ nixpkgs ? import <nixpkgs> {}
, ghc ? "ghc98"
, coqPackages ? "coqPackages_8_17"
, production ? false
, secp256k1git ? null
, wideMultiply ? null
, withAlectryon ? true
, withCoverage ? false
, withProfiler ? false
, withSafegcdCheat ? false
, withTiming ? true
, withValgrind ? false
, doCheck ? true
, env ? "stdenv"
}:
let hp = nixpkgs.haskell.packages.${ghc};
    cp = nixpkgs.${coqPackages};
    pp = nixpkgs.python3Packages;
 in rec
{
  haskell = haskellPackages.callPackage ./Simplicity.Haskell.nix {
    inherit doCheck withValgrind;
  };

  haskellPackages = hp.override {
    overrides = self: super: {
      Simplicity = haskell;

      # Temporary work around for https://github.com/wrengr/unification-fd/issues/70
      "unification-fd" = self.callPackage
        ({ mkDerivation, base, containers, logict, mtl }:
        mkDerivation {
          pname = "unification-fd";
          version = "0.11.2";
          sha256 = "1lyx3g10llkr7vl7c2j15ddlqrkz2r684d1laza7nvq97amrqnqv";
          revision = "1";
          editedCabalFile = "07xmrqmk99lnp3jyk0dqgnpprm3ghnyjdqva0y13ddh3nw8iiqdj";
          libraryHaskellDepends = [ base containers logict mtl ];
          description = "Simple generic unification algorithms";
          license = nixpkgs.lib.licenses.bsd3;
          hydraPlatforms = nixpkgs.lib.platforms.none;
          patches = [ ./unification.patch ];
        }) {};
    };
  };

  coq = nixpkgs.callPackage ./Simplicity.Coq.nix {
    alectryon = if withAlectryon then pp.alectryon else null;
    inherit (cp) coq serapi;
    inherit safegcd-bounds vst;
  };

  c = nixpkgs.callPackage ./Simplicity.C.nix {
    inherit doCheck production wideMultiply withCoverage withProfiler withTiming withValgrind;
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

  safegcd-bounds = nixpkgs.callPackage ./safegcd-bounds.nix {
    inherit (cp) coq;
    cheating = withSafegcdCheat;
  };

  # $ nix-build -A inheritance -o inheritance.Coq.eps
  inheritance = nixpkgs.runCommand "inheritance.Coq.eps" { buildInputs = [ nixpkgs.graphviz ]; } "dot ${./inheritance.Coq.dot} -Teps -o $out";
}
