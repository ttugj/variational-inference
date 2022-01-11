{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc901" }:
let
  inherit (nixpkgs) pkgs;
  hp = pkgs.haskell.packages.${compiler}.extend (hself: hsuper: rec {
            text-short = pkgs.haskell.lib.dontCheck hsuper.text-short;
       });
  ghc = hp.ghcWithPackages (ps: with ps; [
          hmatrix hmatrix-special ghc-typelits-natnormalise ghc-typelits-knownnat vector ghc-typelits-extra MonadRandom mwc-random 
        ]);
in
pkgs.stdenv.mkDerivation {
  name = "vi-env";
  buildInputs = [ ghc hp.cabal-install pkgs.llvm_9 hp.haskell-language-server ];
  shellHook = "eval $(egrep ^export ${ghc}/bin/ghc)";
}
