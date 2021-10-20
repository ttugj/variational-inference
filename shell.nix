{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc901" }:
let
  inherit (nixpkgs) pkgs;
  hp = pkgs.haskell.packages.${compiler}.extend (hself: hsuper: rec {
            text-short = pkgs.haskell.lib.dontCheck hsuper.text-short;
       });
  ghc = hp.ghcWithPackages (ps: with ps; [
          categories hmatrix ghc-typelits-natnormalise ghc-typelits-knownnat profunctors vector vector-th-unbox ghc-typelits-extra
        ]);
in
pkgs.stdenv.mkDerivation {
  name = "vi-env";
  buildInputs = [ ghc pkgs.llvm_9 ];
  shellHook = "eval $(egrep ^export ${ghc}/bin/ghc)";
}
