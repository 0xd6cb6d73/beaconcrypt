# SPDX-License-Identifier: 0BSD

{
  description = "Hermetic beaconcrypt formal-verification toolchain";

  inputs = {
    hax.url = "github:cryspen/hax/4fad0ae6268bc0817cafcf4f0300e50a481e4d49";
    fstar.follows = "hax/fstar";
    nixpkgs.follows = "hax/nixpkgs";
  };

  outputs = { hax, fstar, nixpkgs, ... }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
    in
    {
      devShells = nixpkgs.lib.genAttrs systems (system: {
        proofs = hax.devShells.${system}.ci-examples.overrideAttrs (old: {
          nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [
            hax.packages.${system}.rustc
            fstar.packages.${system}.z3
            nixpkgs.legacyPackages.${system}.ripgrep
            nixpkgs.legacyPackages.${system}.elan
            nixpkgs.legacyPackages.${system}.coqPackages_9_0.coq
            nixpkgs.legacyPackages.${system}.coqPackages_9_0.ssprove
          ];
          SSPROVE_VERSION = nixpkgs.legacyPackages.${system}.coqPackages_9_0.ssprove.version;
        });
      });
    };
}
