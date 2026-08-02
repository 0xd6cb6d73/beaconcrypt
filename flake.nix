# SPDX-License-Identifier: 0BSD

{
  description = "Hermetic beaconcrypt formal-verification toolchain";

  inputs = {
    hax.url = "github:cryspen/hax/5b0ba8be6da3c313fdfed1c19dd0f0721a29f4b3";
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
          ];
        });
      });
    };
}
