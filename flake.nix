# SPDX-License-Identifier: 0BSD

{
  description = "Hermetic beaconcrypt formal-verification toolchain";

  inputs = {
    hax.url = "github:cryspen/hax/4c9e2b7c75ab1e2b645a4a8361ae86c4504f9800";
    fstar.follows = "hax/fstar";
    nixpkgs.follows = "hax/nixpkgs";
    proof-nixpkgs.url = "github:NixOS/nixpkgs/3de8f8d73e35724bf9abef41f1bdbedda1e14a31";
  };

  outputs = { hax, fstar, nixpkgs, proof-nixpkgs, ... }:
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
            nixpkgs.legacyPackages.${system}.rustup
            fstar.packages.${system}.z3
            nixpkgs.legacyPackages.${system}.ripgrep
            nixpkgs.legacyPackages.${system}.elan
            proof-nixpkgs.legacyPackages.${system}.coqPackages_9_0.coq
            proof-nixpkgs.legacyPackages.${system}.coqPackages_9_0.ssprove
          ];
          SSPROVE_VERSION = proof-nixpkgs.legacyPackages.${system}.coqPackages_9_0.ssprove.version;
        });
      });
    };
}
