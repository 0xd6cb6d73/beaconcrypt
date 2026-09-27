# SPDX-License-Identifier: 0BSD

{
  description = "Hermetic beaconcrypt formal-verification toolchain";

  inputs = {
    hax.url = "github:cryspen/hax/f8fe69339b69e48a01b8a6a6bcb2ab5e5c5e424d";
    nixpkgs.follows = "hax/nixpkgs";
  };

  outputs = { hax, nixpkgs, ... }:
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
            nixpkgs.legacyPackages.${system}.ripgrep
            nixpkgs.legacyPackages.${system}.elan
            nixpkgs.legacyPackages.${system}.jq
          ];
        });
      });
    };
}
