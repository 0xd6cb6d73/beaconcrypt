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
      cryptoverifVersion = "2.12";
      cryptoverifFor = system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
        in
        pkgs.stdenv.mkDerivation {
          pname = "cryptoverif";
          version = cryptoverifVersion;
          src = pkgs.fetchurl {
            url = "https://cryptoverif.inria.fr/cryptoverif${cryptoverifVersion}.tar.gz";
            hash = "sha256-d3MIYb57+95bB493hdtHiGnTOronYaQo1Qqq1TcJh1c=";
          };
          nativeBuildInputs = [ pkgs.ocaml ];
          strictDeps = true;
          buildPhase = ''
            runHook preBuild
            ./build
            runHook postBuild
          '';
          installPhase = ''
            runHook preInstall
            mkdir -p "$out/bin"
            ./build install "$out"
            runHook postInstall
          '';
        };
    in
    {
      devShells = nixpkgs.lib.genAttrs systems (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          cryptoverif = cryptoverifFor system;
        in
        {
          proofs = hax.devShells.${system}.ci-examples.overrideAttrs (old: {
            nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [
              hax.packages.${system}.rustc
              fstar.packages.${system}.z3
              pkgs.ripgrep
              pkgs.elan
              pkgs.coqPackages_9_0.coq
              pkgs.coqPackages_9_0.ssprove
              cryptoverif
            ];
            CRYPTOVERIF_DEFAULT_LIB = "${cryptoverif}/share/doc/cryptoverif/default.ocvl";
            CRYPTOVERIF_PQ_LIB = "${cryptoverif}/share/doc/cryptoverif/pq.ocvl";
            CRYPTOVERIF_VERSION = cryptoverifVersion;
            SSPROVE_VERSION = pkgs.coqPackages_9_0.ssprove.version;
          });
          cryptoverif = pkgs.mkShell {
            packages = [ cryptoverif ];
            CRYPTOVERIF_DEFAULT_LIB = "${cryptoverif}/share/doc/cryptoverif/default.ocvl";
            CRYPTOVERIF_PQ_LIB = "${cryptoverif}/share/doc/cryptoverif/pq.ocvl";
            CRYPTOVERIF_VERSION = cryptoverifVersion;
          };
        });
    };
}
