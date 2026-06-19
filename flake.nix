{
  description = "rocq-gameboy development environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            pkgs.coqPackages.coq
            pkgs.coqPackages.ITree
            pkgs.coqPackages.paco
            pkgs.coqPackages.ExtLib
            pkgs.coqPackages.vsrocq-language-server
            pkgs.pandoc
            pkgs.python3Packages.alectryon
            pkgs.dune_3
            pkgs.just
            pkgs.coqPackages.coq.ocamlPackages.ocaml
            pkgs.coqPackages.coq.ocamlPackages.findlib
          ];
        };
      }
    );
}
