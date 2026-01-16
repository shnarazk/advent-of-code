{
  description = "A basic flake with a shell";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = nixpkgs.legacyPackages.${system};
    in {
      devShells.default = pkgs.mkShell {
        packages = [
          pkgs.bashInteractive
          pkgs.ocamlPackages_latest.angstrom
          pkgs.ocamlPackages_latest.dune_3
          pkgs.ocamlPackages_latest.eio
          pkgs.ocamlPackages_latest.eio_main
          pkgs.ocamlPackages_latest.eio_posix
          pkgs.ocamlPackages_latest.ocaml
          pkgs.ocamlPackages_latest.ocamlformat
          pkgs.ocamlPackages_latest.utop
          pkgs.ocamlPackages_latest.ocaml-lsp
          pkgs.opam
        ];
      };
    });
}
