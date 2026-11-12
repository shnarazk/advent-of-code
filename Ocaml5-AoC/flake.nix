{
  description = "A basic flake with a shell";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      forAllSystems = f:
        builtins.listToAttrs (map (system: { name = system; value = f system; }) systems);
    in {
      devShells = forAllSystems (system: let
        pkgs = nixpkgs.legacyPackages.${system};
      in {
        default = pkgs.mkShell {
          packages = [
            pkgs.bashInteractive
            pkgs.ocamlPackages_latest.angstrom
            pkgs.ocamlPackages_latest.dune_3
            pkgs.ocamlPackages_latest.eio
            pkgs.ocamlPackages_latest.eio_main
            pkgs.ocamlPackages_latest.eio_posix
            pkgs.ocamlPackages_latest.ocaml
            pkgs.ocamlPackages_latest.ocaml-lsp
            pkgs.ocamlPackages_latest.ocamlformat
            pkgs.ocamlPackages_latest.ppx_deriving
            pkgs.ocamlPackages_latest.utop
            pkgs.ocamlPackages_latest.uutf
            pkgs.opam
          ];
        };
      });
    };
}
