{
  description = "A basic flake with a shell";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = nixpkgs.legacyPackages.${system};
      R = pkgs.rWrapper.override{
            packages = [
              pkgs.rPackages.ggplot2
              pkgs.rPackages.jsonlite
              pkgs.rPackages.igraph
            ];
          };
    in {
      devShells.default = pkgs.mkShell {
        packages = [
          pkgs.bashInteractive
          pkgs.graphviz
          pkgs.julia-bin
          R
        ];
      };
    });
}
