{
  description = "A basic flake with a shell";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.aoc.url = "github:shnarazk/advent-of-code";

  outputs = { self, nixpkgs, flake-utils, aoc }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = nixpkgs.legacyPackages.${system};
      bqn-driver = aoc.packages.${system}.default;
    in {
      devShells.default = pkgs.mkShell {
        packages = [ pkgs.bashInteractive pkgs.entr bqn-driver ];
      };
    });
}
