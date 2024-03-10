{
  description = "A basic flake with a shell";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = nixpkgs.legacyPackages.${system};
      bqn-driver = nixpkgs.legacyPackages.${system}.stdenv.mkDerivation rec {
         name = "aoc-bqn-driver-${version}";
         pname = "aoc-bqn-driver";
         version = "20230928-1";
         src = self;
         installPhase = ''
           mkdir -p $out/bin;
           cp ./aoc.bqn $out/bin/aoc
           cp ./aoc.bqn $out/bin/2023
           cp ./aoc.bqn $out/bin/2022
           cp ./aoc.bqn $out/bin/2021
           cp ./aoc.bqn $out/bin/2020
           cp ./aoc.bqn $out/bin/2019
           cp ./aoc.bqn $out/bin/2018
           cp ./aoc.bqn $out/bin/2017
           cp ./aoc.bqn $out/bin/2016
           cp ./aoc.bqn $out/bin/2015
           cp ./aocbench.bqn $out/bin/aocbench
         '';
      };
    in {
      devShells.default = pkgs.mkShell {
        packages = [ pkgs.bashInteractive pkgs.entr bqn-driver ];
      };
    });
}
