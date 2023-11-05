{
  description       = "Uiua AoC Dev shell";
  inputs = { 
    nixpkgs.url     = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    uiua.url        = "github:uiua-lang/uiua";
  };
  outputs = { self, nixpkgs, flake-utils, uiua }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = nixpkgs.legacyPackages.${system};
      uiua-driver = nixpkgs.legacyPackages.${system}.stdenv.mkDerivation rec {
         name = "aoc-uiua-driver-${version}";
         pname = "aoc-uiua-driver";
         version = "20231105-2";
         src = self;
         installPhase = ''
           mkdir -p $out/bin;
           cp ./loc.ua $out/bin/loc
           cp ./bench.ua $out/bin/bench
         '';
      };
    in {
      devShells.default = pkgs.mkShell {
        packages = [ pkgs.bashInteractive uiua.packages.${system}.default uiua-driver ];
      };
    });
}
