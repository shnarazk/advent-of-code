{
  description       = "Uiua AoC Dev shell";
  inputs = { 
    nixpkgs.url     = "github:NixOS/nixpkgs/nixpkgs-unstable";
    uiua.url        = "github:uiua-lang/uiua";
  };
  outputs = { self, nixpkgs, uiua }:
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
        uiua-driver = nixpkgs.legacyPackages.${system}.stdenv.mkDerivation rec {
           name = "aoc-uiua-driver-${version}";
           pname = "aoc-uiua-driver";
           version = "20231202-1";
           src = self;
           installPhase = ''
             mkdir -p $out/bin;
             cp ./loc.ua $out/bin/loc
             cp ./bench.ua $out/bin/bench
           '';
        };
      in {
        default = pkgs.mkShell {
          packages = [ pkgs.bashInteractive pkgs.uiua ];
          # packages = [ pkgs.bashInteractive uiua.packages.${system}.default uiua-driver ];
        };
      });
    };
}
