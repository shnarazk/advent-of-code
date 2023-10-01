{
  description            = "A basic flake with a shell";
  inputs = { 
    nixpkgs.url     = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    uiua.url        = "github:uiua-lang/uiua";
  };
  outputs = { self, nixpkgs, flake-utils, uiua }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = nixpkgs.legacyPackages.${system};
    in {
      devShells.default = pkgs.mkShell {
        packages = [ pkgs.bashInteractive uiua.packages.${system}.default ];
      };
    });
}
