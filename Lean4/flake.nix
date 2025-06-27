{
  description = "A basic flake with a shell";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.home.url = "github:shnarazk/flakes";

  outputs =
    {
      nixpkgs,
      flake-utils,
      home,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [
            # pkgs.bashInteractive
            pkgs.elan
            home.packages.${system}.nvim4lean
            # pkgs.nodejs_22
            # pkgs.tokei
          ];
        };
      }
    );
}
