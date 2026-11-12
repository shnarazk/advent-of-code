{
  description = "A basic flake with a shell";
  # inputs.my-flakes.url = "github:shnarazk/flakes";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

  outputs =
    { nixpkgs, ... }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      forAllSystems = f:
        builtins.listToAttrs (map (system: { name = system; value = f system; }) systems);
    in
    {
      devShells = forAllSystems (
        system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
        in
        {
          default = pkgs.mkShell {
            packages = [
              pkgs.bashInteractive
              pkgs.julia-bin
              # my-flakes.packages.${system}.julia-bin
              pkgs.watchexec
            ];
          };
        }
      );
    };
}
