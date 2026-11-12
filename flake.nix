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
            pkgs.cargo-watch
            pkgs.graphviz
            pkgs.lldb_22
            pkgs.libiconv
            pkgs.samply # a profiler
            pkgs.tokei
          ];
        };
      });
    };
}
