{
  description = "A BQN driver for Advent of Code programs";
  inputs.nixpkgs.url = github:NixOS/nixpkgs;
  outputs = { self, nixpkgs }:
  {
    packages = builtins.listToAttrs
      (map
        (system:
           with import nixpkgs { system = "${system}"; };
           {
             name = system;
             value = {
               default =
                 stdenv.mkDerivation rec {
                   name = "aoc-bqn-driver-${version}";
                   pname = "aoc-bqn-driver";
                   version = "20230723-2";
                   src = self;
                   installPhase = ''
                     mkdir -p $out/bin;
                     cp bqn/aoc.bqn $out/bin/aoc
                     cp bqn/aoc.bqn $out/bin/2023
                     cp bqn/aoc.bqn $out/bin/2022
                     cp bqn/aoc.bqn $out/bin/2021
                     cp bqn/aoc.bqn $out/bin/2016
                   '';
                 };
           };
        })
        [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ]
      );
  };
}
