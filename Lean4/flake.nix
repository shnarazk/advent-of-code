{
  description = "A basic flake with a shell";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.nixvim.url = "github:nix-community/nixvim";

  outputs =
    {
      nixpkgs,
      flake-utils,
      nixvim,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        nvim = nixvim.legacyPackages.${system};
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [
            # pkgs.bashInteractive
            pkgs.elan
            (nvim.makeNixvim {
              colorschemes.gruvbox.enable = true;
              globals = {
                mapleader = " ";
                maplocalleader = "  ";
              };
              lsp.inlayHints.enable = true;
              lsp.keymaps = [
                {
                  key = "gd";
                  lspBufAction = "definition";
                }
                {
                  key = "gD";
                  lspBufAction = "references";
                }
                {
                  key = "gt";
                  lspBufAction = "type_definition";
                }
                {
                  key = "gi";
                  lspBufAction = "implementation";
                }
                {
                  key = "k";
                  lspBufAction = "hover";
                }
              ];
              plugins.cmp.enable = true;
              plugins.cmp.autoEnableSources = true;
              plugins.lean.enable = true;
              plugins.lean.autoLoad = true;
              plugins.lean.leanPackage = null;
              plugins.lean.settings.mappings = true;
              plugins.lean.settings.progress_bars.enable = false;
              plugins.lualine.enable = true;
              plugins.nvim-surround.enable = true;
              plugins.which-key.enable = true;
              # plugins.tree-sitter.enable = true;
              # plugins.treesitter-textobjects.enable = true;
            })
            # pkgs.nodejs_22
            # pkgs.tokei
            # pkgs.vscodium
          ];
        };
      }
    );
}
