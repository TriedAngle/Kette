# Neovim Setup

This folder contains Neovim runtime files for Kette:

- `ftdetect/kette.vim` filetype detection for `*.ktt`
- `syntax/kette.vim` syntax highlighting
- `lua/kette/lsp.lua` LSP setup helper for `kette-lsp`

## Install

Add this repository subfolder to your runtimepath in Neovim:

```lua
vim.opt.runtimepath:append("/home/sebastian/Projects/Kette/editor/nvim")
```

Then call the setup helper in your init:

```lua
require("kette.lsp").setup({
  cmd = { "/home/sebastian/Projects/Kette/target/debug/kette-lsp" },
})
```

The setup uses `lspconfig`, so ensure `neovim/nvim-lspconfig` is installed.

## Build the language server

```bash
cargo build -p kette-lsp
```
