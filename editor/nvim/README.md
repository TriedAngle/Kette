# Neovim Setup

This folder contains Neovim runtime files for Kette:

- `ftdetect/kette.vim` filetype detection for `*.ktt`
- `syntax/kette.vim` syntax highlighting
- `lua/kette/lsp.lua` LSP setup helper for `kette-lsp`

Recommended setup is hybrid:

- Vim syntax (`syntax/kette.vim`) provides immediate lexical feedback while typing.
- `kette-lsp` semantic tokens refine names/scopes (`local`, `parameter`, `global`, etc.).

Module paths and qualified export references use `::` (for example `Lib::Nested::Greeter`).

## Install

Add this repository subfolder to your runtimepath in Neovim:

```lua
vim.opt.runtimepath:append("/home/sebastian/Projects/Kette/editor/nvim")
```

Then call the setup helper in your init:

```lua
require("kette.lsp").setup({
  cmd = { "/home/sebastian/Projects/Kette/target/release/kette-lsp" },
})
```

The setup uses `lspconfig`, so ensure `neovim/nvim-lspconfig` is installed.

## Build the language server

```bash
cargo build --release -p kette-lsp
```

Use the release binary in your LSP config for best responsiveness:

`target/release/kette-lsp`

Optional semantic highlight links for Neovim:

```lua
local function set_kette_semantic_hl()
  vim.api.nvim_set_hl(0, "@lsp.type.keyword.kette", { link = "@variable.builtin" })
  vim.api.nvim_set_hl(0, "@lsp.type.punctuation.kette", { link = "Comment" })
end

set_kette_semantic_hl()
vim.api.nvim_create_autocmd("ColorScheme", { callback = set_kette_semantic_hl })
```
