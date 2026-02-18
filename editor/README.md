# Kette Neovim Integration

This guide wires Kette into Neovim with:

- filetype detection for `*.ktt`
- syntax highlighting
- parser diagnostics via `kette-lsp`
- semantic highlighting for unary messages, keyword messages, locals, and globals

## 1) Build the language server

From the repo root:

```bash
cargo build -p kette-lsp
```

The binary will be at:

`/home/sebastian/Projects/Kette/target/debug/kette-lsp`

## 2) Expose the Neovim runtime files

Add the repo Neovim folder as a local package (works with normal runtime + lazy.nvim):

```bash
mkdir -p "/home/sebastian/dots/nvim/pack/kette/start"
ln -sfn "/home/sebastian/Projects/Kette/editor/nvim" "/home/sebastian/dots/nvim/pack/kette/start/kette-nvim"
```

If your config is elsewhere, replace `/home/sebastian/dots/nvim` accordingly.

## 3) Register `kette-lsp`

In your Neovim LSP config, add:

```lua
vim.lsp.config('kette_lsp', {
  capabilities = capabilities,
  on_attach = on_attach,
  cmd = { '/home/sebastian/Projects/Kette/target/debug/kette-lsp' },
  filetypes = { 'kette' },
  root_markers = { '.git', 'Cargo.toml' },
  single_file_support = true,
})
vim.lsp.enable('kette_lsp')
```

## 4) Ensure semantic highlight groups are distinct

Add links for Kette semantic token groups:

```lua
local function set_kette_semantic_hl()
  vim.api.nvim_set_hl(0, '@lsp.type.method.kette', { link = 'Function' })
  vim.api.nvim_set_hl(0, '@lsp.type.function.kette', { link = 'Keyword' })
  vim.api.nvim_set_hl(0, '@lsp.type.variable.kette', { link = 'Identifier' })
  vim.api.nvim_set_hl(0, '@lsp.type.namespace.kette', { link = 'Type' })
  vim.api.nvim_set_hl(0, '@lsp.type.operator.kette', { link = 'Operator' })
end

set_kette_semantic_hl()
vim.api.nvim_create_autocmd('ColorScheme', {
  callback = set_kette_semantic_hl,
})
```

Token mapping in `kette-lsp`:

- unary messages -> `method`
- keyword messages -> `function`
- locals -> `variable`
- globals -> `namespace`
- binary operators -> `operator`

## 5) Restart Neovim and verify

Open a `.ktt` file and verify:

- `:set filetype?` shows `kette`
- `:LspInfo` shows `kette_lsp`
- syntax errors appear as diagnostics while editing
- unary/keyword/local/global coloring differs
