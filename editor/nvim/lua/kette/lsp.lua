local M = {}

function M.setup(opts)
  local lspconfig = require("lspconfig")
  local configs = require("lspconfig.configs")
  local util = require("lspconfig.util")

  if not configs.kette_lsp then
    configs.kette_lsp = {
      default_config = {
        cmd = { "kette-lsp" },
        filetypes = { "kette" },
        root_dir = util.root_pattern(".git", "Cargo.toml"),
        single_file_support = true,
      },
    }
  end

  lspconfig.kette_lsp.setup(vim.tbl_deep_extend("force", {}, opts or {}))
end

return M
