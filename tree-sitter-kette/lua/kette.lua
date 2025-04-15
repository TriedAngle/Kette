local M = {}

function M.setup()
  local parser_config = require("nvim-treesitter.parsers").get_parser_configs()
  
  parser_config.kette = {
    install_info = {
      url = "~/Projects/Kette/tree-sitter-kette", -- Path to your grammar directory
      files = {"src/parser.c"},
    },
    filetype = "kette", -- Set the filetype
  }

  vim.filetype.add({
    extension = {
      ktt = "kette", -- Adjust to your file extension
    },
  })
end

function M.reload()
  vim.cmd("TSUninstall kette")
  vim.cmd("TSInstall kette")
  
  -- vim.treesitter.query.invalidate_query_cache("kette")
  
  vim.notify("Kette parser reloaded", vim.log.levels.INFO)
end

vim.api.nvim_create_user_command("KetteReload", function()
  require("kette").reload()
end, {})

return M
