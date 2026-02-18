# VSCode Integration

This folder contains a minimal VSCode extension that:

- registers `.ktt` as language `kette`
- provides basic TextMate highlighting
- starts `kette-lsp` over stdio for diagnostics + semantic tokens

## Quick Start

1. Build the language server:

```bash
cargo build --release -p kette-lsp
```

2. Build the VSCode extension:

```bash
cd editor/vscode/kette-lsp-client
npm install
npm run compile
```

3. Run it in Extension Development Host:

- open `editor/vscode/kette-lsp-client` in VSCode
- press `F5`
- in the new window, open a `.ktt` file

## User Settings

- `kette.lsp.path`: path to `kette-lsp` binary (default: `kette-lsp` from PATH)
- `kette.lsp.args`: additional args for server launch

Example:

```json
{
  "kette.lsp.path": "/home/sebastian/Projects/Kette/target/release/kette-lsp",
  "kette.lsp.args": []
}
```

## Package (optional)

```bash
cd editor/vscode/kette-lsp-client
npx @vscode/vsce package
```

This creates a `.vsix` file in `editor/vscode/kette-lsp-client`.

Install it with either method:

1. VSCode UI
   - Open Extensions view
   - Click `...` menu -> `Install from VSIX...`
   - Pick the generated `.vsix`

2. CLI

```bash
code --install-extension editor/vscode/kette-lsp-client/kette-lsp-client-0.1.0.vsix
```

After install, set `kette.lsp.path` to your built server path if `kette-lsp` is not on PATH.
