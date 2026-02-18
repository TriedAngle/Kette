import * as vscode from "vscode";
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind,
} from "vscode-languageclient/node";

let client: LanguageClient | undefined;

export async function activate(context: vscode.ExtensionContext): Promise<void> {
  const config = vscode.workspace.getConfiguration("kette");
  const command = config.get<string>("lsp.path", "kette-lsp");
  const args = config.get<string[]>("lsp.args", []);

  const serverOptions: ServerOptions = {
    command,
    args,
    transport: TransportKind.stdio,
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: "file", language: "kette" }],
    synchronize: {
      configurationSection: "kette",
    },
  };

  client = new LanguageClient(
    "kette-lsp",
    "Kette Language Server",
    serverOptions,
    clientOptions,
  );

  context.subscriptions.push(
    vscode.commands.registerCommand("kette.restartLsp", async () => {
      if (!client) {
        return;
      }
      await client.stop();
      await client.start();
      vscode.window.showInformationMessage("Kette LSP restarted");
    }),
  );

  context.subscriptions.push({
    dispose: () => {
      void deactivate();
    },
  });

  await client.start();
}

export async function deactivate(): Promise<void> {
  if (client) {
    await client.stop();
    client = undefined;
  }
}
