use std::collections::HashMap;

use parser::ast::Expr;
use parser::token::Token;
use parser::{Lexer, ParseError, Parser};
use tokio::sync::RwLock;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::{
    Diagnostic, DidChangeTextDocumentParams, DidCloseTextDocumentParams,
    DidOpenTextDocumentParams, InitializeParams, InitializeResult, MessageType,
    SemanticToken, SemanticTokens, SemanticTokensFullOptions,
    SemanticTokensLegend, SemanticTokensOptions, SemanticTokensParams,
    SemanticTokensResult, SemanticTokensServerCapabilities, ServerCapabilities,
    TextDocumentSyncCapability, TextDocumentSyncKind, WorkDoneProgressOptions,
};
use tower_lsp::{Client, LanguageServer, async_trait};
use url::Url;

use crate::diagnostics::diagnostics_from_parse_errors;
use crate::semantic;
use crate::text_edit::apply_content_changes;

pub struct Backend {
    client: Client,
    documents: RwLock<HashMap<Url, DocumentState>>,
}

#[derive(Clone, Debug)]
struct DocumentState {
    text: String,
    version: i32,
    semantic_tokens: Vec<SemanticToken>,
}

impl Backend {
    pub fn new(client: Client) -> Self {
        Self {
            client,
            documents: RwLock::new(HashMap::new()),
        }
    }

    fn analyze_source(source: &str) -> (Vec<Diagnostic>, Vec<SemanticToken>) {
        let tokens: Vec<Token> = Lexer::from_str(source).collect();
        let parse_results: Vec<_> =
            Parser::new(tokens.clone().into_iter()).collect();

        let parse_errors: Vec<ParseError> = parse_results
            .iter()
            .filter_map(|r| r.as_ref().err().cloned())
            .collect();
        let exprs: Vec<Expr> =
            parse_results.into_iter().filter_map(|r| r.ok()).collect();

        let semantic_input: Vec<Token> = tokens
            .iter()
            .filter(|t| {
                !t.is_eof()
                    && !t.is_comment()
                    && !matches!(t.kind, parser::token::TokenKind::Error(_))
            })
            .cloned()
            .collect();

        let diagnostics = diagnostics_from_parse_errors(source, &parse_errors);
        let semantic_tokens =
            semantic::semantic_tokens_from(source, &semantic_input, &exprs);
        (diagnostics, semantic_tokens)
    }

    async fn analyze_store_and_publish(
        &self,
        uri: Url,
        version: i32,
        source: String,
    ) {
        let (diagnostics, semantic_tokens) = Self::analyze_source(&source);

        {
            let mut docs = self.documents.write().await;
            let Some(doc) = docs.get_mut(&uri) else {
                return;
            };
            if doc.version != version {
                return;
            }
            if diagnostics.is_empty() {
                doc.semantic_tokens = semantic_tokens;
            }
        }

        self.client
            .publish_diagnostics(uri, diagnostics, Some(version))
            .await;
    }
}

#[async_trait]
impl LanguageServer for Backend {
    async fn initialize(
        &self,
        _: InitializeParams,
    ) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::INCREMENTAL,
                )),
                semantic_tokens_provider: Some(
                    SemanticTokensServerCapabilities::SemanticTokensOptions(
                        SemanticTokensOptions {
                            work_done_progress_options:
                                WorkDoneProgressOptions {
                                    work_done_progress: None,
                                },
                            legend: SemanticTokensLegend {
                                token_types: semantic::token_types(),
                                token_modifiers: semantic::token_modifiers(),
                            },
                            range: None,
                            full: Some(SemanticTokensFullOptions::Bool(true)),
                        },
                    ),
                ),
                ..ServerCapabilities::default()
            },
            server_info: None,
        })
    }

    async fn initialized(&self, _: tower_lsp::lsp_types::InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "kette-lsp initialized")
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = params.text_document.text;
        let version = params.text_document.version;

        {
            let mut docs = self.documents.write().await;
            docs.insert(
                uri.clone(),
                DocumentState {
                    text: text.clone(),
                    version,
                    semantic_tokens: Vec::new(),
                },
            );
        }

        self.analyze_store_and_publish(uri, version, text).await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        let version = params.text_document.version;
        if params.content_changes.is_empty() {
            return;
        }

        let text = {
            let mut docs = self.documents.write().await;
            let entry =
                docs.entry(uri.clone()).or_insert_with(|| DocumentState {
                    text: String::new(),
                    version,
                    semantic_tokens: Vec::new(),
                });
            if let Err(err) =
                apply_content_changes(&mut entry.text, &params.content_changes)
            {
                self.client
                    .log_message(
                        MessageType::ERROR,
                        format!(
                            "failed to apply text change for {}: {}",
                            uri, err
                        ),
                    )
                    .await;
                return;
            }
            entry.version = version;
            entry.text.clone()
        };

        self.analyze_store_and_publish(uri, version, text).await;
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let uri = params.text_document.uri;
        {
            let mut docs = self.documents.write().await;
            docs.remove(&uri);
        }

        self.client.publish_diagnostics(uri, Vec::new(), None).await;
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> Result<Option<SemanticTokensResult>> {
        let uri = params.text_document.uri;
        let source = {
            let docs = self.documents.read().await;
            docs.get(&uri).cloned()
        };

        let Some(doc) = source else {
            return Ok(None);
        };

        Ok(Some(SemanticTokensResult::Tokens(SemanticTokens {
            result_id: Some(doc.version.to_string()),
            data: doc.semantic_tokens,
        })))
    }
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::time::Instant;

    use super::Backend;

    #[test]
    #[ignore = "manual benchmark"]
    fn bench_core_init_analysis() {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../core/init.ktt");
        let source = fs::read_to_string(path).expect("read core/init.ktt");
        let rounds = 5usize;
        let start = Instant::now();

        let mut diag_count = 0usize;
        let mut sem_count = 0usize;
        for _ in 0..rounds {
            let (diags, sem) = Backend::analyze_source(&source);
            diag_count += diags.len();
            sem_count += sem.len();
        }

        let elapsed = start.elapsed();
        let per_round_ms = elapsed.as_secs_f64() * 1000.0 / rounds as f64;
        eprintln!(
            "bench_core_init_analysis rounds={} total_ms={:.2} per_round_ms={:.2} diags={} sem_tokens={}",
            rounds,
            elapsed.as_secs_f64() * 1000.0,
            per_round_ms,
            diag_count / rounds,
            sem_count / rounds
        );
    }
}
