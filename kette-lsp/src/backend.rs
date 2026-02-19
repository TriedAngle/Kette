use std::collections::HashMap;

use parser::ast::Expr;
use parser::token::Token;
use parser::{Lexer, ParseError, Parser};
use tokio::sync::RwLock;
use tokio::time::{sleep, Duration};
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
use crate::diagnostics::diagnostics_from_semantic_issues;
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
    analyzed_version: i32,
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
        let parse_results: Vec<_> = Parser::new(Lexer::from_str(source)).collect();

        let parse_errors: Vec<ParseError> = parse_results
            .iter()
            .filter_map(|r| r.as_ref().err().cloned())
            .collect();
        let exprs: Vec<Expr> =
            parse_results.into_iter().filter_map(|r| r.ok()).collect();

        let mut diagnostics =
            diagnostics_from_parse_errors(source, &parse_errors);
        let semantic = parser::semantic::analyze_semantics_with_mode(
            &[],
            &exprs,
            parser::semantic::AnalysisMode::Strict,
        );
        diagnostics.extend(diagnostics_from_semantic_issues(
            source,
            &semantic.issues,
        ));
        let semantic_tokens = Self::semantic_tokens_for_source(source, &exprs);
        (diagnostics, semantic_tokens)
    }

    fn diagnostics_for_source(source: &str) -> Vec<Diagnostic> {
        let parse_results: Vec<_> = Parser::new(Lexer::from_str(source)).collect();
        let parse_errors: Vec<ParseError> = parse_results
            .iter()
            .filter_map(|r| r.as_ref().err().cloned())
            .collect();
        let exprs: Vec<Expr> =
            parse_results.into_iter().filter_map(|r| r.ok()).collect();

        let mut diagnostics = diagnostics_from_parse_errors(source, &parse_errors);
        let semantic = parser::semantic::analyze_semantics_with_mode(
            &[],
            &exprs,
            parser::semantic::AnalysisMode::Strict,
        );
        diagnostics.extend(diagnostics_from_semantic_issues(
            source,
            &semantic.issues,
        ));
        diagnostics
    }

    fn semantic_tokens_for_source(source: &str, exprs: &[Expr]) -> Vec<SemanticToken> {
        let semantic_input: Vec<Token> = Lexer::from_str(source)
            .filter(|t| {
                !t.is_eof()
                    && !matches!(t.kind, parser::token::TokenKind::Error(_))
            })
            .collect();
        semantic::semantic_tokens_from(source, &semantic_input, exprs)
    }

    fn semantic_tokens_from_text(source: &str) -> Vec<SemanticToken> {
        let parse_results: Vec<_> = Parser::new(Lexer::from_str(source)).collect();
        let exprs: Vec<Expr> =
            parse_results.into_iter().filter_map(|r| r.ok()).collect();
        Self::semantic_tokens_for_source(source, &exprs)
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
            doc.semantic_tokens = semantic_tokens;
            doc.analyzed_version = version;
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
                    analyzed_version: -1,
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

        {
            let mut docs = self.documents.write().await;
            let entry =
                docs.entry(uri.clone()).or_insert_with(|| DocumentState {
                    text: String::new(),
                    version,
                    analyzed_version: -1,
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
        }

        let text = {
            let docs = self.documents.read().await;
            let Some(doc) = docs.get(&uri) else {
                return;
            };
            if doc.version != version {
                return;
            }
            doc.text.clone()
        };

        let semantic_tokens = Self::semantic_tokens_from_text(&text);
        {
            let mut docs = self.documents.write().await;
            let Some(doc) = docs.get_mut(&uri) else {
                return;
            };
            if doc.version != version {
                return;
            }
            doc.semantic_tokens = semantic_tokens;
            doc.analyzed_version = version;
        }

        sleep(Duration::from_millis(120)).await;

        let text = {
            let docs = self.documents.read().await;
            let Some(doc) = docs.get(&uri) else {
                return;
            };
            if doc.version != version {
                return;
            }
            doc.text.clone()
        };

        let diagnostics = Self::diagnostics_for_source(&text);
        self.client
            .publish_diagnostics(uri, diagnostics, Some(version))
            .await;
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

        let tokens = if doc.analyzed_version == doc.version {
            doc.semantic_tokens.clone()
        } else {
            let fresh = Self::semantic_tokens_from_text(&doc.text);
            let mut docs = self.documents.write().await;
            if let Some(current) = docs.get_mut(&uri) {
                if current.version == doc.version {
                    current.semantic_tokens = fresh.clone();
                    current.analyzed_version = current.version;
                }
            }
            fresh
        };

        Ok(Some(SemanticTokensResult::Tokens(SemanticTokens {
            result_id: Some(doc.version.to_string()),
            data: tokens,
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
