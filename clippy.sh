#!/bin/bash
# Run clippy with strict lints for code quality

cargo clippy --all-features --all-targets -- \
    --deny clippy::undocumented_unsafe_blocks \
    --deny clippy::missing_safety_doc \
    --deny clippy::unwrap_used \
    --deny clippy::approx_constant \
    --warn clippy::needless_lifetimes \
    --warn clippy::let_and_return \
    --warn clippy::explicit_auto_deref \
    --warn clippy::collapsible_if \
    --warn clippy::identity_op \
    --warn clippy::manual_let_else \
    --warn clippy::redundant_closure_for_method_calls \
    --warn clippy::single_match_else \
    --warn clippy::if_not_else \
    --warn clippy::inconsistent_struct_constructor \
    --warn clippy::needless_pass_by_value \
    --warn clippy::must_use_candidate
