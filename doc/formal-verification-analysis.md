<!-- SPDX-License-Identifier: 0BSD -->

# Formal verification analysis

[`beaconcrypt-parse`](../beaconcrypt-parse/README.md) uses schema-specific F* verification against pinned, prechecked dependencies, without `--admit`. Extraction, Rust compilation, protocol integration, and handwritten framing/size checks remain outside that proof. Executable core code and proof artifacts are unchanged. See [generation provenance](../beaconcrypt-parse/generated/README.md).
