# Evolving-record integration evidence

This record concerns the exact 87-module port from published `73f333cb858bc77ecbdbd4db1655a889b1e69734` onto `76a47a4ff5182e395e1a3faa362f523d8e8625d3`. Its 422 public statements retain their theorem bodies and exact standard-axiom guards. The maintained [integration guide](../../../evolving-record-integration.md) states the results, full source-client query bills and remaining proof obligations.

All 87 modules passed direct Lean 4.34.0 checks with one thread and the shared resource lock; their logs were empty. The complete maintained root also passed. Existing module artifacts were reused only with matching source files; the focused pass does not replace final aggregate verification. Inventory validation passed through the approved minimal Nix flake. No Rust or ProVerif input changed, so no mutation suite or ProVerif rerun was needed for this port.

The four recent cohort manifests and independent semantic reviews are retained alongside the integration evidence. Their original worktree paths identify historical runs, not additional dependencies. The first direct check failed because the new output prefix lacked linked existing artifacts; the first root attempt lacked the already maintained VCVio Partition overlay. Both setup omissions were corrected by reusing the unchanged checked dependencies, without changing any proof statement or proof body. The recorded successful checks use the final complete paths.

The separate integration review must approve root imports, all guard checks, inventory hashes, source equality, query accounting, assumptions and scope before publication. No evolving-record confidentiality or end-to-end proof completion is claimed by this record.
