# A2, serial CI and fail-stop reconciliation

The normal merge joins published A2 archive `01bc3b5a1460982aab49b6ae43ef5404dd793a02` with central `7abf30ae48ccd7c84f4d72f1dae6c51574a5199d`. It preserves the 1,356 central Lean files, all 246 ProVerif-related files from their reviewed parents, the CI workflow and 205 existing portable evidence files. The seven shared metadata/document files are frozen in `source-manifest.json`.

The provenance gate is appended after open CTX in the serial extension recipe and exact regression roster. An omission case checks that it cannot disappear. Per-target and overall CI budgets remain unchanged. The combined 28 transcript-fidelity tests, inventory and serial recipe dry-run pass; no proof search or Lean build was repeated. Existing A2, C2/C4 fail-stop and all other result scopes remain unchanged.
