# Lean 4.34.0 dependency compatibility overlays

The Lake manifest is pinned to Aeneas `6852e6474ec508930acba4df79977b3483a10d10` (`nightly-2026.09.03-6852e64`) and Hax-Lean `b49608d5e402577b400569ee989c3f1b69e4aaf3` (`v0.3.17`), matching the Aeneas and Hax-Lean versions selected by the Hax 0.4.0 extraction configuration. Charon remains pinned separately by that configuration to `nightly-2026.09.02`.

`apply-dependency-patches.sh` verifies the Lake configuration, Lean toolchain, Hax extraction configuration, every manifest dependency's revision and checkout root, patch hashes, and resulting diffs before every Lean build. It uses Lake's non-upgrading dependency resolver to materialize exact manifest revisions when a package checkout is missing, rejects local changes in every unpatched dependency, and refuses an unexpected configuration rewrite or dependency checkout change.

## Aeneas

`aeneas-lean-4.34.patch` forward-ports the official unmerged Aeneas Lean 4.33 work from [`95048d69298263591d7b406b38fb2a3b71fce6b3`](https://github.com/cryspen/aeneas/commit/95048d69298263591d7b406b38fb2a3b71fce6b3) and [`48f6fb4b57e13b95bd45899501239a7167dd8b02`](https://github.com/cryspen/aeneas/commit/48f6fb4b57e13b95bd45899501239a7167dd8b02) onto Aeneas `6852e6474ec508930acba4df79977b3483a10d10`, then adapts Lean 4.34's `bv_decide` API and direct BitVec proofs. The overlay retains every original `bv_tac` and `bvify` regression example with its original proposition. Lean 4.34's symbolic bit-vector reifier does not normalize the computed width of a scalar field projection, so the adapter generalizes specialized scalar projections to bit-vector variables while retaining their defining equalities before invoking `bv_decide`. This uses the kernel-checked generalization operation and introduces no assumption. Both modular-arithmetic examples run normally, without error-dropping guards. Beaconcrypt's extracted and handwritten Lean sources contain no `bv_tac` invocations. Pinning the upstream `bump-lean` branch directly is not viable because it predates the `Result` to `RustM` transition and partial-specification interfaces used by Beaconcrypt's generated definitions.

The Aeneas artifact is stored as a plain canonical Git diff rather than a format-patch because the reviewed overlay combines those upstream adaptations with the local source-build and linter configuration; the cited upstream commits identify its inputs, not a synthetic commit containing the combined result.

## Hax-Lean

`hax-lean-4.34.patch` supplies two focused elaboration adaptations for Hax-Lean v0.3.17: explicit fixed-array length facts and a dependent witness elimination accepted by Lean 4.34. The pinned upstream Hax-Lean release still targets Lean and Mathlib 4.31 and includes no corresponding Lean 4.34 adaptation.

The Aeneas overlay disables `preferReleaseBuild` so Lake cannot substitute an upstream archive built from the unpatched tag. It also disables the weak `dupNamespace`, `defProp`, and `ambiguousOpen` linters to keep upstream warning changes from failing Aeneas's warning-clean build; these are style diagnostics, not kernel soundness checks.

These overlays affect only the Lean libraries in Lake's ignored package checkouts. Their revisions match the reviewed Hax 0.4.0 extraction stack so regenerated Beaconcrypt definitions and the libraries used to check them stay aligned. The Makefile runs `lake --rehash build` after preparation so Lake recomputes source hashes; direct `lake build` bypasses these preparation and assurance checks.
