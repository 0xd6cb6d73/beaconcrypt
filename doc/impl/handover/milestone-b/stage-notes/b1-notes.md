# Stage B1 notes: `Computational/PqxdhExtractRomSeparation`

Module: `/tmp/bc-arc-scratch/c-work/b1/PqxdhExtractRomSeparation.lean` (170 lines, sha256 `0faf1d8df2cec4f66044de02b81184230a7a8025679b1fc38a999e182c185a7f`), namespace `BeaconcryptCore.Computational.PqxdhExtractRomSeparation`. Worktree `/tmp/beaconcrypt-authenticated-root-completion` (branch `codex/full-proof-composition`, HEAD `7a9190f`). No tracked file edited, no git state change, no lean-lsp-mcp file opened.

## Checkpoint 1: draft written

- The design names `production_ratchet_unchanged` and `root_under_patch` without statements (section 7, B1 row). Chosen statements are below.
- Rust citations checked: the non-test `crypto_kdf::hkdf::sha512::extract` calls in `beaconcrypt/src` are only `pqxdh.rs:50` (inside `derive_root_key_input`, lines 46-58, called at `server.rs:414` and `beacon.rs:458`) and `ratchet.rs:89` (inside `symmetric_ratchet_hkdf`, lines 86-98, reached through `ratchet_hkdf` 100-104 and `initial_ratchet_hkdf` 106-110). `pqxdh.rs:537` is inside `#[cfg(all(test, ...))] mod tests` (lines 69-70). Extracted types: `Extraction/Types.lean:40-42` (`SymmetricRatchetKdfRequest`, 32-byte input, 41-byte info) and `149-150` (`RootKeyInput`, 192 bytes).

## Checkpoint 2: compiled, guarded (final)

Compile: `cd /tmp/beaconcrypt-authenticated-root-completion/beaconcrypt-core/proofs/lean && flock /tmp/bc-arc-scratch/lean.lock timeout 3600 lake env lean /tmp/bc-arc-scratch/c-work/b1/PqxdhExtractRomSeparation.lean`: exit 0, about 4 s, no errors, no warnings (only Lake's "local changes" notices for the Hax and aeneas packages), all 10 `#guard_msgs` pass.

Counts: 1 definition (`romHmac`), 10 theorems, 10 axiom guards. No `sorry`/`admit`/`axiom`/`native_decide` (the `check-lean-policy` regex finds nothing). No `@[simp]`. Every declaration has a docstring.

Axioms: `eval_other`, `extract_other`, `extract_root`, `expandRoot_same`, `expandFull_same`: `[propext]`. `romHmac_extract`: `[propext, Quot.sound]`. `ratchet_input_ne`, `root_input_eq`, `production_ratchet_unchanged`, `root_under_patch`: `[propext, Classical.choice, Quot.sound]`.

Statements (in namespace, `open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf PqxdhRefinement`):

- `romHmac hmac table : HmacSha512`, `eval key message := if key = zeroSalt ∧ message.length = 192 then table message else hmac.eval key message`.
- `eval_other`: `¬(key = zeroSalt ∧ message.length = 192) → (romHmac hmac table).eval key message = hmac.eval key message` (added helper).
- `romHmac_extract`: `romHmac hmac (extract hmac) = hmac` (added helper).
- `ratchet_input_ne (request : ratchet.SymmetricRatchetKdfRequest) : (absBytes request.input).length ≠ 192`.
- `root_input_eq (input : pqxdh.RootKeyInput) : (absBytes input.bytes).length = 192`.
- `extract_other`: `input.length ≠ 192 → extract (romHmac hmac table) input = extract hmac input`.
- `extract_root`: `input.length = 192 → extract (romHmac hmac table) input = table input`.
- `expandRoot_same`: `expandRoot (romHmac hmac table) prk = expandRoot hmac prk`.
- `expandFull_same`: `expandFull (romHmac hmac table) domain prk = expandFull hmac domain prk`.
- `production_ratchet_unchanged (source) (hmac) (correct : SourceFullCorrect source hmac) (table) (input : Std.Array Std.U8 32#usize)`: `absBytes (RawCtxSourceHkdf.response source.crypto ⟨input, ratchet.SYM_RATCHET_INFO⟩).bytes = (expandFull (romHmac hmac table) .ratchet (extract (romHmac hmac table) (absBytes input))).toList ∧ absBytes (PqxdhRootTableInitialization.initialResponse source.crypto ⟨input, ratchet.SYM_RATCHET_INFO⟩).bytes = (initialPrefix (expandFull (romHmac hmac table) .ratchet (extract (romHmac hmac table) (absBytes input)))).toList`.
- `root_under_patch (hmac) (table) (input : pqxdh.RootKeyInput)`: `expandRoot (romHmac hmac table) (extract (romHmac hmac table) (absBytes input.bytes)) = expandRoot hmac (table (absBytes input.bytes))`.

Scratch meaning checks (`B1MeaningCheck.lean`, a copy of the module plus five `example`s, compiled clean): `PqxdhRootTableInitialization.initialResponse c r = RawCtxSourceHkdf.initialResponse c r` by `rfl`; `production_ratchet_unchanged` instantiates at the existing toy witness (`PqxdhHypothesisWitness.toySource`, `toyHmac`, `toy_full_correct`), so its premise is satisfiable; a table differing from the real Extract at a root input changes that Extract; a PRK equal to `zeroSalt` gets the real root Expand; the Expand message lengths are 47, 42, 106, 111 and 47 bytes as the docstring says.

## Deviations and choices

- `production_ratchet_unchanged` and `root_under_patch` statements were chosen here (the design names them only). `production_ratchet_unchanged` is a conjunction over both widths of the single Rust adapter `symmetric_ratchet_hkdf` (76-byte ongoing `RawCtxSourceHkdf.response`, 64-byte initial `PqxdhRootTableInitialization.initialResponse`, the one used by `PqxdhServerRegistrationPublication.build` and assigned to the Beacon's `.initial` in the design's handler table). Requests are stated in the constructor form `⟨input, ratchet.SYM_RATCHET_INFO⟩`, as in `KdfLaw`, `InitialKdfLaw` and `RawCtxSourceHkdf.initialResponse_prefix`.
- Its one hypothesis, `SourceFullCorrect source hmac`, is the existing functional contract (no security content) that the design already lists among the headline premises ("source HKDF correctness"). No other theorem has a hypothesis beyond the length side conditions of `extract_other`/`extract_root`/`eval_other`.
- Two helpers added: `eval_other`, `romHmac_extract`.
- The scratch `ratchet_input_ne` used `open Aeneas Aeneas.Std`; the module uses the repository's usual opens and full names for extracted types. Proofs of the seven scratch theorems are unchanged apart from that.
- Imports: `PqxdhFullSecretInputKdf`, `PqxdhRootTableInitialization`, `RawCtxSourceHkdf` (the scratch used the first and third).

## Merge TODO (tracked files, not done here)

- Copy to `beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhExtractRomSeparation.lean`.
- Add `import BeaconcryptCore.Computational.PqxdhExtractRomSeparation` to `BeaconcryptCore.lean`.
- `proofs/check-inventory.sh`: `[handwritten-lean]` count +1 (merged once per wave with B2).
- `proofs/reviewed-inventory.txt`: `handwritten-lean<TAB><sha256><TAB>proofs/lean/BeaconcryptCore/Computational/PqxdhExtractRomSeparation.lean`.
- Plain-English explanation in `doc/formal-verification-analysis.md` at B11.
