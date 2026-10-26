# Stage B3a notes: `Computational/PqxdhExtractRomFamily`

Module: `/tmp/bc-arc-scratch/c-work/b3a/PqxdhExtractRomFamily.lean`, namespace `BeaconcryptCore.Computational.PqxdhExtractRomFamily`. Worktree `/tmp/beaconcrypt-authenticated-root-completion` (branch `codex/full-proof-composition`, HEAD `7a9190f`, B1 and B2 modules untracked but built). No tracked file edited, no git state change.

## Checkpoint 0: reading done

- Design sources read: `b-design.md` sections 1.4, 1.5, 5, 6.2 and the B3a row of section 7; `BDesignCheck.lean` (`romImpl`, `rom_public_real`, `rootExpand_outside`); B1 module `PqxdhExtractRomSeparation.lean`; plan section 6.
- The design gives statements only for `romImpl` and `rom_public_real`. `rom_hit`, `rom_miss`, `rom_derive_hit` and `rom_side` are named only. Their statements are chosen by analogy with the existing `PqxdhJointDhExtractFamily.protected_hit`, `protected_miss`, `derive_hit` and `side_real`, and with design line 795 ("the `rom_*` lemmas read only the cache").
- Interpretation of `rom_side`: the existing `side_real` says attacker-computable side sessions stay consistent with public Extract. In R1 that consistency comes from the shared table: an honest derive and the adversary's public zero-salt query at the same actual input bytes are the same lazy-table read (same block, same resulting cache).

## Checkpoint 1: draft compiled

- Draft compiled at the third attempt (about 4 s per compile through the lock; the first two attempts fixed a `change` in `rom_derive_oracle`, a match left unreduced in `rom_root`, the ambiguous name `History` (`PqxdhJointIdentity.History` vs `PqxdhJointDhExtractFamily.History`), the keyword `extends` used as a binder name, and the deprecated `if_pos`/`if_neg`, now `eq_true`/`eq_false` with `↓reduceIte`).
- All 21 theorems compile with axioms within `[propext, Classical.choice, Quot.sound]` (`rootExpand_outside`: `[propext]`). Guards not yet in repository form.

## Checkpoint 2: compiled, guarded (final)

Compile: `cd /tmp/beaconcrypt-authenticated-root-completion/beaconcrypt-core/proofs/lean && flock /tmp/bc-arc-scratch/lean.lock timeout 3600 lake env lean /tmp/bc-arc-scratch/c-work/b3a/PqxdhExtractRomFamily.lean`: exit 0, about 4 s, no errors or warnings (only Lake's "local changes" notices for Hax and aeneas), all 21 `#guard_msgs` pass. Output in `compile-final.out`.

File: 529 lines, sha256 `9d9abe947f727acb8c97148eb58fd50d1a5df98928761aab3a6209d857a33c23`. Imports `PqxdhJointDhExtractRoot` and `PqxdhExtractRomSeparation` (B1, used by `rom_public_patch`/`rom_derive_patch` through `romHmac`, `eval_other`, `extract_root`).

Counts: 1 definition (`romImpl`, byte-identical to `BDesignCheck.lean`), 21 theorems, 21 axiom guards. No `sorry`/`admit`/`axiom`/`native_decide` (the `check-inventory.sh` regex finds nothing). No `@[simp]`. Every declaration has a docstring; module docstring one paragraph per line. Worktree `git status` unchanged; no lean-lsp-mcp file opened.

Axioms: `rootExpand_outside`: `[propext]`; all other 20: `[propext, Classical.choice, Quot.sound]` (inherited from the decidable vector equality in `romImpl` and VCVio's `randomOracle` lemmas).

Statements (namespace `BeaconcryptCore.Computational.PqxdhExtractRomFamily`; common parameters `hmac joint dh seed scalar`; `R := romImpl hmac joint dh seed scalar`; `inside := key = zeroSalt ∧ message.length = 192`):

- `rom_coin`, `rom_sign` (helpers): for every `extractImpl`, `(R q).run state = (impl hmac joint dh seed scalar extractImpl q).run state` at `.inl coin` / `.inr (.sign message)` (`rfl`).
- `rom_public_real` (listed): `¬inside → (R (.inr (.publicHmac key message))).run state = (impl … extractImpl (.inr (.publicHmac key message))).run state`, for every `extractImpl` (design: `actualExtract hmac` only).
- `rom_public_oracle` (helper): `inside → (R (.inr (.publicHmac key message))).run state = (fun r => (r.1, ⟨state.history ++ [.publicHmac key message r.1], r.2⟩)) <$> (HmacOracle.randomOracle message).run state.cache`.
- `rom_hit` (listed): `inside → state.cache message = some block → … = pure (block, ⟨state.history ++ [.publicHmac key message block], state.cache⟩)`.
- `rom_miss` (listed): `inside → state.cache message = none → … = do let block ← $ᵗ HmacBlock; pure (block, ⟨state.history ++ [.publicHmac key message block], state.cache.cacheQuery message block⟩)`.
- `rom_rejected` (helper): `input … message = none → (R (.inr (.derive message))).run state = pure (none, { state with history := state.history ++ [.derive message none] })`.
- `rom_derive_oracle` (helper): `input … message = some bytes → … = (fun r => (some r.1, ⟨state.history ++ [.derive message (some r.1)], r.2⟩)) <$> (HmacOracle.randomOracle bytes).run state.cache`.
- `rom_derive_hit` (listed): `input … message = some bytes → state.cache bytes = some prk → … = pure (some prk, ⟨state.history ++ [.derive message (some prk)], state.cache⟩)`.
- `rom_derive_miss` (helper): the miss counterpart, sampling `prk ← $ᵗ HmacBlock` and recording `state.cache.cacheQuery bytes prk`.
- `rom_side` (listed): `input … message = some bytes → (fun r => (r.1, r.2.cache)) <$> (R (.inr (.derive message))).run state = (fun r => (some r.1, r.2.cache)) <$> (R (.inr (.publicHmac zeroSalt bytes))).run state`.
- `rootExpand_outside` (scratch-checked in `BDesignCheck.lean`): `¬(prk = zeroSalt ∧ rootExpandInput.length = 192)`.
- `rom_root` (helper): `((R ∘ₛ PqxdhJointDhExtractRoot.reduction) (.inr (.derive message))).run state = match input … message with | none => pure (none, {state with history := … ++ [.derive message none]}) | some bytes => (fun r => (some (expandRoot hmac r.1), ⟨state.history ++ [.derive message (some r.1), .publicHmac r.1 rootExpandInput (hmac.eval r.1 rootExpandInput)], r.2⟩)) <$> (HmacOracle.randomOracle bytes).run state.cache`.
- `rom_forward` (helper): the reduction forwards `.inl coin`, `.inr (.sign m)` and `.inr (.publicHmac k m)` unchanged: `(R ∘ₛ reduction) q = R q` (three conjuncts).
- `rom_history_append` (helper): `(R query).run ⟨history, cache⟩ = (fun r => (r.1, ⟨history ++ r.2.history, r.2.cache⟩)) <$> (R query).run ⟨[], cache⟩` for every query.
- `rom_reduction_history_append` (helper): the same for `R ∘ₛ reduction` and every `RootSpec` query.
- `oracle_step` (helper): `r ∈ support ((HmacOracle.randomOracle bytes).run cache) → cache ≤ r.2 ∧ r.2 bytes = some r.1`.
- `rom_cache_mono`, `rom_reduction_cache_mono` (helpers): on the support, `state.cache ≤ result.2.cache`, for `R` and for `R ∘ₛ reduction`.
- `rom_public_patch` (helper): on the support of a public query, for every `table` agreeing with `result.2.cache`, `result.1 = (romHmac hmac table).eval key message`.
- `rom_derive_patch` (helper): on the support of a derivation with `input … = some bytes`, for every such `table`, `result.1 = some (extract (romHmac hmac table) bytes)`.

Scratch meaning checks (`B3aMeaningCheck.lean`, the module body plus five `example`s; compiled clean, `meaning.out` empty apart from Lake notices):

- a fresh public zero-key query at `bytes` followed by a derivation whose input is `bytes` equals `do let b ← $ᵗ HmacBlock; pure (b, some b)` (the table really is shared, and the lemmas compose);
- from the empty family state the answer to a public zero-key 192-byte query is exactly `$ᵗ HmacBlock` (the in-domain branch is random, not the real HMAC);
- from the empty state a root request returns `some (expandRoot hmac b)` for uniform `b`;
- `rom_public_real` also instantiates at `idealImpl`;
- `zeroSalt.toList = List.replicate 64 0` by `rfl`.

## Deviations and choices

- Statements of `rom_hit`, `rom_miss`, `rom_derive_hit`, `rom_side` were chosen here (the design names them only), modelled on `PqxdhJointDhExtractFamily.protected_hit`, `protected_miss`, `derive_hit`. `rom_side` is interpreted as the R1 counterpart of `side_real`: derive and public zero-key query at the same input bytes are the same table read (answer and resulting cache equal; only the log differs).
- `rom_public_real` is stated for every Extract service `extractImpl` of the existing `impl` rather than only `actualExtract hmac` (strictly stronger; the design's form is the instance `extractImpl := actualExtract hmac`, i.e. `realImpl`).
- Helpers added beyond the B3a row (all small, all guarded): `rom_coin`, `rom_sign`, `rom_public_oracle`, `rom_rejected`, `rom_derive_oracle`, `rom_derive_miss`, `rootExpand_outside` (scratch-checked, not assigned to a stage in the design), `rom_root`, `rom_forward`, `rom_history_append`, `rom_reduction_history_append`, `oracle_step`, `rom_cache_mono`, `rom_reduction_cache_mono`, `rom_public_patch`, `rom_derive_patch`. Purpose: per-query cases for `sym_complete` (B6), `honest_no_rom_public`/`touches_history` (B6: `rom_root`, `rom_forward`, `rootExpand_outside`), history erasure and entry persistence for B8b (design line 795: "the `rom_*` lemmas read only the cache"), the root shape for B3b's `romRoot`, and the link to B1's `romHmac` (the design lists B1 as the dependency of B3a).
- No `NonzeroHonestDh` or `X25519ScalarSpread` introduced.

## Merge TODO (tracked files, not done here)

- Copy to `beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhExtractRomFamily.lean` (after B1 is merged, since it imports `PqxdhExtractRomSeparation`).
- Add `import BeaconcryptCore.Computational.PqxdhExtractRomFamily` to `BeaconcryptCore.lean`.
- `proofs/check-inventory.sh`: `[handwritten-lean]` count +1.
- `proofs/reviewed-inventory.txt`: `handwritten-lean<TAB><sha256><TAB>proofs/lean/BeaconcryptCore/Computational/PqxdhExtractRomFamily.lean`.
- Plain-English explanation in `doc/formal-verification-analysis.md` at B11.
