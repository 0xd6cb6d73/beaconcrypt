# Semantic-fidelity review notes: PqxdhRegistrationJointCompiledOwner (8fd99de)

Target: /tmp/beaconcrypt-registration-joint-service-composition, branch codex/registration-joint-service-composition, HEAD 8fd99de181bff6e778ce328d21a0aa188416be6a (worktree clean). Module source SHA256 9be837ec...f5ac matches compiled-owner-manifest.json.

## Checks run (shared lock, -j1 -M8000, lane LEAN_PATH, no .olean output)

- Recheck of the target module from source: exit 0, empty output (all 8 `#guard_msgs` axiom guards pass; only propext, Classical.choice, Quot.sound). Log: recheck-target.log.
- ScratchSemantics.lean: `cap none = 56`, `cap (some .decapsulate) = 1`, `cap (some .staticDh) = 1`, `cap (some .localCall) = 0` by rfl; `classify` sends KEM-pool decapsulate to `some .decapsulate`, KEM create/reveal to `some .localCall`; printed statement types of owner_queries/finish_source/finish_continuation.
- ScratchProjection.lean: `keyMap index (pk, left) = keyMap index (pk, right)` by rfl (encode erases the KEM secret).

## owner_queries

- Statement quantifies over arbitrary setup, codec, raw, encoded owner (`PqxdhRegistrationJointBundle.Owner`) and every `kind : Option Kind`; no premise. `IsQueryBoundP` is VCVio's structural `IsRollBound` (`∀ u` over every typed reply), so it covers all replies and failure paths.
- Classes: `classify (.inr _) = none` (whole original native tail), `classify (.inl q) = some (serviceClass q)`; serviceClass maps only KEM-pool `.decapsulate` and identity-pool `.service _ (.staticDh _)` to the two protocol classes; identity create/reveal/sign, both unifSpec coin sides, KEM create/reveal are `localCall` with cap 0. Partition is exhaustive, so the bound implies at most 58 requests and no other private capability.
- Rust `finish_registration` (beacon.rs:402-510): one `mlkem768::decapsulate`, one DH with the converted identity secret (dh2), dh1/dh3/dh4 with prekey/one-time scalars (local), no signing/keygen/reveal; abort path is pure state change. Matches 1/1/0.
- Tail cap 56 is exactly `PqxdhBeaconPhase2Bounds.native_tail_bound` (root + initial64 + app getter + 53 raw-open KDF/hash/AEAD), used directly in the proof via `tail_queries`; compiled tail queries are forwarded unchanged (`compiler (.inr q) = query (.inr q)` = `tailLift`).
- Proof: `native_run` split; prep charged by `prepare_queries` (preCap), tail by `tail_queries`; failed prep and non-InitSent phases are `pure`. Identity DH goes to the owner's own identity index (privateConversion returns identity.1) and decapsulation to key.2 = kemIndex.
- Deterministic preparation callbacks (decode, conversions, local dhPair, assignedId, eraseShared) become `pure` in the compiled program, so they are not counted as requests; consistent with handoff ("deterministic work remains real local work") and their uniform cost is 0 (source_step_uniform).

## owner_interpreted / owner_source / owner_original / owner_continuation / owner_uniform

- Each is `rw [owner_interpreted]` followed by the Finish15 theorem of the same name; statements are identical to Finish15 with `simulateQ callbacks` replaced by the interpreted compiled owner. Premises: identityOwned / kemOwned (the approved local representation slots); owner_uniform additionally the existing `KemBound setup caps`. No new premise. Uniform bound `69 * max 64 (decapsUniform + baseUniform * decapsBase)` inherited verbatim.

## finish_source / finish_continuation

- Premises: `found` (present slot), identityOwned and kemOwned on an arbitrary `pool`. No honest-origin/partnering/admission premise.
- Equality observes (reply, `owners[ownerAddress]?.map encode`, shared). Reply and complete native shared poststate are exact; resulting private pool is dropped from the RHS (scheduler has no pool).
- Limitation: the observation is lossy compared with Finish15 `finish_source`/`finish_continuation`, which expose the whole scheduler state `{shared, owners.set ownerAddress owner'}`. Other owners are not part of the observed tuple and the reinstalled owner is visible only through `encode`, which erases the identity seed (index + Ed25519 public key) and every KEM secret (also in Fresh/FreshWithCoins phases, where kemOwned gives no slot guarantee). The docstrings and the analysis paragraph state exactly this scope ("public reply, mapped reinstalled owner and complete native shared poststate"), so this is not an overclaim; consumers needing raw post-state must combine with Finish15 results and slot preservation.

## Documentation

- Analysis paragraph is one line, accurate, no new assumption claimed. Wording nit: "These are distribution and query-count equalities" — owner_queries and owner_uniform are upper bounds, not equalities.
- Lane handoff README "Exact restart point" still says no whole-owner class theorem was started; the commit added evidence to that directory but did not update the restart point. Manifest scope and analysis paragraph do record the new state.
- No root import / checker / inventory entry; consistent with the lane practice and stated as pending central integration.

## Verdict

APPROVE_WITH_NITS: statements correct, faithful to Rust and to the existing native bounds, no hidden premises, guarded. Nits only (doc wording, stale lane restart point, lossy-but-documented finish projection).
