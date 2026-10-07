# Item 2, increment 1: Extract/HKDF composition components (S0a, S0b, G1, S3a, G2)

Status: six new Lean modules on branch `claude/extract-composition` (worktree `/tmp/claude-extract-inc1`), based on central `4cc974c0` (`codex/full-proof-composition`, including Codex's `PqxdhRecordLift*` modules). Every module is checked with exact axiom guards, root-imported and listed in the inventory. Independently reviewed at `2fb286d9` by a semantic review and a hygiene review (both "approve with nits"); this revision fixes all their findings: two unguarded theorems in the S0b router module and the totals that undercounted them, the location of the KEM candidate after S0b (it remains in the Extract-table cache keys until S1c), the description of what G1 changes, the re-estimate totals, a missing note on names for consumers and the paragraph on references into `PqxdhJointDhExtractFamily`. The Lean statements are unchanged. Not integrated into central, and central (now `7609c3c8`) is not merged into this branch. No existing module is changed.

The plan is `/tmp/bc-arc-scratch/extract-design/plan.md` (revision 2 with section 15 critique responses, section 16 owner decisions of 2026-10-06 and section 17 implementation decisions of 2026-10-07). Under owner decision 2 (route R1, extended to this line), the zero-key 192-byte HMAC-SHA-512 Extract slice is a random oracle, HMAC-SHA-512 is a PRF and HKDF-Extract on a uniform 32-byte key is a PRG-type game. This increment builds the stages that the plan's section 17 orders first: the two equality stages S0a and S0b, which remove the KEM candidate from every observer and from the Beacon finish, and the three generic lemmas G1 (stage S1a), S3a and G2 (stage S4a).

## Modules

| Stage | Module | Theorems | Main statement | Kind |
| --- | --- | --- | --- | --- |
| S4a (G2) | `PqxdhKeyScheduleFromRoot` | 2 | `fromRoot_bound` | bound, generic |
| S3a | `PqxdhRootFirstEntry` | 13 | `eager_first`, `uniformGame_first` | distribution equality, generic |
| S1a (G1) | `PqxdhExtractRomHiddenSuffix` | 29 | `hidden_suffix_bound` | statistical bound, generic |
| S0a | `PqxdhRegistrationJointKemObserverFree` | 40 | `opaqueBranch_free` | program equality |
| S0b | `PqxdhRegistrationJointBeaconOpaqueFinish` | 20 | `opaqueBranch_marked`, `router_moves` | program equality |
| S0b (router) | `PqxdhRegistrationJointBeaconOpaqueFinishRouter` | 29 | `opaqueBranch_freeRouter` | program equality |

Total: 133 theorems, each with an exact `#print axioms` guard allowing only `propext`, `Classical.choice` and `Quot.sound`.

## G2: the key schedule from a uniform root (`PqxdhKeyScheduleFromRoot`)

```lean
theorem fromRoot_bound (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceFullCorrect source hmac) (distinguisher : Distinguisher) :
    (rootHybrid source distinguisher).boolDistAdvantage
        (PqxdhServerAuthKeySchedule.uniformGame distinguisher) ≤
      (extractRealGame hmac uniform32 (initExtractReduction source hmac distinguisher)).boolDistAdvantage
          (extractUniformGame uniform32 (initExtractReduction source hmac distinguisher)) +
        (hmacPrfRealGame hmac (initExpandReduction source distinguisher)).boolDistAdvantage
          (hmacPrfRandomGame (initExpandReduction source distinguisher)) +
        (extractRealGame hmac uniform32 (stepExtractReduction hmac distinguisher)).boolDistAdvantage
          (extractUniformGame uniform32 (stepExtractReduction hmac distinguisher)) +
        (hmacPrfRealGame hmac (stepExpandReduction distinguisher)).boolDistAdvantage
          (hmacPrfRandomGame (stepExpandReduction distinguisher))
```

This is the plan's G2 statement. It is the middle segment of `PqxdhServerAuthKeySchedule.keySchedule_bound`: the hops `initExtract_hop`, `initExpand_hop`, `init_split`, `stepExtract_hop` and `stepExpand_hop`, joined by triangle inequalities. The reductions make 1, 1, 1 and 2 challenge queries (`initExpandReduction_query_bound`, `stepExpandReduction_query_bound`; each Extract game receives one challenge block). `fromRoot_bound_context` states the same bound when side information is sampled before the root, with the reductions built from `withContext sample distinguisher`.

## S3a: eager sampling of the first fresh entry (`PqxdhRootFirstEntry`)

```lean
theorem eager_first {α : Type} (client : OracleComp (unifSpec + (D →ₒ R)) α) (state : State D R) :
    𝒮[(simulateQ trackedImpl client).run state] =
      𝒮[do let value ← $ᵗ R; (simulateQ (eagerImpl value) client).run state]

theorem uniformGame_first (client : OracleComp RootSpec Bool) :
    𝒟[PqxdhCorrelatedExpandHybrid.uniformGame client] =
      𝒟[do let root ← $ᵗ RootOutput
           (simulateQ (eagerImpl root) client).run' (∅, none)]
```

The lazy uniform table is tracked with the point of its first fresh entry (`trackedImpl`; forgetting the point gives VCVio's lazy random oracle, `tracked_project`). The eager table (`eagerImpl value`) answers the first fresh point with a pre-drawn `value`, later fresh points with fresh uniform values and repeated points from the table. `eager_first` is proved with `PqxdhServerAuthEntryFactor.eager_run`; `first_cached` shows that the recorded first point always holds `value`. `uniformImpl_eq` identifies the root table of the root Expand hybrid with the generic lazy table, so `uniformGame_first` draws entry 0's uniform root before the client runs. It is a distribution equality; no value is programmed.

## G1: splitting the random-oracle table at a hidden suffix (`PqxdhExtractRomHiddenSuffix`)

```lean
theorem hidden_suffix_bound {C : Type} (start : ProbComp (HmacOracle.QueryCache × C))
    (client : C → OracleComp HiddenSpec Bool) (Q : ℕ)
    (keys : HmacOracle.QueryCache × C → Finset Pqxdh.Bytes) (residual : HmacOracle.QueryCache × C → ℕ)
    (covers : ∀ p ∈ support start, ∀ x, p.1 x ≠ none → x ∈ keys p)
    (bounded : ∀ p ∈ support start, (client p.2).IsQueryBoundP IsDirect (residual p))
    (total : ∀ p ∈ support start, (keys p).card + residual p ≤ Q) :
    (sharedGame start client).boolDistAdvantage (splitGame start client) ≤ (Q : ℝ) / 2 ^ 256
```

This is the plan's G1 statement with the binder `prefix` renamed `start` (`prefix` is a Lean keyword). `HiddenSpec = unifSpec + (ExtractOracle + TableOracle)`: a hidden read at 128-byte coordinates `m` and a direct read at a byte string `x`. In `sharedGame`, the prefix produces the table's initial cache and the client's context, a uniform 32-byte `secret` is drawn, and both kinds of read go to the one lazily sampled table (`sharedImpl secret`: a hidden read at `m` reads `familyInput m secret = padFF32 ‖ m ‖ secret`). This is the exact joint sampler: one secret for all hidden reads and one table. In `splitGame`, hidden reads go to a separate coordinate-keyed table (`ExtractOracle.randomOracle`), direct reads go to the public table, and no secret is drawn. The budget depends on the prefix outcome, so prefix cache keys and post-prefix direct reads share one cap, which gives coefficient one.

What the split changes is where the hidden entries live. In `sharedGame` a hidden read uses the entry of the one table at an input that ends in the secret, so which entries the hidden reads use depends on the secret, and a direct read at such an input reaches the same entry. In `splitGame` the hidden entries are keyed by the coordinates alone, depend on no secret and cannot be reached by direct reads. The two worlds differ only when a key of the hidden shape is a prefix cache key or a direct read (`Bad`, `sharedFlag`, `secret_tvDist`), which the guessing term pays for. The split does not make hidden entries at distinct coordinates independent of each other: in `sharedGame` they are already entries of one lazily sampled table at distinct inputs. Their mutual independence, in both worlds, comes from modelling the 192-byte slice as a random oracle (R1); without that idealization, treating Extract outputs at inputs that share one secret 32-byte suffix as independent would be the forbidden decorrelation. The secret is never part of any public context: the split world draws nothing, and the proof uses the secret only in the deferred guessing test.

Proof route (a) of the plan: common state `Tables` (public cache, hidden cache, direct-read log); `view` projects it onto the one table (`shared_project`, valid when the prefix cache has no key of the hidden shape, otherwise an initial collision charged through `keys`); the flagged handlers `sharedFlag` and `splitFlag` agree on every transition that is not a direct read of the hidden shape, and VCVio's `tvDist_simulateQ_run_le_probEvent_output_bad` bounds the distance by the flag probability in the split world (`flagged_tvDist`); the flag is a function of the direct-read log (`flag_log`), and the logged split run is secret-free (`splitFlag_log`); the log has at most `residual p` entries (`splitLog_length`); a union bound over `keys p ∪ log` (`guess_finset_le`, each string has the hidden shape for at most one secret, `guess_le`, `secret_card`) and the averaging lemma `tvDist_bind_le_probEvent` give `prefix_tvDist`; `boolDistAdvantage_le_tvDist` finishes.

## S0a: the observer-free branch (`PqxdhRegistrationJointKemObserverFree`)

```lean
theorem opaqueBranch_free (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        real =
      freeBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        real
```

H0 is `opaqueBranch … false`; the equality holds for both branch bits. `freeBranch` has the same key generation, prefix, challenger encapsulation, uniform draw, stopped router, CCA evaluation, stop status and decision; only its postchallenge step `freePost` differs: every postchallenge handler is erased (`eraseImpl`, `eraseOptionImpl`), so these write-only observers never hold a value:

- the restricted Extract-family history and the native ghost (session and adversary table touches, seal contexts, acceptance snapshot), through `PqxdhServerAuthNative.eraseObservers`;
- the KEM pool/router transcript (queries and replies), including the stopped-router history of the prefix, which enters the postchallenge phase only through the erased start state;
- the identity-pool transcript (identity-routing and signing requests and replies), which the plan asked to be shown free of the candidate; it is erased instead.

The proof is generic (`run_erase`, `run_eraseOption`: the erased run of a handler that never reads its observers is the projection of its run) plus never-read lemmas for every postchallenge handler: the dynamic KEM router for every decapsulation callback (`router_neverRead`), the identity pool (`identity_neverRead`), their combination (`post_neverRead`), the native command backend of the actual source (`impl_neverRead`: Server accept with its snapshot through `tail_oblivious` and `accept_neverRead`, build, public HMAC, BLAKE2b, kernel reveal, Beacon tail and open pool requests), and the private native tail of the opaque resumption (`resume_neverRead`). The decision reads only the stop status and the source's Boolean result (`decision_erase`). Precedents: `PqxdhServerAuthNative.tail_observation` and `PqxdhRegistrationR1Audit` (whose `build_audit` and `hmac_audit` are reused).

## S0b: the marked Beacon finish (`PqxdhRegistrationJointBeaconOpaqueFinish`)

```lean
theorem opaqueBranch_marked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        real =
      markedBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        real

theorem router_moves (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (primitives : Primitives)
    (selected : Nat) (reservation : PqxdhDynamicKemRouter.Reservation KemSK)
    (challenge : MlKem768Ciphertext) (other candidate : MlKemSharedSecret) :
    eraseOptionImpl eraseJoint (PqxdhDynamicKemJointRouter.post primitives kem selected reservation challenge other) ∘ₛ
        markPool selected challenge candidate =
      eraseOptionImpl eraseJoint (PqxdhDynamicKemJointRouter.post primitives kem selected reservation challenge candidate)
```

In `markedBranch` every Beacon finish runs the opaque-handle owner `PqxdhBeaconPhase2Shared.owner` with the handle type `PqxdhPhase2DecapsulationRouting.Shared` (only the type and `materialize` of that module are used). `markedPreparation` keeps every preparation callback of the source, except that the decapsulation reply becomes a handle: on the exact challenge ciphertext under the selected KEM creation index (public handles only; no secret value is compared) the handle is the challenge marker, and every other decapsulation carries its actual result. `markedCompiler` turns the root request into a private request with the DH coordinates and the handle (`RootSpec`); every other tail callback is the source's. `markedImpl` is the source's native backend plus `markedRoot`, the private root interpreter, which alone materializes the marker with the candidate, builds the source root input and reads the same table as the source root callback. The source order (decapsulation before the four DH calls), the no-op `eraseShared`, every rejection and abort branch, and the stop status are those of the source, because the marked owner is related to the native owner by `PqxdhBeaconPhase2Shared.owner_realization`.

Proof: `markPool` overwrites the value of the router's reply to the selected decapsulation of the challenge by the candidate. The router absorbs it (`router_absorbs`), because its reply there is the candidate or a missing-handle rejection; the marking commutes with the encapsulator and the exposed-encapsulation forwarding (`markPool_actual`, `markEnc_hide`) and is pushed into every native handler step (`mark_run`). With the marking in place, the native owner and the opaque-handle owner satisfy the realization obligations for the interpretation `interpret candidate` (`marked_calls`), so every source client step and marked client step have the same marked interpretation (`owner_marked`, `finish_marked`, `client_marked`), and so does every client program (`layered`).

The router's candidate (`PqxdhRegistrationJointBeaconOpaqueFinishRouter`):

```lean
theorem opaqueBranch_freeRouter (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        real =
      freeRouterBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index real
```

`freeRouterBranch` is the marked branch with the post-challenge router holding the fixed public value `placeholder` (32 zero bytes) instead of the candidate. The Beacon still sends the selected decapsulation of the challenge to the router, because the router answers it with a missing-handle rejection if that KEM slot was never created; dropping the request would need the invariant that every live owner's KEM index is below the router's creation count, which spans the client and router layers. The Beacon keeps only the presence of the reply. By `router_moves`, the router holding `placeholder` with that reply overwritten by the candidate is the router holding the candidate; the overwriting is pushed into the program and changes nothing (`markedResume_unmarked`), because no other component sends that request (the Server's raw accept and prefix compiler, every other native handler, Beacon creation, bundle and field reads, and the Server's opaque resumption: `accept_free`, `source_step`, `marked_step`, `client_free`, `resume_free`, counted with `IsQueryBoundP` and VCVio's `IsQueryBoundP.simulateQ_run_StateT_of_step`), and the marked Beacon finish never reads that reply's value (`finish_unmarked`). So the plan's S0b row holds in this form: the router's candidate argument is dead, and the request it still answers carries only the slot's existence.

## Where the KEM candidate is after S0b

In `freeRouterBranch` the candidate is an argument of exactly two things: the private interpreter of the Server's opaque resumption (`KemOpaqueResume.liftImpl`, unchanged from T6) and the private Beacon root interpreter `markedRoot`. The router holds a fixed public value, and no observer holds the candidate (S0a). It is never part of a `SecretInputKdf.Context` or any public context; no fixed-HKDF consumer is used.

The candidate is nevertheless not held only by these two interpreters: it remains in one component of the program state, the keys of the shared Extract-table cache. Both interpreters read the table at the 192-byte input `padFF32 ‖ m ‖ candidate` through `HmacOracle.randomOracle` on the native cache (`PqxdhServerAuthNative.romRootBytes` for the Server's root, and `PqxdhServerAuthNative.sourceRoot`, called by `markedRoot`, for every marked Beacon root) and store that input with its entry in the cache. `PqxdhServerAuthNative.eraseObservers` keeps the cache, because it is not a write-only observer, and the adversary's public `.hmac` (`PqxdhRegistrationJointPublicShared.hmac`, which runs `publicFamily` on the same cache) and every other Server or Beacon root read that same cache. So after S0b the candidate is the 32-byte suffix of cache keys that public reads consult, and a public read at such an input returns the same entry. Plan section 7 lists these cache keys among the private carriers of the candidate and assigns them to S1c, which moves them into a coordinate-keyed hidden table; S0a and S0b do not remove them.

What S1c must do about it. S1b flattens `freeRouterBranch` into G1's `sharedGame` so that this carrier becomes G1's hidden reads: the candidate is G1's `secret`, drawn after the prefix; the reads that the two private interpreters make with the candidate (the Server's selected root, and every Beacon root whose handle is the challenge marker) become hidden reads at the 128-byte coordinates `m` (`familyInput m secret`); and the public `.hmac`, every other Server or Beacon root (including Beacon roots that carry a known decapsulation result) and the prefix's table reads become direct reads or prefix cache keys of the one table. S1c then instantiates `hidden_suffix_bound`. In `splitGame` the hidden entries live in a separate coordinate-keyed table, no secret is drawn and no cache key carries the candidate, at the cost of the guessing term `(qHmac + qAccept + qFinish)/2^256`; this needs `keys` to cover the prefix cache (`covers`) and the prefix reads and the reads after the cut to share one budget (`total`, through the cut-split of `certified`). In the hybrid no reduction is formed over this state before S1c: the S2 reductions are built from `splitGame`, which holds no candidate, and the G2 reductions are applied only at S4b.

State-field survey (plan section 7). The post-challenge state of `freeRouterBranch` consists of the native state `PqxdhServerAuthNative.NativeState`, the router state and the Beacon owners list (`List EncodedEntry`). The native state is `PqxdhJointDhExtractFamily.State` (`history`, erased by S0a, and `cache`) together with `PqxdhServerAuthExperiment.GameState` (`ctx`, the BLAKE2b cache; `server`; `pending`, in which the selected session's token is cleared by the opaque prefix, `PqxdhRegistrationJointKemOpaqueCore.cleared_shape`; `beacon`; `sessions`; and `ghost`, erased by S0a). The router state `PqxdhDynamicKemJointSource.State` is `PqxdhDynamicIdentityPool.SourceState` (`seeds`, and `transcript`, erased by S0a) together with `PqxdhDynamicKemRouter.State` (`created`; `history`, erased by S0a; `forbiddenReveal`; `exhausted`). The semantic review surveyed these fields and found no carrier of the candidate, of a `RootKeyInput` built from it or of the value of the selected decapsulation reply other than the Extract-table cache keys; the field lists above were rechecked against the definitions for this revision. Program state that holds values computed from a root (pending tokens, installed kernels, the BLAKE2b cache and the entries, as opposed to the keys, of the Extract-table cache) is handled by the later stages S1b, S1c and S3b.

## Names for consumers

All names below are in the namespace `BeaconcryptCore.Computational`. Consumers should use the headline names fully qualified: `PqxdhKeyScheduleFromRoot.fromRoot_bound` and `PqxdhKeyScheduleFromRoot.fromRoot_bound_context`; `PqxdhRootFirstEntry.eager_first` and `PqxdhRootFirstEntry.uniformGame_first`; `PqxdhExtractRomHiddenSuffix.hidden_suffix_bound` with its games `PqxdhExtractRomHiddenSuffix.sharedGame` and `PqxdhExtractRomHiddenSuffix.splitGame`; `PqxdhRegistrationJointKemObserverFree.opaqueBranch_free` and `PqxdhRegistrationJointKemObserverFree.freeBranch`; `PqxdhRegistrationJointBeaconOpaqueFinish.opaqueBranch_marked`, `PqxdhRegistrationJointBeaconOpaqueFinish.markedBranch` and `PqxdhRegistrationJointBeaconOpaqueFinish.router_moves`; `PqxdhRegistrationJointBeaconOpaqueFinishRouter.opaqueBranch_freeRouter` and `PqxdhRegistrationJointBeaconOpaqueFinishRouter.freeRouterBranch`.

The short names below are declared in one of the six modules and also in another namespace, so a consumer that opens both namespaces gets an ambiguous name and must write it qualified. The list was checked against central `7609c3c8`: a scratch metaprogram over the root import of `7609c3c8` lists every constant `<namespace>.<name>` for each user-facing declaration name of the six modules (auto-generated equation, recursor and injectivity lemmas excluded; the one user theorem that this filter also dropped, `PqxdhExtractRomHiddenSuffix.eq_familyInput_of_coordinate`, does not occur in the Lean sources of `7609c3c8`), and the declaration list of the six modules shows the one name that two of them declare.

- Declared in two of the new modules: `resume_free`, in `PqxdhRegistrationJointKemObserverFree` (`eraseOutcome <$> opaqueResume … = freeResume …`) and in `PqxdhRegistrationJointBeaconOpaqueFinishRouter` (an `IsQueryBoundP` statement). S1b starts from `freeRouterBranch` and is likely to open both.
- `PqxdhRegistrationJointBeaconOpaqueFinish`: `RootSpec` (also `PqxdhCorrelatedExpand`, `PqxdhJointDhExtractRoot` and `PqxdhRegistrationJointKemOpaqueClient`; S2's `rootClient` uses `PqxdhCorrelatedExpand.RootSpec`); `Shared`, an abbreviation of `PqxdhPhase2DecapsulationRouting.Shared` (also `PqxdhPhase2DecapsulationRouting` and `PqxdhPhase2LiveFinish`); `Secrets`, an abbreviation of `PqxdhBeaconPhase2Shared.Secrets Shared` (also `PqxdhBeaconPhase2Shared`); `interpret` (also `PqxdhServerAuthCtxCalls`, `RawCtxSelectedChain` and `RawCtxSelectedMessageKey`).
- `PqxdhRegistrationJointBeaconOpaqueFinishRouter`: `placeholder` (also `PqxdhRegistrationJointKemOpaqueSuffix`); `source_step` (also 20 other namespaces, among them `PqxdhRegistrationJointSigningTranscript` and `PqxdhRegistrationJointReportFreshness`); `marked_step` (also `RawCtxSelectedFamilyNonceCoupling`); `simulateQ_free` (also `PqxdhDeploymentPublishedTuple`).
- `PqxdhRegistrationJointKemObserverFree`: `evaluate_map` (also `PqxdhServerAuthNative`); `eraseOutcome` (also `PqxdhRegistrationJointInitializedSchedule`); `eraseObservers_idem` (also `PqxdhDeploymentServerAuthStable`); `run_erase` (also `PqxdhDeploymentLaterServerGame`, `PqxdhLaterChallengeGeneratedContinuation`, `PqxdhLaterChallengePreparedCapture`, `PqxdhLaterChallengeSampler` and `PqxdhLaterSavedSampler`).
- `PqxdhRootFirstEntry`: `State` (also 91 other `BeaconcryptCore` namespaces, among them `PqxdhJointDhExtractFamily`, `PqxdhDynamicKemRouter` and `PqxdhDynamicKemJointSource`); `eagerImpl` and `lazyImpl` (also `PqxdhDynamicIdentityPool`); `trackedImpl` (also `RawCtxReceiveConsumption`); `eager_done` (also `PqxdhDeploymentServerAuthEager`).
- `PqxdhExtractRomHiddenSuffix`: `Bad` (also `PqxdhDeploymentServerAuthLocal` and `PqxdhKemCorrectnessError`); `view` (also 12 other namespaces); `logged` (also 7 other namespaces); `sharedImpl` (also `AdaptiveCtxSharedTarget`, `RawCtxCanonicalSeal` and `RawCtxMixedShared`); `splitGame` (also `AdaptiveCtxCanonical`); `splitImpl` (also `AdaptiveCtxCanonical` and `AdaptiveSealKeyFamily`).

Two further names coincide only with names in Lean's own namespaces (`coordinate` with `Lean.Omega.LinearCombo.coordinate`, `overwrite` with `Lean.Lsp.CreateFile.Options.overwrite`). No name was renamed.

## Checks

- Direct checks: each module with Lean 4.34, `-j1 -M8000`, `timeout 180`, through `coord.sh lean`, into the scratch prefix `/tmp/bc-arc-scratch/extract-design/inc1/olean` (a resolved symlink mirror of the first prefix of the published central `LEAN_PATH` of `4cc974c0`, followed by that `LEAN_PATH`). Final checks of all six modules in import order: exit 0, empty logs. After the review fixes, the four changed or dependent modules (G1, S0a, S0b and the S0b router module) were checked again in import order: exit 0, empty logs; S3a and G2 are unchanged.
- Exact axiom guards: 133 of 133 theorems; profiles `propext, Classical.choice, Quot.sound` (109), `propext, Quot.sound` (11), `propext` (7), none (6). The hygiene review found two unguarded theorems, `onLeft_inl` and `onLeft_inr` of the S0b router module: written as `@[simp] theorem` on one line, they were missed by the line-anchored pattern `^theorem ` of the guard generator and of the inventory count, so the earlier totals (27 for that module, 131 in all) were undercounts. Both now have `@[simp]` on its own line and an exact guard (`does not depend on any axioms`), and the inventory block lists them. A scratch metaprogram over the compiled modules finds the set of theorem constants of each module equal to the set of its guard names, in all six modules. Guard liveness: a scratch file with one deliberately wrong guard per module fails six times; after the fix, the same file with a seventh wrong guard (`onLeft_inl` claimed to depend on `propext`) fails seven times.
- Root import `BeaconcryptCore.lean` through `coord.sh lean` with `timeout 180`: exit 0, empty log, before and after the review fixes.
- Focused `make -C beaconcrypt-core check-inventory` in the locked minimal proof flake (`flake.nix` and `flake.lock` identical to the worktree) under a `coord.sh` `@nix` lease at the S0b commit, at the S0b-completion commit and on the tree of the review-fix commit: exit 0, "Formal-verification inventory matches the reviewed boundary."; `git diff --check` clean at every commit; `coord.sh inv recount` and `inv rehash` after every module and after the review fixes.
- Forbidden constructs: no `sorry`, `admit`, `axiom`, `opaque`, `native_decide`, `implemented_by`, `extern` or `unsafe`. Scoped options: `set_option linter.deprecated false in` on ten declarations of S3a and G1 that use VCVio's probability notation (`Pr[…]`, `𝒮[…]`, which VCVio marks deprecated in favour of measures; its identical-until-bad and union-bound lemmas are stated in that notation); no deprecated lemma is used, in particular not `probOutput_true_le_add_ofReal_boolDistAdvantage`. `set_option backward.isDefEq.respectTransparency false in` on `evaluate_map` (S0a), as in the central KEM modules.
- Contamination: the exact-token grep of the plan's risk 9 finds none of its tokens in the six modules. A direct-reference constant scan (a Lean metaprogram over all 470 declarations of the six modules, including auxiliary ones) finds no reference to any listed fixed-HKDF item (`PqxdhCorrelatedExtractFamily.advantage`, `reduction`, `prepare`, `realGame`, `realImpl`, `evaluate`, `productionHiddenRoot`, `RawCtxSourceHkdf.rootResponse`, `PqxdhCorrelatedExpand.rootPost`, `rootResume`, `rootReduction`, `reduction_expanded_eq`, `PqxdhPhase2DecapsulationRouting.derive`, the listed `PqxdhPhase2DhRootConsumer` items, `PqxdhChallengeSecretRouting.*`, `PqxdhBeaconPhase2Routed.*`, `KemOpaqueReal.*`, `MlKem768RecipientCorrectness`, `jointKdfView`, `fixedHkdfSha512JointStream`, games of `PqxdhJointDhExtractFamily`); its liveness case (a scratch definition referencing `PqxdhCorrelatedExtractFamily.realGame`) is detected. The modules do reference `PqxdhJointDhExtractFamily`, but only its family-state types and constructors, which are part of the native state `PqxdhServerAuthNative.NativeState`: `State`, `State.mk`, `State.history`, `State.cache`, `History`, `Observation`, `Observation.derive`, `Observation.publicHmac` and `Message`. A direct-reference scan of types and values (opaque values included) finds 29 such references from 18 declarations: `State` from the S0a never-read lemmas (`accept_neverRead`, `tail_oblivious`, the `oblivious_*` lemmas), from `freeResume`, `markedResume` and their lemmas (`resume_free` in both modules, `resume_marked`, `accept_free`, `markedResume_unmarked`), and the history and cache constructors in `oblivious_romRootBytes` and `oblivious_sourceRoot`, which show that the native Server and Beacon root readers never read the family history or the ghost (`Message` is the message type of `romRootBytes`). The history is what S0a erases; the cache is kept until S1c. No game, reduction or advantage of `PqxdhJointDhExtractFamily` is referenced, so the plan's risk-9 rule, which forbids its games, holds. The exact count depends on which equation lemmas Lean has generated (the hygiene review counted 31).

## Deviations from the plan

- G1: the binder `prefix` is renamed `start`; otherwise the statement is the plan's.
- S0a: the identity-pool transcript is erased rather than shown free of the candidate; the erasure is an equality like the others.
- S0b: the Beacon still requests the selected decapsulation of the challenge from the router and uses only the presence of the reply (to keep the missing-slot rejection without a cross-layer invariant); the router holds a fixed public value instead of the candidate (`opaqueBranch_freeRouter`).
- S3a has no planned statement beyond its description; the statements above are the ones built.
- No planned statement turned out false or unprovable, and none was weakened.

## Remaining item 2 stages and re-estimate

This increment built S0a, S0b (including the router's candidate), S1a, S3a and S4a, which the plan estimated at 15.5 to 26 agent-days, in one working session. The existing source14 infrastructure (realization lemmas, never-read precedents, generic simulation lemmas) made the equality stages much cheaper than planned. Remaining, in the order of plan section 17:

| Stage | Plan estimate | Re-estimate | Note |
| --- | --- | --- | --- |
| S1b skeleton | 10-18 | 5-10 | starts from `freeRouterBranch`; observers, Beacon markers and the router's candidate are already gone |
| S1c ROM split | 4-7 | 2-4 | G1 instance, which removes the candidate from the Extract-table cache keys; prefix read log and cut-split of `certified` |
| S2 root Expand | 3-6 | 2-4 | `rootClient`, `IsRoot` transport, `expanded_uniform_bound` |
| S3b entry factor | 6-10 | 3-6 | `uniformGame_first`, factored forms, `entryD` |
| S4b T7 | 1-2 | 0.5-1 | `fromRoot_bound` |
| T (finish once) | 2-3 | 1-2 | `qRoot = 2` |
| S7 every entry | 2-3 | 1-3 | reuses Codex's `PqxdhRecordLiftLazyTable` |
| S8 bills | 3-5 | 2-4 | |
| S5, S6 | 2.5-4 | 1.5-2.5 | |
| S9 | 5-8 | 3-5 | guide, assumption lists, review |

Remaining total: 21 to 41.5 agent-days, the sum of the rows above (plan: 38.5 to 66 for the same stages). S1b remains the main risk (elaboration memory under `-M8000`).

## Not claimed

No item 2 headline (T7, T8) is stated yet; these modules are components. G1 is a statistical lemma under the random-oracle model of the slice (R1); G2 is generic in the distinguisher. The equalities S0a and S0b charge no advantage and do not change the source's semantics; they assume nothing about the KEM, the codec or the primitives. Not covered: persistence, snapshots, codec internals, running-code access and primitive implementations (owner scope).
