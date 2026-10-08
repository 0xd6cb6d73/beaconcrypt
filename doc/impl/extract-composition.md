# Item 2: Extract/HKDF composition (increments 1 and 2)

Status: increment 1 (six modules: stages S0a, S0b, G1, S3a and G2) is integrated into central at `ae4a4996`. Increment 2 (twelve modules: stages S1b, S1c and S2) is on branch `claude/extract-composition` (worktree `/tmp/claude-extract-inc1`): it was independently reviewed at `09ae745b` by a semantic review and a hygiene review, central `62c5f4b7` was merged into the branch (`f14a8046`), the next commit (`0ea4260c`) fixes all review findings without changing any Lean statement, and central `f20cb4b0` was then merged as well (`a6c50b30`). Increment 2 is not yet integrated into central; central has since moved to `7045f0f6` (one Codex commit; a trial merge conflicts only in the inventory count line and digests), which the integration step merges. Neither increment changes an existing module.

The plan is `/tmp/bc-arc-scratch/extract-design/plan.md` (revision 2 with section 15 critique responses, section 16 owner decisions of 2026-10-06, section 17 implementation decisions of 2026-10-07, section 18 the service signature fixed by CE-11, section 19 the increment-1 status and section 20 the increment-2 interface notes); `doc/impl/extract-composition-plan.md` is a snapshot of it. Under owner decision 2 (route R1, extended to this line), the zero-key 192-byte HMAC-SHA-512 Extract slice is a random oracle, and the Extract PRG-type game on a uniform 32-byte key, an additional assumption of Server authentication, is extended to this line. HMAC-SHA-512 as a PRF is a standard game and not part of the R1 idealization; the owner accepted it and the Extract PRG-type game as ordinary primitive games (plan section 16), and their advantages are explicit terms of the bounds.

## Increment 1: components (S0a, S0b, G1, S3a, G2)

Increment 1 builds the stages that the plan's section 17 orders first: the two equality stages S0a and S0b, which remove the KEM candidate from every observer and from the Beacon finish, and the three generic lemmas G1 (stage S1a), S3a and G2 (stage S4a). It consists of six new Lean modules, built on branch `claude/extract-composition` from central `4cc974c0` (`codex/full-proof-composition`, including Codex's `PqxdhRecordLift*` modules). Every module is checked with exact axiom guards, root-imported and listed in the inventory. Independently reviewed at `2fb286d9` by a semantic review and a hygiene review (both "approve with nits"); the review-fix revision fixed all their findings: two unguarded theorems in the S0b router module and the totals that undercounted them, the location of the KEM candidate after S0b (it remains in the Extract-table cache keys until S1c), the description of what G1 changes, the re-estimate totals, a missing note on names for consumers and the paragraph on references into `PqxdhJointDhExtractFamily`. The Lean statements were unchanged. Central `d68e1ce4` was then merged into the branch, and the branch was integrated into central at `ae4a4996`. No existing module is changed.

### Modules

| Stage | Module | Theorems | Main statement | Kind |
| --- | --- | --- | --- | --- |
| S4a (G2) | `PqxdhKeyScheduleFromRoot` | 2 | `fromRoot_bound` | bound, generic |
| S3a | `PqxdhRootFirstEntry` | 13 | `eager_first`, `uniformGame_first` | distribution equality, generic |
| S1a (G1) | `PqxdhExtractRomHiddenSuffix` | 29 | `hidden_suffix_bound` | statistical bound, generic |
| S0a | `PqxdhRegistrationJointKemObserverFree` | 40 | `opaqueBranch_free` | program equality |
| S0b | `PqxdhRegistrationJointBeaconOpaqueFinish` | 20 | `opaqueBranch_marked`, `router_moves` | program equality |
| S0b (router) | `PqxdhRegistrationJointBeaconOpaqueFinishRouter` | 29 | `opaqueBranch_freeRouter` | program equality |

Total: 133 theorems, each with an exact `#print axioms` guard allowing only `propext`, `Classical.choice` and `Quot.sound`.

### G2: the key schedule from a uniform root (`PqxdhKeyScheduleFromRoot`)

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

### S3a: eager sampling of the first fresh entry (`PqxdhRootFirstEntry`)

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

### G1: splitting the random-oracle table at a hidden suffix (`PqxdhExtractRomHiddenSuffix`)

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

### S0a: the observer-free branch (`PqxdhRegistrationJointKemObserverFree`)

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

### S0b: the marked Beacon finish (`PqxdhRegistrationJointBeaconOpaqueFinish`)

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

### Where the KEM candidate is after S0b

In `freeRouterBranch` the candidate is an argument of exactly two things: the private interpreter of the Server's opaque resumption (`KemOpaqueResume.liftImpl`, unchanged from T6) and the private Beacon root interpreter `markedRoot`. The router holds a fixed public value, and no observer holds the candidate (S0a). It is never part of a `SecretInputKdf.Context` or any public context; no fixed-HKDF consumer is used.

The candidate is nevertheless not held only by these two interpreters: it remains in one component of the program state, the keys of the shared Extract-table cache. Both interpreters read the table at the 192-byte input `padFF32 ‖ m ‖ candidate` through `HmacOracle.randomOracle` on the native cache (`PqxdhServerAuthNative.romRootBytes` for the Server's root, and `PqxdhServerAuthNative.sourceRoot`, called by `markedRoot`, for every marked Beacon root) and store that input with its entry in the cache. `PqxdhServerAuthNative.eraseObservers` keeps the cache, because it is not a write-only observer, and the adversary's public `.hmac` (`PqxdhRegistrationJointPublicShared.hmac`, which runs `publicFamily` on the same cache) and every other Server or Beacon root read that same cache. So after S0b the candidate is the 32-byte suffix of cache keys that public reads consult, and a public read at such an input returns the same entry. Plan section 7 lists these cache keys among the private carriers of the candidate and assigns them to S1c, which moves them into a coordinate-keyed hidden table; S0a and S0b do not remove them.

What S1c must do about it. S1b flattens `freeRouterBranch` into G1's `sharedGame` so that this carrier becomes G1's hidden reads: the candidate is G1's `secret`, drawn after the prefix; the reads that the two private interpreters make with the candidate (the Server's selected root, and every Beacon root whose handle is the challenge marker) become hidden reads at the 128-byte coordinates `m` (`familyInput m secret`); and the public `.hmac`, every other Server or Beacon root (including Beacon roots that carry a known decapsulation result) and the prefix's table reads become direct reads or prefix cache keys of the one table. S1c then instantiates `hidden_suffix_bound`. In `splitGame` the hidden entries live in a separate coordinate-keyed table, no secret is drawn and no cache key carries the candidate, at the cost of the guessing term `(qHmac + qAccept + qFinish)/2^256`; this needs `keys` to cover the prefix cache (`covers`) and the prefix reads and the reads after the cut to share one budget (`total`, through the cut-split of `certified`). In the hybrid no reduction is formed over this state before S1c: the S2 reductions are built from `splitGame`, which holds no candidate, and the G2 reductions are applied only at S4b.

State-field survey (plan section 7). The post-challenge state of `freeRouterBranch` consists of the native state `PqxdhServerAuthNative.NativeState`, the router state and the Beacon owners list (`List EncodedEntry`). The native state is `PqxdhJointDhExtractFamily.State` (`history`, erased by S0a, and `cache`) together with `PqxdhServerAuthExperiment.GameState` (`ctx`, the BLAKE2b cache; `server`; `pending`, in which the selected session's token is cleared by the opaque prefix, `PqxdhRegistrationJointKemOpaqueCore.cleared_shape`; `beacon`; `sessions`; and `ghost`, erased by S0a). The router state `PqxdhDynamicKemJointSource.State` is `PqxdhDynamicIdentityPool.SourceState` (`seeds`, and `transcript`, erased by S0a) together with `PqxdhDynamicKemRouter.State` (`created`; `history`, erased by S0a; `forbiddenReveal`; `exhausted`). The semantic review surveyed these fields and found no carrier of the candidate, of a `RootKeyInput` built from it or of the value of the selected decapsulation reply other than the Extract-table cache keys; the field lists above were rechecked against the definitions for this revision. Program state that holds values computed from a root (pending tokens, installed kernels, the BLAKE2b cache and the entries, as opposed to the keys, of the Extract-table cache) is handled by the later stages S1b, S1c and S3b.

### Names for consumers

All names below are in the namespace `BeaconcryptCore.Computational`. Consumers should use the headline names fully qualified: `PqxdhKeyScheduleFromRoot.fromRoot_bound` and `PqxdhKeyScheduleFromRoot.fromRoot_bound_context`; `PqxdhRootFirstEntry.eager_first` and `PqxdhRootFirstEntry.uniformGame_first`; `PqxdhExtractRomHiddenSuffix.hidden_suffix_bound` with its games `PqxdhExtractRomHiddenSuffix.sharedGame` and `PqxdhExtractRomHiddenSuffix.splitGame`; `PqxdhRegistrationJointKemObserverFree.opaqueBranch_free` and `PqxdhRegistrationJointKemObserverFree.freeBranch`; `PqxdhRegistrationJointBeaconOpaqueFinish.opaqueBranch_marked`, `PqxdhRegistrationJointBeaconOpaqueFinish.markedBranch` and `PqxdhRegistrationJointBeaconOpaqueFinish.router_moves`; `PqxdhRegistrationJointBeaconOpaqueFinishRouter.opaqueBranch_freeRouter` and `PqxdhRegistrationJointBeaconOpaqueFinishRouter.freeRouterBranch`.

The short names below are declared in one of the six modules and also in another namespace, so a consumer that opens both namespaces gets an ambiguous name and must write it qualified. The list was checked against central `7609c3c8`: a scratch metaprogram over the root import of `7609c3c8` lists every constant `<namespace>.<name>` for each user-facing declaration name of the six modules (auto-generated equation, recursor and injectivity lemmas excluded; the one user theorem that this filter also dropped, `PqxdhExtractRomHiddenSuffix.eq_familyInput_of_coordinate`, does not occur in the Lean sources of `7609c3c8`), and the declaration list of the six modules shows the one name that two of them declare. Each list below names the other `BeaconcryptCore` namespaces that declare the name; the names that are also declared outside `BeaconcryptCore` are only `interpret`, `view` and `State`, whose entries say so, and `coordinate` and `overwrite` (last paragraph).

- Declared in two of the new modules: `resume_free`, in `PqxdhRegistrationJointKemObserverFree` (`eraseOutcome <$> opaqueResume … = freeResume …`) and in `PqxdhRegistrationJointBeaconOpaqueFinishRouter` (an `IsQueryBoundP` statement). S1b starts from `freeRouterBranch` and is likely to open both.
- `PqxdhRegistrationJointBeaconOpaqueFinish`: `RootSpec` (also `PqxdhCorrelatedExpand`, `PqxdhJointDhExtractRoot` and `PqxdhRegistrationJointKemOpaqueClient`; S2's `rootClient` uses `PqxdhCorrelatedExpand.RootSpec`); `Shared`, an abbreviation of `PqxdhPhase2DecapsulationRouting.Shared` (also `PqxdhPhase2DecapsulationRouting` and `PqxdhPhase2LiveFinish`); `Secrets`, an abbreviation of `PqxdhBeaconPhase2Shared.Secrets Shared` (also `PqxdhBeaconPhase2Shared`); `interpret` (also `PqxdhServerAuthCtxCalls`, `RawCtxSelectedChain` and `RawCtxSelectedMessageKey`, and outside `BeaconcryptCore` VCVio's `SemanticsVia` and `MeasureSemanticsVia`).
- `PqxdhRegistrationJointBeaconOpaqueFinishRouter`: `placeholder` (also `PqxdhRegistrationJointKemOpaqueSuffix`); `source_step` (also 20 other `BeaconcryptCore` namespaces, among them `PqxdhRegistrationJointSigningTranscript` and `PqxdhRegistrationJointReportFreshness`); `marked_step` (also `RawCtxSelectedFamilyNonceCoupling`); `simulateQ_free` (also `PqxdhDeploymentPublishedTuple`).
- `PqxdhRegistrationJointKemObserverFree`: `evaluate_map` (also `PqxdhServerAuthNative`); `eraseOutcome` (also `PqxdhRegistrationJointInitializedSchedule`); `eraseObservers_idem` (also `PqxdhDeploymentServerAuthStable`); `run_erase` (also `PqxdhDeploymentLaterServerGame`, `PqxdhLaterChallengeGeneratedContinuation`, `PqxdhLaterChallengePreparedCapture`, `PqxdhLaterChallengeSampler` and `PqxdhLaterSavedSampler`).
- `PqxdhRootFirstEntry`: `State` (also 91 other `BeaconcryptCore` namespaces, among them `PqxdhJointDhExtractFamily`, `PqxdhDynamicKemRouter` and `PqxdhDynamicKemJointSource`, and 135 namespaces outside `BeaconcryptCore`, in Lean, Std, Mathlib, Aesop, Aeneas, Qq, `PFunctor`, `ShareCommon` and VCVio's `KEMScheme.IND_CCA_Adversary` and `KEMScheme.IND_CPA_Adversary`); `eagerImpl` and `lazyImpl` (also `PqxdhDynamicIdentityPool`); `trackedImpl` (also `RawCtxReceiveConsumption`); `eager_done` (also `PqxdhDeploymentServerAuthEager`).
- `PqxdhExtractRomHiddenSuffix`: `Bad` (also `PqxdhDeploymentServerAuthLocal` and `PqxdhKemCorrectnessError`); `view` (also 12 other `BeaconcryptCore` namespaces and 3 `Lean.Elab` ones: `Lean.Elab.Command.InductiveElabStep1`, `Lean.Elab.Command.PreElabHeaderResult` and `Lean.Elab.HeaderProcessedSnapshot`); `logged` (also 7 other `BeaconcryptCore` namespaces); `sharedImpl` (also `AdaptiveCtxSharedTarget`, `RawCtxCanonicalSeal` and `RawCtxMixedShared`); `splitGame` (also `AdaptiveCtxCanonical`); `splitImpl` (also `AdaptiveCtxCanonical` and `AdaptiveSealKeyFamily`).

Two further names coincide only with names in Lean's own namespaces (`coordinate` with `Lean.Omega.LinearCombo.coordinate`, `overwrite` with `Lean.Lsp.CreateFile.Options.overwrite`). No name was renamed.

### Checks

- Direct checks: each module with Lean 4.34, `-j1 -M8000`, `timeout 180`, through `coord.sh lean`, into the scratch prefix `/tmp/bc-arc-scratch/extract-design/inc1/olean` (a resolved symlink mirror of the first prefix of the published central `LEAN_PATH` of `4cc974c0`, followed by that `LEAN_PATH`). Final checks of all six modules in import order: exit 0, empty logs. After the review fixes, the four changed or dependent modules (G1, S0a, S0b and the S0b router module) were checked again in import order: exit 0, empty logs; S3a and G2 are unchanged.
- Exact axiom guards: 133 of 133 theorems; profiles `propext, Classical.choice, Quot.sound` (109), `propext, Quot.sound` (11), `propext` (7), none (6). The hygiene review found two unguarded theorems, `onLeft_inl` and `onLeft_inr` of the S0b router module: written as `@[simp] theorem` on one line, they were missed by the line-anchored pattern `^theorem ` of the guard generator and of the inventory count, so the earlier totals (27 for that module, 131 in all) were undercounts. Both now have `@[simp]` on its own line and an exact guard (`does not depend on any axioms`), and the inventory block lists them. A scan by declaration range over the compiled modules finds 133 theorem constants, whose names are exactly the 133 guard names of the six sources (an earlier scratch list filtered auto-generated `eq_` lemmas, which also dropped the user theorem `PqxdhExtractRomHiddenSuffix.eq_familyInput_of_coordinate`, and listed 132). Guard liveness: a scratch file with one deliberately wrong guard per module fails six times; after the fix, the same file with a seventh wrong guard (`onLeft_inl` claimed to depend on `propext`) fails seven times.
- Root import `BeaconcryptCore.lean` through `coord.sh lean` with `timeout 180`: exit 0, empty log, before and after the review fixes.
- Focused `make -C beaconcrypt-core check-inventory` in the locked minimal proof flake (`flake.nix` and `flake.lock` identical to the worktree) under a `coord.sh` `@nix` lease at the S0b commit, at the S0b-completion commit and on the tree of the review-fix commit: exit 0, "Formal-verification inventory matches the reviewed boundary."; `git diff --check` clean at every commit; `coord.sh inv recount` and `inv rehash` after every module and after the review fixes.
- Forbidden constructs: no `sorry`, `admit`, `axiom`, `opaque`, `native_decide`, `implemented_by`, `extern` or `unsafe`. Scoped options: `set_option linter.deprecated false in` on ten declarations of S3a and G1 that use VCVio's probability notation (`Pr[…]`, `𝒮[…]`, which VCVio marks deprecated in favour of measures; its identical-until-bad and union-bound lemmas are stated in that notation); no deprecated lemma is used, in particular not `probOutput_true_le_add_ofReal_boolDistAdvantage`. `set_option backward.isDefEq.respectTransparency false in` on `evaluate_map` (S0a), as in the central KEM modules.
- Contamination: the exact-token grep of the plan's risk 9 finds none of its tokens in the six modules. A direct-reference constant scan (a Lean metaprogram over all 470 declarations of the six modules, including auxiliary ones) finds no reference to any listed fixed-HKDF item (`PqxdhCorrelatedExtractFamily.advantage`, `reduction`, `prepare`, `realGame`, `realImpl`, `evaluate`, `productionHiddenRoot`, `RawCtxSourceHkdf.rootResponse`, `PqxdhCorrelatedExpand.rootPost`, `rootResume`, `rootReduction`, `reduction_expanded_eq`, `PqxdhPhase2DecapsulationRouting.derive`, the listed `PqxdhPhase2DhRootConsumer` items, `PqxdhChallengeSecretRouting.*`, `PqxdhBeaconPhase2Routed.*`, `KemOpaqueReal.*`, `MlKem768RecipientCorrectness`, `jointKdfView`, `fixedHkdfSha512JointStream`, games of `PqxdhJointDhExtractFamily`); its liveness case (a scratch definition referencing `PqxdhCorrelatedExtractFamily.realGame`) is detected. The modules do reference `PqxdhJointDhExtractFamily`, but only its family-state types and constructors, which are part of the native state `PqxdhServerAuthNative.NativeState`: `State`, `State.mk`, `State.history`, `State.cache`, `History`, `Observation`, `Observation.derive`, `Observation.publicHmac` and `Message`. A direct-reference scan of types and values (opaque values included) finds 29 such references from 18 declarations: `State` from the S0a never-read lemmas (`accept_neverRead`, `tail_oblivious`, the `oblivious_*` lemmas), from `freeResume`, `markedResume` and their lemmas (`resume_free` in both modules, `resume_marked`, `accept_free`, `markedResume_unmarked`), and the history and cache constructors in `oblivious_romRootBytes` and `oblivious_sourceRoot`, which show that the native Server and Beacon root readers never read the family history or the ghost (`Message` is the message type of `romRootBytes`). The history is what S0a erases; the cache is kept until S1c. No game, reduction or advantage of `PqxdhJointDhExtractFamily` is referenced, so the plan's risk-9 rule, which forbids its games, holds. The exact count depends on which equation lemmas Lean has generated (the hygiene review counted 31).

### Deviations from the plan

- G1: the binder `prefix` is renamed `start`; otherwise the statement is the plan's.
- S0a: the identity-pool transcript is erased rather than shown free of the candidate; the erasure is an equality like the others.
- S0b: the Beacon still requests the selected decapsulation of the challenge from the router and uses only the presence of the reply (to keep the missing-slot rejection without a cross-layer invariant); the router holds a fixed public value instead of the candidate (`opaqueBranch_freeRouter`).
- S3a has no planned statement beyond its description; the statements above are the ones built.
- No planned statement turned out false or unprovable, and none was weakened.

### Remaining item 2 stages and re-estimate

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

### Not claimed

No item 2 headline (T7, T8) is stated yet; these modules are components. G1 is a statistical lemma under the random-oracle model of the slice (R1); G2 is generic in the distinguisher. The equalities S0a and S0b charge no advantage and do not change the source's semantics; they assume nothing about the KEM, the codec or the primitives. Not covered: persistence, snapshots, codec internals, running-code access and primitive implementations (owner scope).

## Increment 2: S1b, S1c and S2

Increment 2 builds stages S1b, S1c and S2 of the plan on branch `claude/extract-composition`, from central `ae4a4996` (which contains increment 1). Scratch, logs and resumption notes: `/tmp/bc-arc-scratch/extract-design/inc2/` (`NOTES.md`). Status: twelve new Lean modules with 207 theorems, each with an exact axiom guard, root-imported and listed in the inventory; commits `73b763e9` (S1b), `f30da2f7` (S1b module documentation names), `4cd25180` (S1c), `bcca3a56` (S2) and `09ae745b` (documentation: the increment-2 checks, the analysis paragraphs and the receipt `doc/impl/proof-receipts/extract-composition-inc2.json`). Independently reviewed at `09ae745b` by a semantic review and a hygiene review. `f14a8046` merges central `62c5f4b7` into the branch (coordination protocol section 6), `0ea4260c` fixes all review findings (section "Increment 2: review fixes" below), `a6c50b30` merges central `f20cb4b0`, and the documentation commit after it re-issues the receipt for that merged tip. Not integrated into central. No existing module is changed.

### S1b: the KEM-ideal branch as G1's shared world (`PqxdhRegistrationJointKemPostSkeleton*`)

| Module | Theorems | Content |
| --- | --- | --- |
| `PqxdhRegistrationJointKemPostSkeletonTools` | 11 | generic: a table at a level of an interpreter stack (`tableAt`), forwarding of table queries (`fwd`, `fwdOption`), state splitting (`split_run`), moving the table below a stateless or an optional stateful interpreter (`push_stateless`, `push_option`) |
| `PqxdhRegistrationJointKemPostSkeletonGroup` | 15 | the grouped Beacon finish and `opaqueBranch_grouped` |
| `PqxdhRegistrationJointKemPostSkeletonServices` | 0 | definitions: the services skeleton (oracles, services with the section 18 types, native layer, `postSkel`), `nativeServices`, `factorHidden` |
| `PqxdhRegistrationJointKemPostSkeletonNative` | 42 | every native-layer step of the grouped branch splits into the skeleton's step with the shared table below it; the table-consistency lemmas |
| `PqxdhRegistrationJointKemPostSkeleton` | 11 | the split of the resumption under any pair of interpreters (`resume_lift_backend`), the grouped resumption under the shared table (`groupedResume_split`), the compilation to G1's interface, coins through the stack, `opaqueBranch_shared` |

```lean
theorem opaqueBranch_shared (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false =
      sharedGame (sharedStart (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
          selected index)
        (sharedClient setup codec checks decision count selected)
```

H0 of the plan (equal to H0b by S0a and S0b) is G1's shared world. `sharedStart` runs the challenger's key generation, the stopped-source prefix up to the selected raw accept (`sourcePreOpaque`) and the challenger's encapsulation, and returns the cache of the shared zero-key 192-byte Extract table at the cut (`cacheOf`) and the context of the post-challenge phase (key pair, prechallenge context, challenge ciphertext). It returns no candidate: the candidate becomes G1's secret, drawn by `sharedGame` after `sharedStart`, where the opaque branch draws its uniform candidate. `sharedClient` is the post-challenge phase of the services skeleton with the native services, compiled to G1's interface by `compileHidden` (a hidden read at coordinates `m` becomes G1's hidden read at `m` followed by real Expand; coins and direct reads are forwarded). It has no candidate argument. In this form the candidate is exactly G1's secret suffix of the hidden reads: the Server's private resumption root and every grouped Beacon finish whose decapsulation handle is the challenge marker read the table at `familyInput m candidate`; every other read of the table (the adversary's public HMAC on the slice, other Server roots, Beacon roots with a known decapsulation result, the Beacon tail's root callback) is a direct read, and the cache keys written before the cut are G1's prefix cache. This is the carrier that increment 1 left for S1c: S1c moves the hidden entries out of the shared cache keys by G1.

The services skeleton. The skeleton's post-challenge phase is a client of two oracles, `TSpec V = ValueOracle V + TableOracle`: hidden reads at 128-byte coordinates with values of type `V`, and direct reads at full byte strings. The plan's services `serverRoot`, `beaconRoot` and `table` are these oracles; the hops interpret them differently (S1b: G1's shared table with real Expand; S1c: G1's split world; S2: a root table). The service record `Services V Response` has `rootOf : V → RootOutput` (the root that the pending token of the hidden Server session holds) and `hidden : V → Hidden Response`, whose two fields have exactly the field types of `PqxdhServerAuthEntryFactor.Services` required by plan section 18: `hiddenBuild : Returned → Option Bytes → ServerState → StateT SealState ProbComp (RustM (Option Response × ServerState))` and `hiddenAfter : PqxdhPhase2DhMetadata.Prepared Response → StateT (SharedState Unit) ProbComp (Option Staged)`. The skeleton records the hidden Server session and its value in its state (`Marks V`: the session index of the Server's private resumption, set at its private root request), dispatches the build of that session to `hiddenBuild` (`buildService`), and hands the continuation of every grouped Beacon finish with the challenge marker to `hiddenAfter`, on the prepared state `embed pending` (its response, ciphertext, ephemeral value, metadata and DH outputs; the Server identity fields and the KEM field are placeholders that no service reads, since both the native and the factored continuation read only `PqxdhPhase2DhRootConsumer.cleared`). `nativeServices` sets `V = RootOutput`, `rootOf = id`, `hiddenBuild` to the source's native response tail on the session's pending token and `hiddenAfter` to the source's native continuation at the root. `factorHidden` instantiates `hidden` by the fields of `PqxdhServerAuthEntryFactor.factorServices setup codec checks context value`, which shows that the factored forms of plan section 18 fit; S3b and S7 instantiate the skeleton with them.

The native layer of the skeleton (`skelImpl`, `resumeImpl`) keeps the game state without analysis observers and the marks; it forwards private-pool and encapsulation requests and sends coins to the exposed encapsulation interface's coin channel. Below it run the source's interpreters, each forwarding the table oracles: the actual encapsulator, the post-challenge router holding `placeholder`, and the CCA evaluation (`evalLayer`). `postSkel` is this stack followed by the decision.

Proof. (1) `opaqueBranch_grouped`: the grouped branch, in which every Beacon finish reaches the native layer as one request for its private root and the continuation after it (`groupedOwner`, `groupNative`; `tail_grouped`, `owner_grouped`, `client_grouped` with S0b's `layered`), and the encapsulation-hiding wrapper of the resumed client is dropped (`forward_actual`). (2) State splitting: every step of the erased grouped native backend and of the erased private resumption interpreter, run from the native state `join cache state`, is the skeleton's step from `state` followed by `opRoot hmac candidate` at `cache` (`groupedImpl_split`, `resumeImpl_split`, `groupedResume_split`); `opRoot` answers a direct read at `x` by the lazily sampled table at `x` and a hidden read at `m` by the table at `familyInput m candidate` with real Expand. The table-consistency lemmas are `split_romRoot_value` (a Server root read on the candidate-suffixed input `KemOpaqueClient.bytes` is a hidden read, by `familyInput_source`), `split_romRoot_table` and `split_sourceRoot` (other roots are direct reads), `split_hmac` (the public HMAC reads the same table on the slice) and `split_group` (a grouped Beacon root is a hidden read on the challenge marker and a direct read on a known result, by `build_root_key_input_abs` and `PqxdhPhase2InputBytes.root_input`, with `afterRoot_embed` for the continuation). (3) The table moves below the actual encapsulator (`push_stateless`, `actual_coins`), below the router (`push_option`, `router_coins`, after `run_eraseOption` with S0a's `post_neverRead` removes its erased observers) and below the CCA evaluation (`push_stateless`, `evalLayer_coins`); the decision reads none of the states. (4) At the bottom `opRoot` with uniform coins is G1's `sharedImpl` composed with `compileHidden` (`shared_compile`). `resume_lift_backend` states only that the Server's resumption splits into its compiled prefix under one interpreter and its private tail under another, for any pair of interpreters; it is `KemOpaqueResume.resume` unfolded, it does not relate the resumption to the source, and no proof uses it (`resumeImpl_backend` shows that the skeleton's resumption interpreter is such a pair). The content that the plan's backend-generic restatement of `KemOpaqueResume.resume_lift` (plan section 9 and risk 4 of section 11) was meant to provide, the source's private resumption with its root request answered by a backend other than the restricted Extract-ROM interpreter with the candidate, is `resumeImpl_split` (per request: the source's resumption interpreter is the skeleton's with the shared table below it) and `groupedResume_split` (the whole resumed client); consumers should use those.

Notes for consumers. The value of the hidden Server session is read at the private root request of the Server's resumption (during the selected raw accept), not at the build; the build reads it from the marks. This is inherent: the source derives the Server root at the accept, as the Rust Server does (`get_shared_secret` in `server.rs` calls `derive_root_key_input` before the response is built), so the program equality fixes it. The value of a hidden Beacon entry is read at its grouped finish request. Plan section 18 and CE-11 design v2 (sections 5.7, 5.8 and 6) expected the first draw of a slot's 108 bytes at "the hidden build and the hidden finish"; with this skeleton the Server slot's first touch is the resumption's private root request, and its value is used only by the build of that session (with the factored services `rootOf` can be a constant, so the pending token holds no part of the value). The skeleton's hidden reads are keyed by 128-byte coordinates (`ValueOracle V := Message →ₒ V`), while plan section 18 has S7 read the per-slot 108 bytes only through `PqxdhRecordLiftLazyTable.impl j`, keyed by `Slot n`. S7 and CE-11 therefore need a layer in front of the lazy table that allocates a slot to each new coordinate in first-touch order, with equal coordinates (for example the Server's and those of the matching Beacon finish) sharing one slot. Plan section 20 and notes in CE-11 design v2 sections 5.7 and 6 record both points, and that CE-11's `defer` and `oblivious` obligations and the first-touch classes of `allowanceG` must be re-checked against an accept-time touch before the remaining CE-11a split steps or S7 start. The skeleton's names are in the namespace `BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton`, shared by its five modules.

### S1c: the random-oracle split at coefficient one (`PqxdhRegistrationJointKemRomSplit*`)

| Module | Theorems | Content |
| --- | --- | --- |
| `PqxdhRegistrationJointKemRomSplitTools` | 8 | generic accounting: `potential_run`, `scan_potential` (the cut-split along the scan to the selected raw accept), `isQueryBoundP_or`, `isQueryBoundP_option_of_step`, `randomOracle_keys` |
| `PqxdhRegistrationJointKemRomSplitPrefix` | 39 | the table-cache keys at the cut: native key growth (`impl_grows`), table requests per source request (`client_bound`, a Beacon finish makes at most one root request), `commands_cut`, `opaqueScan_fits`, `sharedStart_fits` |
| `PqxdhRegistrationJointKemRomSplitPost` | 32 | the table reads after the cut: per skeleton step (`skelImpl_reads`, `resumeImpl_reads`), per source request (`groupedClient_bound`, `resume_root`), through the lower layers (`fwd_reads`, `fwdOption_reads`), `sharedClient_direct` |
| `PqxdhRegistrationJointKemRomSplit` | 7 | `tableBudget`, `certified_table`, `shared_split` (the G1 instance), `opaqueBranch_split` |

```lean
theorem opaqueBranch_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false).boolDistAdvantage
      (splitGame (sharedStart (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index) (sharedClient setup codec checks decision count selected)) ≤
      ((budget (.inl 3) + budget (.inl 5) + budget (.inl 6) : ℕ) : ℝ) / 2 ^ 256
```

The opaque KEM-ideal branch (H0) and G1's split world (H1 of the plan) on S1b's prefix and client are distinguishable with advantage at most `(qAccept + qFinish + qHmac)/2^256`, where `qAccept = budget (.inl 3)`, `qFinish = budget (.inl 5)` and `qHmac = budget (.inl 6)` are T5's source budgets of raw accepts, Beacon finishes and public HMAC requests. This is the plan's coefficient-one term `ε_rom`; the fallback `2·…` was not needed. The premise is exactly T5's `certified`; no assumption is added. In the split world the hidden entries are keyed by their 128-byte coordinates alone (`ExtractOracle.randomOracle`), no secret is drawn, and the KEM candidate is not the suffix of any key of the shared Extract-table cache, which holds only the prefix cache and the direct reads: this removes the carrier that increment 1 left in the cache keys (plan section 19). The step is valid only because the zero-key 192-byte Extract slice is modelled as a random oracle (route R1); R1 also gives the hidden entries at distinct coordinates their mutual independence in both worlds, and without that idealization the split would be the forbidden decorrelation. The theorem's docstring says so.

The budget split (the plan's cut-split of `certified`). G1 needs, for every outcome `p` of the prefix, a finite set `keys p` covering the keys of the table cache at the cut and a bound `residual p` on the direct reads of the client, with `(keys p).card + residual p ≤ Q`. `keys p` is the finite set of cache keys and `residual p = Q - (keys p).card`, with `Q = tableBudget budget`. Two facts give the bound:

- Before the cut (`PqxdhRegistrationJointKemRomSplitPrefix`). Every native step of the source backend adds at most one key to the table cache, and only on a raw accept (its root read), a public HMAC or a Beacon tail root callback (`impl_grows`); every source request makes at most one such native request, and only if it is a raw accept, a Beacon finish (whose native owner makes at most one root request, `nativeOwner_root`) or a public HMAC (`client_bound`). Along the scan of the source program to the selected raw accept, the potential "number of cache keys" and the remaining table budget of the suspended continuation move together (`scan_potential` on the composition of the source client and native backend, `commands_cut`): at a reached cut, the keys number at most `c`, the selected accept and the `c` table requests before it fit `Q` (`c + 1 ≤ Q`), and the continuation keeps `Q - c - 1`. Rejected verifications and rejections before encapsulation complete the run (`opaqueScan_fits`); the stopped router and the Server birth do not touch the cache (`sourcePreOpaque_fits`, `sharedStart_fits`).
- After the cut (`PqxdhRegistrationJointKemRomSplitPost`). Every native step of the skeleton makes at most one table read, and only on a raw accept, a public HMAC, a Beacon tail root callback or a grouped Beacon finish (`skelImpl_reads`); the Server's resumption makes at most one, at its private root request (`resumeImpl_reads`, `resume_root`); every source request of the continuation makes at most one such request, and only if it is a table request of the source (`groupedClient_bound`); the encapsulator, the router and the CCA evaluation forward table reads one for one (`fwd_reads`, `fwdOption_reads`). So the client makes at most `1 + (Q - c - 1) = Q - c` direct reads (`sharedClient_direct`); the one read of the resumption is the selected accept's. Inactive contexts make none (`sharedClient_inactive`).

Every hidden read is a table read too, so the bound counts hidden reads against the budget as well; it is not tight but it is the plan's term.

### S2: the root Expand (`PqxdhRegistrationJointKemRootExpand*`)

| Module | Theorems | Content |
| --- | --- | --- |
| `PqxdhRegistrationJointKemRootExpandLocal` | 6 | generic internalization of a prefix and of the public table into a root client (`publicLocal`, `internalize`; `random_coins`, `split_step`, `split_local_run`, `splitGame_local`); `rootClient`, `splitGame_root`, `splitGame_expanded` |
| `PqxdhRegistrationJointKemRootExpandCount` | 33 | the root count: Beacon finish requests (`FinishKind`, `certified_finish`), inheritance of query bounds by the continuation at the cut (`scan_inherit`, `commands_inherit`, `opaqueScan_inherit`, `sourcePreOpaque_inherit`, `sharedStart_inherit`), hidden reads per skeleton step (`skelImpl_hidden`, `resumeImpl_hidden`), grouped finishes per source request (`groupedClient_group`), forwarding through the lower layers (`fwd_hidden`, `fwdOption_hidden`), `postSkel_hidden`, `publicLocal_root`, `rootClient_root` |
| `PqxdhRegistrationJointKemRootExpand` | 3 | `rootClient_uniform` (the `expanded_uniform_bound` instance), `split_uniform` (H1 to H2), `opaqueBranch_uniform` (S1c and S2 composed) |

```lean
theorem splitGame_root (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    splitGame (sharedStart (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index) (sharedClient setup codec checks decision count selected) =
      randomGame (simulateQ (compile setup.hmac) (rootClient (Reader := Reader) setup codec checks ensureInit supplied
        decision work runtime count selected index))

theorem rootClient_root … (budget) (certified : …) :
    (rootClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
      index).IsQueryBoundP IsRoot (1 + budget (.inl 5))

theorem split_uniform … (budget) (certified : …) :
    (splitGame (sharedStart …) (sharedClient setup codec checks decision count selected)).boolDistAdvantage
      (uniformGame (rootClient …)) ≤
      ∑ slot ∈ Finset.range (1 + budget (.inl 5)),
        (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClient …) slot)).boolDistAdvantage
          (hmacPrfRandomGame (indexedReduction setup.hmac (rootClient …) slot))

theorem opaqueBranch_uniform … (budget) (certified : …) :
    (opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false).boolDistAdvantage (uniformGame (rootClient …)) ≤
      ((budget (.inl 3) + budget (.inl 5) + budget (.inl 6) : ℕ) : ℝ) / 2 ^ 256 +
        ∑ slot ∈ Finset.range (1 + budget (.inl 5)),
          (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClient …) slot)).boolDistAdvantage
            (hmacPrfRandomGame (indexedReduction setup.hmac (rootClient …) slot))
```

(`…` abbreviates the arguments of `opaqueBranch_split`; `certified` is T5's source budget, unchanged. `randomGame` is `PqxdhCorrelatedExtractFamily.randomGame`, `compile` is `PqxdhCorrelatedExpand.compile`, `IsRoot`, `uniformGame` and `indexedReduction` are those of `PqxdhCorrelatedExpandHybrid`.)

The root client. `rootClient` is a client of `PqxdhCorrelatedExpand.RootSpec` (uniform coins and root requests at 128-byte coordinates). It is `internalize start post` at S1b's prefix `sharedStart` and the skeleton's post-challenge phase `postSkel` with the native services. `internalize` runs the prefix on the root client's own coins (key generation, the stopped source up to the selected raw accept, the encapsulation) and then the skeleton client, answering its coins and its hidden reads by its own coin and root requests and every direct read from a lazily sampled public table that it holds itself, starting from the table cache at the cut (`publicLocal`). So the CCA evaluation, the post-challenge router, the actual encapsulator, the native game state (with its BLAKE2b table) and the public zero-key 192-byte table all run inside the root client, as plan section 9 requires; only the hidden table is outside.

The equality (`splitGame_local`, generic in the prefix and the skeleton client). G1's split world answers hidden reads from a coordinate-keyed lazily sampled table (`ExtractOracle.randomOracle`) and direct reads from the public table; the family's `randomGame` answers family queries from the same kind of coordinate-keyed table. Per query (`split_step`), the split world's step at the state `(cache, hidden)` is the root client's step at `cache`, compiled by `compile` (a root request becomes a family query followed by real Expand, exactly as `compileHidden` does for a hidden read) and run under the family's random table at `hidden`; the public table's coins are the root client's coins (`compile_coins`, `random_coins`). Induction (`split_local_run`) and the prefix (`random_coins` again) give the game equality. `splitGame_expanded` then applies `PqxdhCorrelatedExpand.expandedGame_eq`: H1 is the cached-root game with real Expand on `rootClient`.

The root count (`rootClient_root`). `PqxdhCorrelatedExpandHybrid.IsRoot` counts every root request, repeated ones included. The root client makes one root request per hidden read of the skeleton client and none for its coins or its public table (`publicLocal_root`). Hidden reads happen only at the Server's private resumption root (at most one, `resume_root`, which rests on `KemOpaqueCosts.client_root`) and at grouped Beacon finishes whose decapsulation handle is the challenge marker (at most one per grouped finish, `skelImpl_hidden`); raw accepts, public HMAC and Beacon tail root callbacks read only the public table. Each source request of the continuation makes at most one grouped finish, and only if it is a Beacon finish request (`groupedClient_group`, from S1c's `groupedOwner_bound`). The encapsulator, the router and the CCA evaluation forward hidden reads one for one (`fwd_hidden`, `fwdOption_hidden`). The continuation suspended at the cut makes at most `qFinish = budget (.inl 5)` Beacon finish requests, because a continuation of the scan inherits every query bound of the source program (`scan_inherit`, generic in the predicate and the handler, carried through the source client and native backend, the stopped run and the prefix by `commands_inherit`, `opaqueScan_inherit`, `sourcePreOpaque_inherit` and `sharedStart_inherit`). Hence `qRoot = 1 + qFinish`, the plan's conservative count (finish requests before the cut are not subtracted); stage T (plan section 17) tightens it to `2`.

The bound. `rootClient_uniform` is `expanded_uniform_bound` at `rootClient` with `q = 1 + qFinish`: H1 and H2 (`uniformGame rootClient`, every root a fresh uniform root, consistent on repeated coordinates) are distinguishable with advantage at most the sum over `slot < 1 + qFinish` of the HMAC-SHA-512 PRF advantages of `indexedReduction setup.hmac rootClient slot`, each a one-challenge-query adversary. This is the plan's `ε_exp`; it is a standard computational step (after S1c each hidden PRK is a fresh uniform block read only by its Expand). `opaqueBranch_uniform` composes S1c and S2 by the triangle inequality: H0 to H2 costs `ε_rom + ε_exp`.

Candidate freedom. `rootClient` has no candidate argument, and `splitGame_root` shows that it is defined from the arguments of `splitGame`, which draws no candidate; this is the stated lemma of plan section 10 for the S2 reductions, whose `scanSampler` contexts hold stopped states of `rootClient`. Candidate freedom rests on this structure. Two scratch metaprograms support it. The closure check (`inc2/probe/rootclient-closure.lean`) walks the definition closure of `rootClient` across all namespaces (2879 constants through definition values, 4883 when the types of the visited constants are walked as well; theorem values are not entered) and reaches none of the definitions that carry the candidate in the earlier games: `opaqueBranch`, `freeBranch`, `freeRouterBranch`, `groupedBranch`, `opRoot`, G1's `sharedImpl` and `sharedGame`, and `markedRoot`. Its liveness cases are detected (the closure of G1's `sharedGame` reaches `sharedImpl`, and the closure of `groupedBranch` reaches `markedRoot`). The type `MlKemSharedSecret` does occur in the closure, as the type of encapsulation and decapsulation results (for example the known decapsulation results of other ciphertexts), which a name-level walk cannot separate from the candidate. The definition-level term grep (`inc2/probe/rootclient-term-grep.lean`) is narrower: it walks only the values of the 1198 constants of the `BeaconcryptCore` namespace reachable from `rootClient` and matches only direct occurrences of `uniformSample` and `SampleableType.selectElem` in them. It finds such samplings only of DH scalars (`PqxdhJointGapDh.sampleScalar`) and identity seeds (`PqxdhJointIdentity.sampleSeed`), none at `MlKemSharedSecret` or `RootOutput` (both `List.Vector UInt8 32`, so the match is on the type name). It cannot see samplings inside VCVio generics or `setup` fields, for example the BLAKE2b oracle `CtxRomAuth.ctxRandomOracle` (`uniformSampleImpl.withCaching`, 64-byte digests, reached through `hashGame`), the public Extract table's `HmacOracle.randomOracle` draws or the coin queries, so it cannot by itself rule out a candidate draw made through a generic sampler.

Notes for consumers. S3b starts from `uniformGame rootClient` (H2). In it the hidden Server value is the uniform root of the resumption's coordinates, drawn at the selected raw accept's private root request, and each grouped Beacon finish on the challenge marker reads the uniform root of its coordinates (the same root as the Server's when the coordinates coincide). `internalize` and `splitGame_local` are generic in the prefix and the skeleton client, so another instance of the services skeleton with `V = RootOutput` can reuse them.

### Increment 2: checks

- Direct checks: each module with Lean 4.34, `-j1 -M8000`, `timeout 180`, through `coord.sh lean`, into the scratch prefix `/tmp/bc-arc-scratch/extract-design/inc2/olean` (a resolved mirror of the increment-1 integration prefix, which is the first prefix of the published `LEAN_PATH` of central `ae4a4996`, without the root olean), followed by that `LEAN_PATH`. Every module's check after its guards were added had exit 0 and an empty log; after the S2 commit all twelve modules and then the root were checked again in import order: exit 0, empty logs. After the merge of central `62c5f4b7`, all twelve modules and the root were checked in import order against a new scratch prefix `/tmp/bc-arc-scratch/extract-design/inc2/merge62/olean` (a resolved mirror of the first prefix of the published `LEAN_PATH` of `62c5f4b7`, without the root olean) followed by that `LEAN_PATH`, and after the review fixes the five modules with changed documentation, every module that imports them and the root were checked again in import order; after the merge of central `f20cb4b0`, all twelve modules and the root were checked once more in import order against `/tmp/bc-arc-scratch/extract-design/inc2/mergef20/olean` (a resolved mirror of the first prefix of the published `LEAN_PATH` of `f20cb4b0`, without the root olean) followed by that `LEAN_PATH`: exit 0, empty logs.
- Exact axiom guards: 207 of 207 theorems (S1b 79, S1c 86, S2 42); profiles `propext, Classical.choice, Quot.sound` (190), `propext, Quot.sound` (10), `propext` (1), none (6). A scratch metaprogram (`inc2/probe/theorem-coverage.lean`) lists the 878 constants of the twelve modules: every one depends only on `propext`, `Classical.choice` and `Quot.sound`, and the 207 theorem constants with declaration ranges are exactly the 207 guard names (the other 358 theorem constants are generated equation, injectivity and `congr_simp` lemmas). Guard liveness: a scratch file with one deliberately wrong guard for each of the eleven modules with theorems fails eleven times.
- Root import `BeaconcryptCore.lean` through `coord.sh lean` with `timeout 180` after each stage, after the merges of central `62c5f4b7` and `f20cb4b0` and after the review fixes: exit 0, empty log.
- Inventory: `coord.sh inv recount` (1574 to 1586 handwritten Lean files) and `inv rehash` after each stage. The S1b and S1c commits recorded a stale digest of `check-inventory.sh` in `reviewed-inventory.txt`, because the rehash ran before the recount changed the count line; the S2 commit corrects it, and a scratch check of all 2006 digest rows against the S2 tree finds no mismatch. Focused `make -C beaconcrypt-core check-inventory` in the locked minimal proof flake under a `coord.sh` `@nix` lease on the S2 tree, on the tree merged with `62c5f4b7`, on the review-fix tree and on the tree merged with `f20cb4b0`: exit 0, "Formal-verification inventory matches the reviewed boundary.". The merge with central `62c5f4b7` recounted 1594 to 1606 handwritten Lean files and rehashed the root and `check-inventory.sh` (last); the review fixes rehashed the five modules with changed documentation, and a scratch comparison of all 2026 digest rows with the review-fix tree finds no mismatch; the merge with `f20cb4b0` recounted 1596 to 1608 and rehashed the root and `check-inventory.sh` (last). `git diff --check` clean at every commit. Transcript fidelity (`make -C beaconcrypt-core check-proverif-transcript-fidelity` in the same flake under a `@cargo` lease) on the review-fix tree and on the tree merged with `f20cb4b0`: exit 0.
- Forbidden constructs: no `sorry`, `admit`, `axiom`, `opaque`, `native_decide`, `implemented_by`, `extern` or `unsafe` in the twelve modules; no scoped `set_option` (only the module-level `autoImplicit false` and `maxRecDepth 100000`); no probability notation and no deprecated lemma.
- Contamination: the direct-reference constant scan of increment 1, extended to the twelve modules (`inc2/probe/contamination-scan.lean`, 878 declarations), finds no reference to any listed fixed-HKDF item; its liveness case is detected.
- Candidate freedom of `rootClient`: it rests on `splitGame_root` and on `rootClient` having no candidate argument. Supporting scratch checks, described in the S2 section: the closure check (`inc2/probe/rootclient-closure.lean`: 2879 constants of the definition closure across all namespaces, none of the eight candidate-carrying definitions reached, liveness detected) and the definition-level term grep (`inc2/probe/rootclient-term-grep.lean`), whose scope is direct `uniformSample` and `SampleableType.selectElem` occurrences in the values of the 1198 reachable `BeaconcryptCore` definitions, not samplers inside VCVio generics or `setup` fields; within that scope it finds no sampling at `MlKemSharedSecret`. The contamination scan, the guard-coverage scan, the guard-liveness file and the term grep were rerun on the review-fix tree and again on the tree merged with `f20cb4b0`, with the same results as before, and the closure check was run on both with identical output.
- Not run: no `lake build`, `make verify`, `nix-collect-garbage`, mutation testing, ProVerif or Rust run.

### Increment 2: review fixes

The semantic and hygiene reviews of `09ae745b` raised two minor findings and nine nits. The fixes change documentation, Lean module and declaration documentation and the receipt only; no Lean statement, proof or guard changed.

- Candidate freedom (minor): the S2 section, the checks, the analysis and the receipt now state the scope of the term grep (direct `uniformSample` and `SampleableType.selectElem` occurrences in `BeaconcryptCore` definition values, not samplers inside VCVio generics or `setup` fields), rest candidate freedom on `splitGame_root` and the absence of a candidate argument, and add the closure check as supporting evidence.
- First touch and slots (minor): the S1b consumer note, the services module documentation, plan section 20 and notes in CE-11 design v2 sections 5.7 and 6 now say that the Server slot's first touch is the selected accept's private root request (`resumeTail`), that S7 and CE-11 need a first-touch coordinate-to-slot layer in front of `PqxdhRecordLiftLazyTable`, and that `defer`, `oblivious` and `allowanceG` must be re-checked against an accept-time touch.
- `resume_lift_backend` (nit): the module documentation, its docstring and the S1b section now say that it only splits the resumption into prefix and tail under any pair of interpreters, and point to `resumeImpl_split` and `groupedResume_split`.
- Stage T (nit): "optional stage T would tighten" is now "stage T (plan section 17) tightens" in the root-count module and the S2 section.
- Titles (nit): the three S2 modules have title headings.
- Status, title and R1 wording (nits): this guide has one title for the topic, a current status line and the two increments as level-2 sections; the analysis and the plan paragraph above say that the HMAC-SHA-512 PRF is the standard game accepted by the owner, not part of R1.
- `resumeImplT` (nit): the services module documentation names `resumeImpl`.
- Commit label (nit): `f30da2f7` is labelled "S1b module documentation names".
- Stale intermediate digests (nit): no change; the three intermediate commits stay as they are (no history rewriting), and the inventory was recounted before it was rehashed, with `check-inventory.sh` last, at the merge and the fixes.
- Central moved (nit): central `62c5f4b7` is merged into the branch (`f14a8046`) with the section 6 hot-spot resolution (central's side first), followed by `inv recount`, `inv rehash` (`check-inventory.sh` last), the root import, the focused inventory check and the transcript-fidelity check. Central moved to `f20cb4b0` during the fixes and was merged the same way (`a6c50b30`); the receipt is re-issued for that tip. Central has since moved to `7045f0f6`; the integration step merges it.

### Increment 2: deviations from the plan

- S1b: the services skeleton is layered rather than one flattened handler. The plan's services `serverRoot`, `beaconRoot` and `table` are realized as the two oracles of the skeleton (hidden reads by coordinates, direct reads), and the section 18 services (`hiddenBuild`, `hiddenAfter`) as the record `Hidden` with exactly the required field types. The source's Beacon finish is grouped into one request for its root and its continuation, and the encapsulation-hiding wrapper of the resumed client is dropped by an equality. The prepared state handed to `hiddenAfter` has placeholders in the Server identity fields and the KEM field, which no service reads. The hidden Server value is first read at the resumption's private root request, not at the build (see the consumer note of S1b and CE-11 design v2 section 5.7); plan section 20 records the interface consequences for S7 and CE-11 (the accept as a first-touch class, a coordinate-to-slot layer in front of `PqxdhRecordLiftLazyTable`).
- S1c: the prefix "table-read log" of the plan is realized as a key-count potential of the table cache along the scan to the selected raw accept, which gives the covering set and the cut-split of `certified` directly. The residual counts every table read after the cut (hidden reads included) plus the Server's resumption; the bound is still the plan's coefficient-one term `(qAccept + qFinish + qHmac)/2^256`.
- S2: the `IsRoot` count goes through the skeleton's hidden reads (S1b restated the branch, so the pool, router, generated-finish compiler and CCA wrapper appear as the skeleton's layers); `KemOpaqueCosts.client_root` enters through S1c's `resume_root`. The finish budget of the continuation at the cut is obtained by inheritance (`scan_inherit`), without subtracting the finishes before the cut, which gives the plan's conservative `qRoot = 1 + qFinish`. The closure check and the definition-level term grep are scratch metaprograms, recorded here and in the receipt, not committed checks.
- The plan did not name the S2 statements; the built ones are `splitGame_root`, `splitGame_expanded`, `rootClient_root`, `rootClient_uniform`, `split_uniform` and `opaqueBranch_uniform`.
- No planned statement turned out false or unprovable, none was weakened, no assumption or contract was added and no existing module was changed.

### Increment 2: remaining stages and re-estimate

S1b, S1c and S2 (plan 17 to 31 agent-days, increment-1 re-estimate 9 to 18) were built in one working session. Remaining, in the order of plan section 17:

| Stage | Plan estimate | Re-estimate | Note |
| --- | --- | --- | --- |
| S3b entry factor | 6-10 | 2-5 | `uniformGame rootClient = rootHybrid source entryD`; `factorHidden` already instantiates the section 18 services; `uniformGame_first` |
| S4b T7 | 1-2 | 0.5-1 | `fromRoot_bound` |
| T (finish once) | 2-3 | 1-2 | `qRoot = 2` |
| S7 every entry | 2-3 | 1-3 | reuses Codex's `PqxdhRecordLiftLazyTable` behind a first-touch coordinate-to-slot layer (plan section 20) |
| S8 bills | 3-5 | 2-3 | |
| S5, S6 | 2.5-4 | 1-2 | |
| S9 | 5-8 | 2-4 | guide, assumption lists, review |

Remaining total: 9.5 to 20 agent-days, the sum of the rows above (plan: 21.5 to 35 for the same stages). The main risk is now S3b: equating the uniform-root world with the factored entry experiment needs the native and factored services to agree on the selected session and on every Beacon finish, under `-M8000`.

### Increment 2: not claimed

No item 2 headline (T7, T8) is stated yet. S1b is a program equality; S1c is a statistical bound valid only under the random-oracle model of the zero-key 192-byte Extract slice (R1); S2 is a computational bound whose PRF advantages are explicit terms. All three are for the opaque KEM-ideal branch of theorem T6 and take T5's source budget `certified` as their only premise. Not covered: persistence, snapshots, codec internals, running-code access and primitive implementations (owner scope).
