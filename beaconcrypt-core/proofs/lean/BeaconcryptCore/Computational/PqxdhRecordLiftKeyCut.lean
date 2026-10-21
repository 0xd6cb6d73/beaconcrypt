-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability
import BeaconcryptCore.Computational.PqxdhServerAuthEntrySimulation

/-!
# Record-lift selected-key law (items 4 and 5, stage S4, X2)

**Statement.** `key_cut_view`: for every mode assignment, every coordinate `target` and every adversary within its budget, the view of the CTX world `PqxdhRecordLiftIdeal.ctxRun modes` has the law of first sampling a uniform key and then running `PqxdhRecordLiftCtxLink.ctxRunWith (selectedKey target key) modes`, the CTX world whose `target` coordinate is keyed with the supplied key instead of its table entry's key bytes. `key_cut` and `key_cut_measure` restate it for every decision on the view, in the form of `PqxdhRecordLiftCtxLink.link`, in the deprecated `𝒮` and in the measure notation `𝒟`. The exported law is `key_cut_measure`, in `𝒟`, and it is the only form that `PqxdhRecordLiftCtx` uses. `miss_eager`, `table_eager`, `key_cut_view` and `key_cut` are internal bridges stated in the deprecated `𝒮` because the central lemmas they apply, `PqxdhServerAuthEntryFactor.eager_run` and `PqxdhRecordLiftProjectionCut.split_continuation`, are stated in `𝒮`; only these four theorems switch off the deprecation linter. Together with `link` this identifies both sides of every hybrid step with the one-key challenger's real and replay games; the law is needed on both sides because replay mode also seals with the key.

**Proof.** Three steps. (1) `table_eager`: by `PqxdhServerAuthEntryFactor.eager_run`, the CTX world has the law of sampling a uniform key up front and running `world`, which at the target's lookup miss stores the sampled output with its 32 key bytes replaced by the key (`keyStore`); at that miss the two samplings have the same law (`miss_eager`, from `PqxdhRecordLiftProjectionCut.split_continuation`), and no other request reads the key. Both worlds read every key from the table, so no availability premise is needed here. (2) `selected_table`: in the key-storing world, reading the target's key from the table or using the supplied key directly gives the same world, because every keyed request is at a present coordinate (`PqxdhRecordLiftCtxAvailability.program_map`) and a present target entry carries the supplied key (`KeyStored`, `world_preserve`). (3) `stored_view`: in a selected-key world nothing reads the target entry's key bytes (`chain_mask`, `nonce_mask`, `selectedKey_mask`, `hiddenOpening_mask`, `hiddenSealing_mask`), so masking them (`maskState`) is a simulation of every service (`world_mask`) and the stored key bytes do not affect the client result or the produced frames.

**Scope.** No theorem of this module has an assumption or contract hypothesis or uses a contract: no proof uses a field of the primitive record or a security game (fields reached only inside definitions, such as those of the setup's DH interface, are structural). This module leaves the hop bounds and the assembly of `CtxAuthLiftStatement` to `PqxdhRecordLiftCtx` and `PqxdhRecordLiftCtxBills`; see `doc/impl/record-lift-ctx-hybrid.md`. New Claude work; nothing adapted from Codex WIP.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftCtxHybrid PqxdhRecordLiftCtxLink
open PqxdhRecordLiftCtxAvailability
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable PqxdhRecordLiftMaterialTable
open PqxdhFullSecretInputKdf (FullOutput)
open PqxdhSecretInputKdf (RootOutput)
open CtxRomAuth AdaptiveCtxReceive
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

/-! ### Lookups of the CTX world -/

/-- The primitive state after a lookup miss: one native KDF call and 76 uniform bytes charged. -/
def missPrimitive (primitive : PqxdhRecordLiftWorld.Primitive) : PqxdhRecordLiftWorld.Primitive :=
  ({ (PqxdhRecordLiftChainOracle.charge primitive).1 with uniform := primitive.1.uniform + 76 }, primitive.2)

/-- The chain-world state after a lookup miss at `coordinate` that stores `output`. -/
def missBase (coordinate : Label n) (base : PqxdhRecordLiftProtocol.Private n) (output : FullOutput) :
    PqxdhRecordLiftProtocol.Private n :=
  { base with chain := base.chain.cacheQuery coordinate output, primitive := missPrimitive base.primitive }

/-- The CTX state after a lookup miss at `coordinate` that stores `output`. -/
def missState (coordinate : Label n) (state : CtxPrivate n) (output : FullOutput) : CtxPrivate n :=
  { state with base := missBase coordinate state.base output }

/-- The CTX state after a lookup hit: one native KDF call charged. -/
def hitState (state : CtxPrivate n) : CtxPrivate n :=
  { state with base := { state.base with primitive := PqxdhRecordLiftChainOracle.charge state.base.primitive } }

/-- A CTX-world lookup miss samples a full 76-byte output and stores it. -/
theorem lookup_miss (keyed : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp))
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (coordinate : Label n) (state : CtxPrivate n)
    (missing : state.base.chain coordinate = none) :
    (ctxInterpreterOf keyed replace setup codec (.lookup coordinate)).run state =
      (fun output => ((), missState coordinate state output)) <$> ($ᵗ FullOutput) := by
  rw [show ctxInterpreterOf keyed replace setup codec (.lookup coordinate) =
    ctxInterpreterWith tableKey (fun _ => .real) replace setup codec (.lookup coordinate) from rfl, lookup_factor]
  rw [PqxdhRecordLiftChainOracle.lookup_miss _ _ _ _ _ rfl missing, Functor.map_map]
  rfl

/-- A CTX-world lookup hit charges one native KDF call and changes nothing else. -/
theorem lookup_hit (keyed : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp))
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (coordinate : Label n) (state : CtxPrivate n)
    (output : FullOutput) (found : state.base.chain coordinate = some output) :
    (ctxInterpreterOf keyed replace setup codec (.lookup coordinate)).run state = pure ((), hitState state) := by
  rw [show ctxInterpreterOf keyed replace setup codec (.lookup coordinate) =
    ctxInterpreterWith tableKey (fun _ => .real) replace setup codec (.lookup coordinate) from rfl, lookup_factor]
  rw [PqxdhRecordLiftChainOracle.lookup_hit _ _ _ _ _ rfl output found, map_pure]
  rfl

/-! ### The target lookup with a stored-output transformation -/

/-- The CTX world whose lookup of `target`, on a miss, stores `store output` instead of the sampled `output`; every other request is `ctxInterpreterOf keyed`'s. -/
noncomputable def world (keyed : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp))
    (store : FullOutput → FullOutput) (target : Label n) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (CtxPrivate n) ProbComp)
  | .lookup coordinate => fun state =>
      if coordinate = target ∧ state.base.chain target = none then
        (fun output => ((), missState target state (store output))) <$> ($ᵗ FullOutput)
      else (ctxInterpreterOf keyed replace setup codec (.lookup coordinate)).run state
  | query => ctxInterpreterOf keyed replace setup codec query

/-- Storing the sampled output itself is the CTX world. -/
theorem world_id (keyed : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp)) (target : Label n)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (query : PqxdhRecordLiftProtocol.Service n)
    (state : CtxPrivate n) :
    (world keyed id target replace setup codec query).run state =
      (ctxInterpreterOf keyed replace setup codec query).run state := by
  cases query with
  | lookup coordinate =>
      change (if coordinate = target ∧ state.base.chain target = none then
        (fun output => ((), missState target state (id output))) <$> ($ᵗ FullOutput)
        else (ctxInterpreterOf keyed replace setup codec (.lookup coordinate)).run state) = _
      split
      · rename_i selected
        obtain ⟨rfl, missing⟩ := selected
        rw [lookup_miss keyed replace setup codec coordinate state missing]
        rfl
      · rfl
  | _ => rfl

/-- Away from a missing target lookup, the world is the CTX world. -/
theorem world_other (keyed : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp)) (store : FullOutput → FullOutput)
    (target : Label n) (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (query : PqxdhRecordLiftProtocol.Service n)
    (state : CtxPrivate n) (other : ¬(query = .lookup target ∧ state.base.chain target = none)) :
    (world keyed store target replace setup codec query).run state =
      (ctxInterpreterOf keyed replace setup codec query).run state := by
  cases query with
  | lookup coordinate =>
      change (if coordinate = target ∧ state.base.chain target = none then
        (fun output => ((), missState target state (store output))) <$> ($ᵗ FullOutput)
        else (ctxInterpreterOf keyed replace setup codec (.lookup coordinate)).run state) = _
      rw [ite_eq_right (by rintro ⟨rfl, missing⟩; exact other ⟨rfl, missing⟩)]
  | _ => rfl

/-- At a missing target, the world's lookup samples and stores the transformed output. -/
theorem world_miss (keyed : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp)) (store : FullOutput → FullOutput)
    (target : Label n) (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (state : CtxPrivate n)
    (missing : state.base.chain target = none) :
    (world keyed store target replace setup codec (.lookup target)).run state =
      (fun output => ((), missState target state (store output))) <$> ($ᵗ FullOutput) := by
  change (if target = target ∧ state.base.chain target = none then
    (fun output => ((), missState target state (store output))) <$> ($ᵗ FullOutput)
    else (ctxInterpreterOf keyed replace setup codec (.lookup target)).run state) = _
  rw [ite_eq_left ⟨rfl, missing⟩]

/-! ### Sampling the target's key up front -/

open PqxdhRecordLiftProjectionCut (Retained restore retained secret restore_split split_restore split_continuation)

/-- A sampled output with its 32 key bytes replaced by `key`; its nonce and next-chain bytes are kept. -/
noncomputable def keyStore (key : RootOutput) (output : FullOutput) : FullOutput :=
  restore .key (retained .key output) key

set_option linter.deprecated false in
/-- Storing a uniform output, or a uniform output whose key bytes are replaced by an independent uniform key sampled before it, has the same law under every continuation. -/
theorem miss_eager {Result : Type} (continuation : FullOutput → Result) :
    𝒮[continuation <$> ($ᵗ FullOutput)] =
      𝒮[do let key ← $ᵗ RootOutput; (fun output => continuation (keyStore key output)) <$> ($ᵗ FullOutput)] := by
  have swap := evalSPMF_bind_bind_swap ($ᵗ RootOutput) ($ᵗ FullOutput)
    (fun key output => (pure (continuation (keyStore key output)) : ProbComp Result))
  have first := split_continuation (X := Result) .key
    (fun value _ => do let key ← $ᵗ RootOutput; pure (continuation (restore .key value key)))
  have drop : ∀ value : Retained,
      𝒮[(do let _ ← $ᵗ RootOutput
            let key ← $ᵗ RootOutput
            pure (continuation (restore .key value key)) : ProbComp Result)] =
        𝒮[(do let key ← $ᵗ RootOutput; pure (continuation (restore .key value key)) : ProbComp Result)] :=
    fun value => DeferredSampling.evalSPMF_bind_const_neverFails _ probFailure_eq_zero _
  have second := split_continuation (X := Result) .key (fun value key => pure (continuation (restore .key value key)))
  simp only [restore_split] at second
  simp only [map_eq_bind_pure_comp, Function.comp_def] at swap ⊢
  rw [swap]
  simp only [keyStore]
  rw [first, second, evalSPMF_bind ($ᵗ Retained), evalSPMF_bind ($ᵗ Retained)]
  exact congrArg _ (funext fun value => (drop value).symm)


set_option linter.deprecated false in
/-- **Eager target key.** For every mode assignment and every program, the CTX world has the law of first sampling a uniform key and then running the world that stores that key in the target's entry at its lookup miss. Both read every key from the table. -/
theorem table_eager (modes : Label n → KeyMode) (target : Label n) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    {Result : Type} (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result) (state : CtxPrivate n) :
    𝒮[(simulateQ (ctxInterpreterWith tableKey modes replace setup codec) client).run state] =
      𝒮[do
        let key ← $ᵗ RootOutput
        (simulateQ (world (keyedWith tableKey modes (RawCtxUniversalDecoder.decoder codec.frameRead)
          setup.source.crypto) (keyStore key) target replace setup codec) client).run state] := by
  rw [ctxInterpreterWith_of]
  apply PqxdhServerAuthEntryFactor.eager_run_vcvioLegacy ($ᵗ RootOutput) _ _ (fun state => Present state.base.chain target)
  · intro query state present
    refine ⟨fun key => world_other _ _ target replace setup codec query state
      (fun ⟨_, missing⟩ => by obtain ⟨output, found⟩ := present; rw [found] at missing; cases missing), ?_⟩
    intro result supported
    obtain ⟨output, found⟩ := present
    exact ⟨output, (chain_step _ (keyedWith_chain tableKey modes _ _) replace setup codec query state result
      supported).1 found⟩
  · intro query state absent
    have missing : state.base.chain target = none := by
      cases found : state.base.chain target with
      | none => rfl
      | some output => exact absurd ⟨output, found⟩ absent
    by_cases selected : query = .lookup target
    · subst selected
      right
      refine ⟨?_, fun key result supported => ?_⟩
      · rw [lookup_miss _ replace setup codec target state missing]
        simp only [world_miss _ _ target replace setup codec state missing]
        exact miss_eager (fun output => ((), missState target state output))
      · rw [world_miss _ _ target replace setup codec state missing, support_map] at supported
        obtain ⟨output, _, rfl⟩ := supported
        exact ⟨_, QueryCache.cacheQuery_self (state.base.chain : Table (Slot n)) target _⟩
    · left
      exact fun key => world_other _ _ target replace setup codec query state (fun ⟨same, _⟩ => selected same)

/-! ### Masking the target's key bytes -/

/-- The all-zero 32-byte key. -/
def zeroKey : RootOutput := ⟨List.replicate 32 0, by simp⟩

/-- A table output with its key bytes zeroed. -/
noncomputable def maskStore (output : FullOutput) : FullOutput := keyStore zeroKey output

/-- The table with the key bytes of the target's entry zeroed. -/
noncomputable def maskAt (target : Label n) (table : Table (Slot n)) : Table (Slot n) := fun label =>
  if label = target then (table label).map maskStore else table label

/-- The CTX state with the key bytes of the target's entry zeroed. -/
noncomputable def maskState (target : Label n) (state : CtxPrivate n) : CtxPrivate n :=
  { state with base := { state.base with chain := maskAt target state.base.chain } }

theorem base_mask (keyed : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp)) (target : Label n)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (query : PqxdhRecordLiftProtocol.Service n)
    (notLookup : ∀ coordinate, query ≠ .lookup coordinate) (notOpening : ∀ pending, query ≠ .opening pending)
    (notSealing : ∀ pending, query ≠ .sealing pending) (state : CtxPrivate n) :
    Prod.map id (maskState target) <$> (ctxInterpreterOf keyed replace setup codec query).run state =
      (ctxInterpreterOf keyed replace setup codec query).run (maskState target state) := by
  cases query with
  | lookup coordinate => exact absurd rfl (notLookup coordinate)
  | opening pending => exact absurd rfl (notOpening pending)
  | sealing pending => exact absurd rfl (notSealing pending)
  | _ =>
    simp only [ctxInterpreterOf, onBase, PqxdhRecordLiftProtocol.interpreter, PqxdhRecordLiftProtocol.sampled,
      PqxdhRecordLiftProtocol.withRecord, PqxdhRecordLiftProtocol.primitiveWork, PqxdhRecordLiftProtocol.putRecord,
      PqxdhRecordLiftProtocol.recordState, PqxdhRecordLiftProtocol.publish, StateT.run, bind_pure_comp,
      Functor.map_map, map_pure, maskState]
    all_goals rfl

theorem keyStore_material (key : RootOutput) (output : FullOutput) :
    (PqxdhOrderedChainHybrids.material (keyStore key output)).1 = key ∧
      (PqxdhOrderedChainHybrids.material (keyStore key output)).2 = (PqxdhOrderedChainHybrids.material output).2 ∧
      PqxdhOrderedChainHybrids.nextChain (keyStore key output) = PqxdhOrderedChainHybrids.nextChain output := by
  have restored := split_restore .key (retained .key output) key
  simp only [Prod.mk.injEq] at restored
  refine ⟨restored.2, ?_, ?_⟩
  · change (retained .key (keyStore key output)).2 = (retained .key output).2
    rw [keyStore, restored.1]
  · change (retained .key (keyStore key output)).1 = (retained .key output).1
    rw [keyStore, restored.1]

/-- Masking keeps the chain read from every table position. -/
theorem chain_mask (target : Label n) (seeds : Seeds (Slot n)) (table : Table (Slot n)) :
    chain seeds (maskAt target table) = chain seeds table := by
  funext coordinate
  have entry : maskAt target table (previous coordinate) = (table (previous coordinate)).map maskStore ∨
      maskAt target table (previous coordinate) = table (previous coordinate) := by
    unfold maskAt
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  unfold chain
  rcases entry with masked | kept
  · rw [masked]
    cases found : table (previous coordinate) with
    | none => rfl
    | some output =>
        simp only [Option.map_some]
        rw [maskStore, (keyStore_material zeroKey output).2.2]
  · rw [kept]

/-- Masking keeps every coordinate's nonce. -/
theorem nonce_mask (target : Label n) (table : Table (Slot n)) (label : Label n) :
    (materialAt (maskAt target table) label).2 = (materialAt table label).2 := by
  unfold materialAt maskAt
  split
  · cases table label with
    | none => rfl
    | some output => exact (keyStore_material zeroKey output).2.1
  · rfl

/-- Masking keeps every key other than the target's. -/
theorem key_mask (target : Label n) (table : Table (Slot n)) (label : Label n) (different : label ≠ target) :
    materialAt (maskAt target table) label = materialAt table label := by
  unfold materialAt maskAt
  rw [ite_eq_right different]

/-- The selected key never reads the masked bytes. -/
theorem selectedKey_mask (target : Label n) (key : CtxKey) (table : Table (Slot n)) (label : Label n) :
    selectedKey target key (maskAt target table) label = selectedKey target key table label := by
  unfold selectedKey
  split
  · rfl
  · rename_i different
    rw [key_mask target table label different]

theorem hiddenOpening_mask (target : Label n) (seeds : Seeds (Slot n)) (table : Table (Slot n))
    (pending : PqxdhRecordLiftProtocol.Opening n) :
    hiddenOpening seeds (maskAt target table) pending = hiddenOpening seeds table pending := by
  unfold hiddenOpening
  rw [chain_mask]
  split
  · rfl
  · split
    · rfl
    · split
      · rw [nonce_mask]
      · rfl

theorem hiddenSealing_mask (target : Label n) (writer : RawCtxMixedShared.Writer) (table : Table (Slot n))
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (pending : PqxdhRecordLiftProtocol.Sealing n) :
    hiddenSealing writer (maskAt target table) replace pending = hiddenSealing writer table replace pending := by
  have nonce := nonce_mask target table pending.material
  unfold hiddenSealing
  generalize (materialAt (maskAt target table) pending.material).2 = masked at nonce ⊢
  subst nonce
  funext frames
  split
  · refine congrArg (fun continuation => _ >>= continuation) (funext fun reply => ?_)
    cases reply <;> rfl
  · rfl

/-- An explicit-key request whose key function never reads the masked bytes commutes with masking. -/
theorem keyedWith_mask (keyOf : KeyOf n) (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (target : Label n) (insensitive : ∀ table label, keyOf (maskAt target table) label = keyOf table label)
    (query : (KeyedSpec n).Domain) (state : CtxPrivate n) :
    Prod.map id (maskState target) <$> (keyedWith keyOf modes decode crypto query).run state =
      (keyedWith keyOf modes decode crypto query).run (maskState target state) := by
  simp only [keyedWith, StateT.run, PqxdhRecordLiftProtocol.sampled, maskState, insensitive, bind_pure_comp,
    Functor.map_map]
  rfl

/-- A keyed program commutes with masking when its keyed implementation does. -/
theorem simulate_mask (keyed : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp)) (target : Label n)
    (keyedMask : ∀ query state, Prod.map id (maskState target) <$> (keyed query).run state =
      (keyed query).run (maskState target state))
    {Result : Type} (client : OracleComp (KeyedSpec n) Result) (state : CtxPrivate n) :
    Prod.map id (maskState target) <$> (simulateQ keyed client).run state =
      (simulateQ keyed client).run (maskState target state) :=
  map_run_simulateQ_eq_of_query_map_eq keyed keyed (maskState target) keyedMask client state

theorem opening_mask (keyed : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp)) (target : Label n)
    (keyedMask : ∀ query state, Prod.map id (maskState target) <$> (keyed query).run state =
      (keyed query).run (maskState target state))
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (pending : PqxdhRecordLiftProtocol.Opening n)
    (state : CtxPrivate n) :
    Prod.map id (maskState target) <$> (ctxInterpreterOf keyed replace setup codec (.opening pending)).run state =
      (ctxInterpreterOf keyed replace setup codec (.opening pending)).run (maskState target state) := by
  change Prod.map id (maskState target) <$> (simulateQ keyed (hiddenOpening
      (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain pending)).run state =
    (simulateQ keyed (hiddenOpening (PqxdhRecordLiftProtocol.cachedSeeds state.base)
      (maskAt target state.base.chain) pending)).run (maskState target state)
  rw [hiddenOpening_mask]
  exact simulate_mask keyed target keyedMask _ state

theorem sealing_mask (keyed : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp)) (target : Label n)
    (keyedMask : ∀ query state, Prod.map id (maskState target) <$> (keyed query).run state =
      (keyed query).run (maskState target state))
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (pending : PqxdhRecordLiftProtocol.Sealing n)
    (state : CtxPrivate n) :
    Prod.map id (maskState target) <$> (ctxInterpreterOf keyed replace setup codec (.sealing pending)).run state =
      (ctxInterpreterOf keyed replace setup codec (.sealing pending)).run (maskState target state) := by
  change Prod.map id (maskState target) <$> (do
      let result ← (simulateQ keyed ((hiddenSealing codec.frameWrite state.base.chain replace pending).run
        state.base.pending)).run state
      pure (result.1.1, { result.2 with base := { result.2.base with pending := result.1.2 } })) = (do
      let result ← (simulateQ keyed ((hiddenSealing codec.frameWrite (maskAt target state.base.chain) replace
        pending).run state.base.pending)).run (maskState target state)
      pure (result.1.1, { result.2 with base := { result.2.base with pending := result.1.2 } }))
  rw [hiddenSealing_mask, ← simulate_mask keyed target keyedMask _ state]
  simp only [map_bind, bind_map_left, map_pure]
  rfl

theorem mask_miss_self (target : Label n) (state : CtxPrivate n) (output : FullOutput) :
    maskState target (missState target state output) = missState target (maskState target state) (maskStore output) := by
  have chainEq : maskAt target (state.base.chain.cacheQuery target output) =
      (maskAt target state.base.chain).cacheQuery target (maskStore output) := by
    funext label
    unfold maskAt
    by_cases same : label = target
    · subst same
      simp [QueryCache.cacheQuery_self]
    · simp [same]
  simp only [maskState, missState, missBase, chainEq]

theorem mask_miss_other (target coordinate : Label n) (different : coordinate ≠ target) (state : CtxPrivate n)
    (output : FullOutput) :
    maskState target (missState coordinate state output) = missState coordinate (maskState target state) output := by
  have chainEq : maskAt target (state.base.chain.cacheQuery coordinate output) =
      (maskAt target state.base.chain).cacheQuery coordinate output := by
    funext label
    unfold maskAt
    by_cases same : label = coordinate
    · subst same
      simp [QueryCache.cacheQuery_self, different]
    · rw [QueryCache.cacheQuery_of_ne _ _ same, QueryCache.cacheQuery_of_ne _ _ same]
  simp only [maskState, missState, missBase, chainEq]

theorem maskAt_none (target : Label n) (table : Table (Slot n)) :
    maskAt target table target = none ↔ table target = none := by
  simp [maskAt]

/-- The target-lookup world commutes with masking, the stored outputs being masked too. -/
theorem world_mask (keyed : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp)) (store : FullOutput → FullOutput)
    (target : Label n)
    (keyedMask : ∀ query state, Prod.map id (maskState target) <$> (keyed query).run state =
      (keyed query).run (maskState target state))
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (query : PqxdhRecordLiftProtocol.Service n)
    (state : CtxPrivate n) :
    Prod.map id (maskState target) <$> (world keyed store target replace setup codec query).run state =
      (world keyed (fun output => maskStore (store output)) target replace setup codec query).run
        (maskState target state) := by
  cases query with
  | lookup coordinate =>
      by_cases selected : coordinate = target ∧ state.base.chain target = none
      · obtain ⟨rfl, missing⟩ := selected
        rw [world_miss _ _ _ replace setup codec state missing,
          world_miss _ _ _ replace setup codec _ ((maskAt_none _ _).mpr missing), Functor.map_map]
        simp only [Prod.map, id, mask_miss_self]
      · have masked : ¬(coordinate = target ∧ (maskState target state).base.chain target = none) :=
          fun ⟨same, missing⟩ => selected ⟨same, (maskAt_none _ _).mp missing⟩
        rw [world_other _ _ _ replace setup codec _ state (fun ⟨same, missing⟩ => selected ⟨by cases same; rfl, missing⟩),
          world_other _ _ _ replace setup codec _ _ (fun ⟨same, missing⟩ => masked ⟨by cases same; rfl, missing⟩)]
        cases found : state.base.chain coordinate with
        | some output =>
            have maskedFound : (maskState target state).base.chain coordinate =
                some (if coordinate = target then maskStore output else output) := by
              change maskAt target state.base.chain coordinate = _
              unfold maskAt
              split <;> simp [found]
            rw [lookup_hit _ replace setup codec coordinate state output found,
              lookup_hit _ replace setup codec coordinate _ _ maskedFound, map_pure]
            rfl
        | none =>
            have different : coordinate ≠ target := fun same => selected ⟨same, same ▸ found⟩
            have maskedMissing : (maskState target state).base.chain coordinate = none := by
              change maskAt target state.base.chain coordinate = none
              unfold maskAt
              rw [ite_eq_right different, found]
            rw [lookup_miss _ replace setup codec coordinate state found,
              lookup_miss _ replace setup codec coordinate _ maskedMissing, Functor.map_map]
            simp only [Prod.map, id, mask_miss_other target coordinate different]
  | opening pending => exact opening_mask keyed target keyedMask replace setup codec pending state
  | sealing pending => exact sealing_mask keyed target keyedMask replace setup codec pending state
  | _ =>
      apply base_mask keyed target replace setup codec
      all_goals intro _ h; cases h

/-! ### The supplied key read from the table -/

/-- A CTX-world service changes no table entry other than its own lookup coordinate. -/
theorem chain_frame (keyed : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp))
    (keep : ∀ query state, ∀ result ∈ support ((keyed query).run state), result.2.base.chain = state.base.chain)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (query : PqxdhRecordLiftProtocol.Service n)
    (state : CtxPrivate n) (result : (PqxdhRecordLiftProtocol.ServiceSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreterOf keyed replace setup codec query).run state))
    (label : Label n) (other : label ∉ lookupCoordinates query) :
    result.2.base.chain label = state.base.chain label := by
  cases query with
  | lookup coordinate =>
      have different : label ≠ coordinate := fun same => other (by simp [lookupCoordinates, same])
      cases found : state.base.chain coordinate with
      | some output =>
          rw [lookup_hit _ replace setup codec coordinate state output found, support_pure,
            Set.mem_singleton_iff] at supported
          subst result
          rfl
      | none =>
          rw [lookup_miss _ replace setup codec coordinate state found, support_map] at supported
          obtain ⟨output, _, rfl⟩ := supported
          exact QueryCache.cacheQuery_of_ne _ _ different
  | opening pending => rw [simulate_chain keyed keep _ state result supported]
  | sealing pending =>
      simp only [ctxInterpreterOf, StateT.run, bind_pure_comp, support_map, Set.mem_image] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      change inner.2.base.chain label = _
      rw [simulate_chain keyed keep _ state inner member]
  | _ =>
    simp only [ctxInterpreterOf, onBase, PqxdhRecordLiftProtocol.interpreter, PqxdhRecordLiftProtocol.sampled,
      PqxdhRecordLiftProtocol.withRecord, PqxdhRecordLiftProtocol.primitiveWork, PqxdhRecordLiftProtocol.putRecord,
      PqxdhRecordLiftProtocol.recordState, PqxdhRecordLiftProtocol.publish, StateT.run, bind_pure_comp, support_map,
      Set.mem_image, Functor.map_map, support_pure, Set.mem_singleton_iff] at supported
    first
      | obtain ⟨_, rfl, rfl⟩ := supported
      | obtain ⟨_, _, rfl⟩ := supported
    rfl

/-- The table stores the supplied key at the target, once present. -/
def KeyStored (target : Label n) (key : RootOutput) (state : CtxPrivate n) : Prop :=
  ∀ output, state.base.chain target = some output → secret .key output = key

/-- Every service of the key-storing world grows the table, makes its lookup present and keeps the stored key. -/
theorem world_preserve (keyed : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp))
    (keep : ∀ query state, ∀ result ∈ support ((keyed query).run state), result.2.base.chain = state.base.chain)
    (target : Label n) (key : RootOutput) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : PqxdhRecordLiftProtocol.Service n) (state : CtxPrivate n) (stored : KeyStored target key state)
    (result : (PqxdhRecordLiftProtocol.ServiceSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((world keyed (keyStore key) target replace setup codec query).run state)) :
    KeyStored target key result.2 ∧ state.base.chain ≤ result.2.base.chain ∧
      ∀ label ∈ lookupCoordinates query, Present result.2.base.chain label := by
  by_cases selected : query = .lookup target ∧ state.base.chain target = none
  · obtain ⟨rfl, missing⟩ := selected
    rw [world_miss _ _ target replace setup codec state missing, support_map] at supported
    obtain ⟨output, _, rfl⟩ := supported
    refine ⟨fun found present => ?_, fun label value found => ?_, fun label member => ?_⟩
    · change (state.base.chain.cacheQuery target (keyStore key output)) target = some found at present
      rw [QueryCache.cacheQuery_self] at present
      cases present
      exact (keyStore_material key output).1
    · have different : label ≠ target := by
        rintro rfl
        rw [missing] at found
        cases found
      exact (QueryCache.cacheQuery_of_ne _ _ different).trans found
    · simp only [lookupCoordinates, List.mem_singleton] at member
      rw [member]
      exact ⟨_, QueryCache.cacheQuery_self (state.base.chain : Table (Slot n)) target _⟩
  · rw [world_other _ _ target replace setup codec query state selected] at supported
    have grown := chain_step keyed keep replace setup codec query state result supported
    refine ⟨fun found present => ?_, grown.1, grown.2⟩
    by_cases looked : target ∈ lookupCoordinates query
    · cases old : state.base.chain target with
      | none =>
          exfalso
          cases query <;> simp [lookupCoordinates] at looked
          exact selected ⟨by rw [looked], old⟩
      | some value =>
          have same : some found = some value := present.symm.trans (grown.1 old)
          cases same
          exact stored _ old
    · rw [chain_frame keyed keep replace setup codec query state result supported target looked] at present
      exact stored found present

/-- The initial table is empty. -/
theorem initial_chain (label : Label n) : (CtxPrivate.initial : CtxPrivate n).base.chain label = none := rfl

theorem initial_stored (target : Label n) (key : RootOutput) : KeyStored target key (CtxPrivate.initial : CtxPrivate n) :=
  fun output found => by rw [initial_chain] at found; cases found

/-- With the supplied key stored, the table key and the selected key agree at every present coordinate. -/
theorem tableKey_selected (target : Label n) (key : RootOutput) (state : CtxPrivate n)
    (stored : KeyStored target key state) (label : Label n) (present : Present state.base.chain label) :
    tableKey state.base.chain label = selectedKey target key state.base.chain label := by
  unfold selectedKey
  split
  · rename_i same
    subst same
    obtain ⟨output, found⟩ := present
    unfold tableKey materialAt
    rw [found]
    exact stored output found
  · rfl

/-- With the supplied key stored, the table-key and selected-key worlds agree on every request touching only present coordinates. -/
theorem world_selected_step (modes : Label n → KeyMode) (target : Label n) (key : RootOutput)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (positions : Nat)
    (query : PqxdhRecordLiftProtocol.Service n) (state : CtxPrivate n) (stored : KeyStored target key state)
    (touches : Touches positions state.base.chain query) :
    (world (keyedWith tableKey modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
      (keyStore key) target replace setup codec query).run state =
    (world (keyedWith (selectedKey target key) modes (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto) (keyStore key) target replace setup codec query).run state := by
  cases query with
  | lookup coordinate => simp only [world, ctxInterpreterOf]
  | opening pending =>
      rw [world_other _ _ _ _ _ _ _ _ (fun selected => by cases selected.1),
        world_other _ _ _ _ _ _ _ _ (fun selected => by cases selected.1)]
      exact opening_congr _ _ replace setup codec pending state (fun label selected request =>
        keyedWith_congr _ _ _ _ _ _ _ state (tableKey_selected target key state stored label (touches label selected).1)
          rfl)
  | sealing pending =>
      rw [world_other _ _ _ _ _ _ _ _ (fun selected => by cases selected.1),
        world_other _ _ _ _ _ _ _ _ (fun selected => by cases selected.1)]
      exact sealing_congr _ _ replace setup codec pending state (fun request =>
        keyedWith_congr _ _ _ _ _ _ _ state (tableKey_selected target key state stored _ touches.1) rfl)
  | _ => simp only [world, ctxInterpreterOf]

/-- **The supplied key read from the table.** For every adversary within its budget, the world that stores the supplied key in the target's entry and reads every key from the table is the world that stores it and keys the target with the supplied key directly. -/
theorem selected_table (modes : Label n → KeyMode) (target : Label n) (key : RootOutput)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (budget : PqxdhDeploymentInterface.Budget) (respects : budget.Respects adversary) :
    (simulateQ (world (keyedWith tableKey modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
      (keyStore key) target replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
        CtxPrivate.initial =
    (simulateQ (world (keyedWith (selectedKey target key) modes (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto) (keyStore key) target replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
        CtxPrivate.initial := by
  have mapped := program_map budget _ _ id (fun state : CtxPrivate n => state.base.chain) (KeyStored target key)
    (fun query state stored touches => by
      rw [Prod.map_id, id_map]
      exact world_selected_step modes target key replace setup codec _ query state stored touches)
    (fun query state stored result supported => world_preserve _ (keyedWith_chain tableKey modes _ _) target key
      replace setup codec query state stored result supported)
    env setup.source.crypto codec route serverKid bounds mode adversary respects CtxPrivate.initial
    (initial_stored target key)
  rwa [Prod.map_id, id_map] at mapped

/-! ### The selected-key law -/

/-- Masking forgets the supplied key. -/
theorem keyStore_mask (key : RootOutput) : (fun output => maskStore (keyStore key output)) = maskStore := by
  funext output
  unfold maskStore keyStore
  have restored := congrArg Prod.fst (split_restore .key (retained .key output) key)
  simp only at restored
  rw [restored]

/-- Masking an absent target changes nothing. -/
theorem mask_absent (target : Label n) (state : CtxPrivate n) (missing : state.base.chain target = none) :
    maskState target state = state := by
  have chainEq : maskAt target state.base.chain = state.base.chain := by
    funext label
    unfold maskAt
    split
    · rename_i same
      rw [same, missing]
      rfl
    · rfl
  simp only [maskState, chainEq]

/-- The world storing every sampled output itself is the CTX world. -/
theorem world_id_impl (keyed : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp)) (target : Label n)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    world keyed id target replace setup codec = ctxInterpreterOf keyed replace setup codec := by
  funext query
  exact StateT.ext (world_id keyed target replace setup codec query)

/-- The selected-key keyed implementation commutes with masking. -/
theorem selected_keyedMask (modes : Label n → KeyMode) (target : Label n) (key : CtxKey) (decode : RawDecoder)
    (crypto : Pqxdh.Crypto) (query : (KeyedSpec n).Domain) (state : CtxPrivate n) :
    Prod.map id (maskState target) <$> (keyedWith (selectedKey target key) modes decode crypto query).run state =
      (keyedWith (selectedKey target key) modes decode crypto query).run (maskState target state) :=
  keyedWith_mask _ modes decode crypto target (selectedKey_mask target key) query state

/-- For a fixed supplied key, storing it in the target's entry changes no view of the selected-key world. -/
theorem stored_view (modes : Label n → KeyMode) (target : Label n) (key : RootOutput)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) {Result : Type}
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result) :
    (fun result => (result.1, result.2.base.produced)) <$> (simulateQ (world (keyedWith (selectedKey target key) modes
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto) (keyStore key) target replace setup codec)
        client).run CtxPrivate.initial =
    (fun result => (result.1, result.2.base.produced)) <$> (simulateQ (ctxInterpreterWith (selectedKey target key) modes
      replace setup codec) client).run CtxPrivate.initial := by
  have keyedMask := selected_keyedMask modes target key (RawCtxUniversalDecoder.decoder codec.frameRead)
    setup.source.crypto
  have masked := map_run_simulateQ_eq_of_query_map_eq _
    (world (keyedWith (selectedKey target key) modes (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto) maskStore target replace setup codec) (maskState target)
    (fun query state => by
      have step := world_mask _ (keyStore key) target keyedMask replace setup codec query state
      rwa [keyStore_mask] at step) client CtxPrivate.initial
  have plain := map_run_simulateQ_eq_of_query_map_eq _
    (world (keyedWith (selectedKey target key) modes (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto) maskStore target replace setup codec) (maskState target)
    (fun query state => world_mask _ id target keyedMask replace setup codec query state) client CtxPrivate.initial
  rw [mask_absent target _ (initial_chain target)] at masked plain
  rw [ctxInterpreterWith_of, ← world_id_impl _ target]
  have viewMasked := congrArg (fun program => (fun result => (result.1, result.2.base.produced)) <$> program) masked
  have viewPlain := congrArg (fun program => (fun result => (result.1, result.2.base.produced)) <$> program) plain
  simp only [Functor.map_map] at viewMasked viewPlain
  exact viewMasked.trans viewPlain.symm

/-- A CTX-world view depends only on the client result and the produced frames. -/
theorem ctxView_map (program : ProbComp (Client n E X × CtxPrivate n)) :
    ctxView <$> program = (fun result => viewOf result.1 result.2) <$>
      ((fun result => (result.1, result.2.base.produced)) <$> program) := by
  rw [Functor.map_map]
  rfl

set_option linter.deprecated false in
/-- **The selected-key law.** For every mode assignment, coordinate and adversary within its budget, the CTX world's view has the law of first sampling a uniform key and running the CTX world whose `target` coordinate is keyed with it (`PqxdhRecordLiftCtxLink.selectedKey`). -/
theorem key_cut_view (modes : Label n → KeyMode) (target : Label n) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (budget : PqxdhDeploymentInterface.Budget) (respects : budget.Respects adversary) :
    𝒮[ctxView <$> ctxRun modes replace setup codec route env serverKid bounds mode adversary] =
      𝒮[do
        let key ← $ᵗ CtxKey
        ctxView <$> ctxRunWith (selectedKey target key) modes replace setup codec route env serverKid bounds mode
          adversary] := by
  have eager := table_eager modes target replace setup codec
    (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
    CtxPrivate.initial
  have perKey : ∀ key : CtxKey, ctxView <$> (simulateQ (world (keyedWith tableKey modes
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto) (keyStore key) target replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
        CtxPrivate.initial =
      ctxView <$> ctxRunWith (selectedKey target key) modes replace setup codec route env serverKid bounds mode
        adversary := by
    intro key
    rw [selected_table modes target key replace setup codec route env serverKid bounds mode adversary budget respects,
      ctxView_map, stored_view, ← ctxView_map]
    rfl
  rw [← ctxRunWith_tableKey, ctxRunWith, evalSPMF_map, eager, ← evalSPMF_map, map_bind]
  simp only [perKey]

set_option linter.deprecated false in
/-- The selected-key law for every decision on the view, in the form of `PqxdhRecordLiftCtxLink.link`. -/
theorem key_cut {Out : Type} (modes : Label n → KeyMode) (target : Label n) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (budget : PqxdhDeploymentInterface.Budget) (respects : budget.Respects adversary)
    (decision : View n E X → ProbComp Out) :
    𝒮[ctxRun modes replace setup codec route env serverKid bounds mode adversary >>= fun result =>
        decision (ctxView result)] =
      𝒮[do
        let key ← $ᵗ CtxKey
        let result ← ctxRunWith (selectedKey target key) modes replace setup codec route env serverKid bounds mode
          adversary
        decision (ctxView result)] := by
  have law := congrArg (fun distribution => distribution >>= fun view => 𝒮[decision view])
    (key_cut_view modes target replace setup codec route env serverKid bounds mode adversary budget respects)
  simp only [← evalSPMF_bind, bind_map_left, bind_assoc] at law
  exact law

/-- The selected-key law in the measure notation of the targets. -/
theorem key_cut_measure {Out : Type} [MeasurableSpace Out] (modes : Label n → KeyMode) (target : Label n)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (budget : PqxdhDeploymentInterface.Budget) (respects : budget.Respects adversary)
    (decision : View n E X → ProbComp Out) :
    𝒟[ctxRun modes replace setup codec route env serverKid bounds mode adversary >>= fun result =>
        decision (ctxView result)] =
      𝒟[do
        let key ← $ᵗ CtxKey
        let result ← ctxRunWith (selectedKey target key) modes replace setup codec route env serverKid bounds mode
          adversary
        decision (ctxView result)] :=
  evalDist_eq_of_evalSPMF_eq _ _
    (key_cut modes target replace setup codec route env serverKid bounds mode adversary budget respects decision)

end BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.lookup_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.lookup_miss

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.lookup_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.lookup_hit

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.world_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.world_id

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.world_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.world_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.world_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.world_miss

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.miss_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.miss_eager

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.table_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.table_eager

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.base_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.base_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.keyStore_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.keyStore_material

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.chain_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.chain_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.nonce_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.nonce_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.key_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.key_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.selectedKey_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.selectedKey_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.hiddenOpening_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.hiddenOpening_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.hiddenSealing_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.hiddenSealing_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.keyedWith_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.keyedWith_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.simulate_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.simulate_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.opening_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.opening_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.sealing_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.sealing_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.mask_miss_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.mask_miss_self

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.mask_miss_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.mask_miss_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.maskAt_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.maskAt_none

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.world_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.world_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.chain_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.chain_frame

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.world_preserve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.world_preserve

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.initial_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.initial_chain

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.initial_stored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.initial_stored

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.tableKey_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.tableKey_selected

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.world_selected_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.world_selected_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.selected_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.selected_table

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.keyStore_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.keyStore_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.mask_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.mask_absent

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.world_id_impl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.world_id_impl

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.selected_keyedMask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.selected_keyedMask

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.stored_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.stored_view

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.ctxView_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.ctxView_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.key_cut_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.key_cut_view

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.key_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.key_cut

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.key_cut_measure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftKeyCut.key_cut_measure
