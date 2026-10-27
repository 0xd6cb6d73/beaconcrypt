-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys
import BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit

/-!
# Kernel identities of the ideal registration's hidden steps (CE-11b, unit U2)

Step 3 of the split chain of CE-11b design-v2 section 5.2. The first-touch split form `PqxdhDeploymentIdealKeys.idealSplitX` reads, at every hidden read, the material and the seed of the slot, and its hidden steps use the seed half of the value read only through the kernel they publish (the marked build's Server peer) or stage (owner k's established Beacon). `split_kernel` shows that `idealSplitX` is, command by command and exactly, the eager split form `idealSplitEager`: the same draws, with the seed half of every value read replaced by the dummy seed (`eagerDummy`), and with the marked build and owner k's challenge finish followed by a seed fix that reads the seed of the slot from the seed table without drawing it and puts the World's kernel of that seed on the published peer and on the established owner (`xPeek` with `buildApply` and `stepApply`). `ideal_to_splitEager` composes it with `PqxdhDeploymentIdealKeys.ideal_to_splitX`.

- The selected accept ignores the value of its hidden read (`acceptStep_ignores`, from the closure lemmas of `Ignores` and `IgnoresS`), so two services with the same state effects run it alike (`slotImpl_same`, `slotCoreX_same`); `eagerDummy` has the split service's state effects (`eagerDummy_same`).
- Native kernel identities: the marked build at a material and a seed is the build at the material and the dummy seed with the World's Server kernel of the seed put on the published peer (`buildHidden_seed`, from CE-11a's `PqxdhDeploymentHiddenSplit.build_split_raw`); the erased hidden finish at a seed is the one at the dummy seed with the World's Beacon kernel of the seed staged (`nativeCtx_erased_seed`, from `erased_split`); and the source commit of a finish with a replaced staged kernel is the commit with the established owner's kernel replaced (`finish_withKernel`).
- On pairs (the slot program's state with the allocator and the service state): after a read through the allocator in front of the split service, the seed table holds the seed half of the value read at the slot of the coordinates (`slotImpl_split_support`), and a read in front of `eagerDummy` is the read in front of the split service with the seed half replaced by the dummy seed when the coordinates have a slot (`slotImpl_eagerDummy`). The kernel identities of the grouped finish, the grouped owner, owner k's challenge finish and the ideal registration's finish (`group_seed`, `owner_seed`, `challenge_seed`, `finishStepC_seed`) and of its build (`buildStepC_seed`) follow with seed fixes read without drawing (`pairPeek`, `pairPeek_map`); `finishStepC` and `buildStepC` are `finishStep` and `buildStep` that also report the coordinates of their hidden read (`finishStepC_fst`, `buildStepC_fst`), and `slotRunX_seed` carries an identity on pairs to the extended state (`attach_pairPeek`).
- `lazyDummy` (the material of a slot only, joined with the dummy seed) is the service of the final split form, built on top of this module.

These are equalities of programs. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentBackend (XState RegImpl ctxLens seedLens handlerWith gameWith xinitial)
open PqxdhDeploymentIdealSlots (Coord SlotSpec SlotProgram slotCore detach attach)
open PqxdhDeploymentIdealSteps (realRegAt onSlots liftS)
open PqxdhDeploymentIdealErase (SlotFrame readAt)
open PqxdhDeploymentIdealKeys (slotCoreX detachX attachX seedPut)
open PqxdhRegistrationJointKemSecondEntry (Alloc slotImpl emptyAlloc)
open PqxdhDeploymentSeedSplit (SlotService MaterialSpec mapBackend joinTable splitService)
open PqxdhDeploymentFinishErasure (outcomeMap fullX)
open LazyOracleDiscard (Commutes StateLens CacheLens LawEq)
open PqxdhRecordLiftInterface (EnvQuery EnvSpec)

variable {KemSK : Type} {n : ℕ}

/-! ### Slot clients that ignore the values of their hidden reads -/

section Ignores

/-- Two slot handlers with the same coins and the same state effect of every value request (the values may differ). -/
def SameEffects {σ : Type} (impl₁ impl₂ : QueryImpl SlotSpec (StateT σ ProbComp)) : Prop :=
  (∀ coin, impl₁ (.inl coin) = impl₂ (.inl coin)) ∧
    ∀ coords, ((fun _ => ()) <$> impl₁ (.inr coords) : StateT σ ProbComp Unit) = (fun _ => ()) <$> impl₂ (.inr coords)

/-- A slot client that ignores the values of its hidden reads: two slot handlers with the same effects simulate it alike. -/
def Ignores {α : Type} (oa : OracleComp SlotSpec α) : Prop :=
  ∀ {σ : Type} (impl₁ impl₂ : QueryImpl SlotSpec (StateT σ ProbComp)), SameEffects impl₁ impl₂ →
    simulateQ impl₁ oa = simulateQ impl₂ oa

theorem Ignores.pure {α : Type} (a : α) : Ignores (pure a : OracleComp SlotSpec α) := fun _ _ _ => by
  simp only [simulateQ_pure]

theorem Ignores.bind {α β : Type} {oa : OracleComp SlotSpec α} {f : α → OracleComp SlotSpec β}
    (first : Ignores oa) (rest : ∀ a, Ignores (f a)) : Ignores (oa >>= f) := fun impl₁ impl₂ same => by
  simp only [simulateQ_bind, first impl₁ impl₂ same, fun a => rest a impl₁ impl₂ same]

theorem Ignores.map {α β : Type} {oa : OracleComp SlotSpec α} (f : α → β) (first : Ignores oa) :
    Ignores (f <$> oa) := fun impl₁ impl₂ same => by
  simp only [simulateQ_map, first impl₁ impl₂ same]

/-- A coins-only slot client ignores the values of hidden reads (it makes none). -/
theorem Ignores.liftS {α : Type} (work : ProbComp α) : Ignores (liftS work) := fun impl₁ impl₂ same => by
  rw [PqxdhDeploymentIdealSteps.liftS,
    QueryImpl.simulateQ_liftComp_left_eq_of_apply impl₁ (fun t => impl₁ (.inl t)) (fun _ => rfl),
    QueryImpl.simulateQ_liftComp_left_eq_of_apply impl₂ (fun t => impl₂ (.inl t)) (fun _ => rfl)]
  congr 1
  funext t
  exact same.1 t

/-- A hidden read whose value the continuation ignores. -/
theorem Ignores.read {β : Type} (coords : Coord) {k : OracleComp SlotSpec β} (rest : Ignores k) :
    Ignores ((SlotSpec.query (.inr coords) : OracleComp SlotSpec _) >>= fun _ => k) := fun impl₁ impl₂ same => by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
    rest impl₁ impl₂ same]
  have unit₁ : (impl₁ (.inr coords) >>= fun _ => simulateQ impl₂ k) =
      ((fun _ => ()) <$> impl₁ (.inr coords) >>= fun _ => simulateQ impl₂ k) := by rw [bind_map_left]
  have unit₂ : (impl₂ (.inr coords) >>= fun _ => simulateQ impl₂ k) =
      ((fun _ => ()) <$> impl₂ (.inr coords) >>= fun _ => simulateQ impl₂ k) := by rw [bind_map_left]
  rw [unit₁, unit₂, same.2 coords]

/-- A stateful slot step that ignores the values of its hidden reads from every state. -/
def IgnoresS {σ α : Type} (step : StateT σ (OracleComp SlotSpec) α) : Prop := ∀ s, Ignores (step.run s)

theorem IgnoresS.pure {σ α : Type} (a : α) : IgnoresS (pure a : StateT σ (OracleComp SlotSpec) α) := fun s => by
  rw [StateT.run_pure]
  exact Ignores.pure _

theorem IgnoresS.bind {σ α β : Type} {step : StateT σ (OracleComp SlotSpec) α}
    {next : α → StateT σ (OracleComp SlotSpec) β} (first : IgnoresS step) (rest : ∀ a, IgnoresS (next a)) :
    IgnoresS (step >>= next) := fun s => by
  rw [StateT.run_bind]
  exact Ignores.bind (first s) fun r => rest r.1 r.2

/-- A simulation whose every query ignores the values of hidden reads ignores them. -/
theorem IgnoresS.simulateQ {ι' σ α : Type} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec' (StateT σ (OracleComp SlotSpec))) (each : ∀ q, IgnoresS (impl q))
    (work : OracleComp spec' α) : IgnoresS (simulateQ impl work) := by
  induction work using OracleComp.inductionOn with
  | pure a => rw [simulateQ_pure]; exact IgnoresS.pure a
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
      exact IgnoresS.bind (each q) ih

end Ignores

/-! ### The selected accept ignores the value of its hidden read -/

section AcceptIgnores
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhServerAuthNative (NativeState)
open PqxdhDeploymentIdealSteps (tailCE acceptActive acceptInactive acceptExposed acceptStep IdealCore)
open PqxdhDeploymentIdealParams (Target Params)

/-- Every request of item 2's marker tail under `tailCE` ignores the value of its hidden read. -/
theorem tailCE_ignores (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (query : (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).Domain) :
    IgnoresS (tailCE (KemSK := KemSK) (Reader := Reader) hmac index query) := by
  intro s
  rcases query with (input | auxiliary) | mutation
  · simp only [tailCE]
    cases input.shared with
    | challenge => exact Ignores.read _ (Ignores.pure _)
    | known secret => exact Ignores.map _ (Ignores.liftS _)
  · exact Ignores.map _ (Ignores.liftS _)
  · exact Ignores.map _ (Ignores.liftS _)

/-- The active selected accept ignores the value of its hidden read. -/
theorem acceptActive_ignores (seed : PqxdhJointIdentity.IdentitySeed) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (verified : PqxdhServerRootPreparation.Verified Reader) :
    IgnoresS (acceptActive (KemSK := KemSK) setup codec checks seed challenge verified) := by
  intro s
  refine Ignores.bind (Ignores.liftS _) fun pre => ?_
  split
  · exact Ignores.bind (Ignores.liftS _) fun _ => Ignores.pure _
  · refine Ignores.bind (Ignores.liftS _) fun prepared => ?_
    exact Ignores.bind (IgnoresS.simulateQ _ (tailCE_ignores _ _) _ _) fun _ => Ignores.pure _

/-- The raw accept of the ideal registration ignores the value of its hidden read. -/
theorem acceptStep_ignores (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (raw : Pqxdh.Bytes) :
    IgnoresS (acceptStep setup codec route checks t p created raw) := by
  intro x
  change Ignores (if x.backend.accepts = t.accept then _ else _)
  split
  · refine Ignores.map _ ?_
    unfold acceptExposed
    split
    · split
      · exact acceptActive_ignores setup codec checks _ _ _ _
      · exact Ignores.map _ (Ignores.liftS _)
    · exact Ignores.map _ (Ignores.liftS _)
  · exact Ignores.liftS _

end AcceptIgnores

/-! ### Services of the split forms -/

section Services
open PqxdhDeploymentHiddenLayout (joinOutput splitOutput)
open PqxdhDeploymentHiddenSplit (dummySeed)
open PqxdhRegistrationJointKemSecondEntry (slot_some slot_none)

/-- The seed table of the record world's slots. -/
abbrev SeedCache (n : ℕ) := (PqxdhRecordLiftWorld.SeedSpec n).QueryCache

/-- The material cache of the slots. -/
abbrev MatCache (n : ℕ) := (MaterialSpec n).QueryCache

/-- The eager service with dummy values: the split service's draws (the material and the seed of the slot at every read), returning the material joined with the dummy seed. -/
noncomputable def eagerDummy : SlotService (MatCache n × SeedCache n) n :=
  fun j => (fun v => joinOutput (splitOutput v).1 dummySeed) <$> splitService j

/-- The lazy service: the material of the slot only, joined with the dummy seed; the seed table is untouched. -/
noncomputable def lazyDummy : SlotService (MatCache n × SeedCache n) n :=
  fun j => (fun m => joinOutput m dummySeed) <$> (StateLens.fst (MatCache n) (SeedCache n)).query (spec := MaterialSpec n) j

/-- Two slot services with the same state effects (their values may differ). -/
def SameSvc {S : Type} (svc₁ svc₂ : SlotService S n) : Prop :=
  ∀ j, ((fun _ => ()) <$> svc₁ j : StateT S ProbComp Unit) = (fun _ => ()) <$> svc₂ j

/-- The eager service with dummy values has the split service's state effects. -/
theorem eagerDummy_same : SameSvc (eagerDummy (n := n)) splitService := fun j => by
  simp only [eagerDummy, Functor.map_map]

/-- Allocators in front of two services with the same state effects are slot handlers with the same effects. -/
theorem slotImpl_same {S : Type} (svc₁ svc₂ : SlotService S n) (same : SameSvc svc₁ svc₂) :
    SameEffects (slotImpl (D := Coord) svc₁) (slotImpl svc₂) := by
  refine ⟨fun _ => rfl, fun coords => ?_⟩
  apply StateT.ext
  intro st
  rw [StateT.run_map, StateT.run_map]
  have serve : ∀ (j : PqxdhRecordLiftInterface.Slot n) (alloc : Alloc Coord n),
      (fun r : PqxdhServerAuthKeySchedule.Output × S => ((), (alloc, r.2))) <$> (svc₁ j).run st.2 =
        (fun r : PqxdhServerAuthKeySchedule.Output × S => ((), (alloc, r.2))) <$> (svc₂ j).run st.2 := by
    intro j alloc
    have h := congrArg (fun step : StateT S ProbComp Unit => (fun r => ((), (alloc, r.2))) <$> step.run st.2) (same j)
    simpa only [StateT.run_map, Functor.map_map] using h
  rcases found : st.1.1 coords with _ | j
  · by_cases room : st.1.2 < n
    · rw [slot_none _ _ _ found room, slot_none _ _ _ found room, Functor.map_map, Functor.map_map]
      exact serve _ _
    · simp only [slotImpl, QueryImpl.add_apply_inr, StateT.run_mk, found, room, _root_.dite_false]
  · rw [slot_some _ _ _ _ found, slot_some _ _ _ _ found, Functor.map_map, Functor.map_map]
    exact serve _ _

/-- A slot core with the seeds in the extended state runs a command that ignores the values of its hidden reads alike under two services with the same state effects. -/
theorem slotCoreX_same {Γ : Type} (prog : PqxdhLiveServerConstruction.Created Unit → SlotProgram KemSK Γ n)
    (svc₁ svc₂ : SlotService (MatCache n × SeedCache n) n) (same : SameSvc svc₁ svc₂)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : EnvQuery) (ignores : IgnoresS (prog created query)) :
    slotCoreX prog svc₁ created query = slotCoreX prog svc₂ created query := by
  apply StateT.ext
  intro x
  simp only [slotCoreX, StateT.run_mk]
  rw [ignores (detachX x) _ _ (slotImpl_same svc₁ svc₂ same)]

end Services

/-! ### Kernel identities of the hidden steps at the dummy seed -/

section KernelIdentities
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhDeploymentIdealSteps (buildHidden)
open PqxdhDeploymentHiddenLayout (joinOutput splitOutput)
open PqxdhDeploymentHiddenSplit (dummySeed replaceRaw setPeerKernel withKernel)

/-- Settling commutes with replacing the published kernel. -/
theorem settle_replaceRaw (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))) :
    PqxdhServerAuthExperiment.settle server (Functor.map (replaceRaw kernel) result) =
      replaceRaw kernel (PqxdhServerAuthExperiment.settle server result) := by
  cases result <;> rfl

/-- The Server peer published by a build response gets a kernel. -/
def peerFix (response : Option PqxdhServerRegistrationPublication.Response) (state : NativeState KemSK)
    (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) : NativeState KemSK :=
  match response with
  | none => state
  | some response => (state.1, { state.2 with server := setPeerKernel state.2.server response.keyId kernel })

/-- Kernel identity of the marked build (design-v2 section 5.2, step 3): the marked build with the factored services at a material and a seed is the marked build at the material and the dummy seed, with the World's Server kernel of the seed put on the peer the build published. -/
theorem buildHidden_seed (m : PqxdhDeploymentHiddenLayout.Material) (seed : PqxdhRecordLiftSeed.Seed) (session : ℕ)
    (payload : Option Pqxdh.Bytes) (state : NativeState KemSK) :
    (buildHidden (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks (joinOutput m seed)) session
        payload).run state =
      (fun r => (r.1, peerFix r.1 r.2 (PqxdhRecordLiftWorld.kernel .server seed))) <$>
        (buildHidden (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks (joinOutput m dummySeed))
          session payload).run state := by
  have built : (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks (joinOutput m seed)).hiddenBuild =
      fun token payload server => Functor.map (replaceRaw (PqxdhRecordLiftWorld.kernel .server seed)) <$>
        (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks (joinOutput m dummySeed)).hiddenBuild
          token payload server := by
    funext token payload server
    exact PqxdhDeploymentHiddenSplit.build_split_raw _ _ setup.source _ m seed dummySeed _ _ () server
  unfold buildHidden
  rw [built, PqxdhDeploymentBackend.nativeGet_bind, PqxdhDeploymentBackend.nativeGet_bind]
  rcases pending : state.2.pending session with _ | token
  · simp only [StateT.run_pure, map_pure]
    rfl
  · simp only []
    rw [PqxdhDeploymentBackend.nativeCoins_bind, PqxdhDeploymentBackend.nativeCoins_bind, StateT.run_map, bind_map_left,
      map_bind]
    refine bind_congr fun result => ?_
    rw [settle_replaceRaw]
    rcases settled : PqxdhServerAuthExperiment.settle state.2.server result.1 with ⟨_ | response, after⟩
    · simp only [PqxdhDeploymentHiddenSplit.replaceRaw]
      rfl
    · simp only [PqxdhDeploymentHiddenSplit.replaceRaw]
      rfl

section BuildStepC
variable (route : RawCtxServerRouting.SenderDecoder)
open PqxdhDeploymentIdealSteps (buildStep buildHidden IdealCore)
open PqxdhDeploymentIdealErase (buildFocus)

/-- The marked build on the extended state, reporting the coordinates of its hidden read. -/
noncomputable def buildHiddenC (hidden : PqxdhServerAuthKeySchedule.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (session : ℕ) (payload : Option Pqxdh.Bytes) (coords : Coord) :
    StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) (Option PqxdhServerRegistrationPublication.Response × Option Coord) :=
  readAt coords >>= fun value => onSlots ((fun r => (r, some coords)) <$> buildFocus (hidden value) session payload coords)

/-- The build of the ideal registration that also reports the coordinates of its hidden read (`buildStep` with the marked coordinates returned on the hidden branch). -/
noncomputable def buildStepC (hidden : PqxdhServerAuthKeySchedule.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (created : PqxdhLiveServerConstruction.Created Unit) (session : ℕ) (payload : Option Pqxdh.Bytes) :
    StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) (Option PqxdhServerRegistrationPublication.Response × Option Coord) :=
  fun x => match x.backend.marks with
    | some (index, coords) =>
        if index = session ∧ (x.base.native.shared.2.pending session).isSome then
          (buildHiddenC hidden session payload coords).run x
        else (fun r => ((r.1, none), r.2)) <$> onSlots (realRegAt setup codec route checks created ⟨.build session payload, trivial⟩) x
    | none => (fun r => ((r.1, none), r.2)) <$> onSlots (realRegAt setup codec route checks created ⟨.build session payload, trivial⟩) x

/-- Without the reported coordinates, `buildStepC` is `buildStep`. -/
theorem buildStepC_fst (hidden : PqxdhServerAuthKeySchedule.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (created : PqxdhLiveServerConstruction.Created Unit) (session : ℕ) (payload : Option Pqxdh.Bytes) :
    (fun r => r.1) <$> buildStepC setup codec checks route hidden created session payload =
      buildStep setup codec route checks hidden created session payload := by
  apply StateT.ext
  intro x
  rw [StateT.run_map]
  unfold buildStepC buildStep
  simp only [StateT.run]
  rcases marked : x.backend.marks with _ | ⟨index, coords⟩
  · simp only [Functor.map_map]
    exact id_map _
  · simp only []
    split
    · have h := PqxdhDeploymentIdealErase.readAt_bind_run coords
        (fun value => onSlots ((fun r => (r, some coords)) <$> buildFocus (hidden value) session payload coords)) x
      simp only [StateT.run] at h
      rw [buildHiddenC, h, map_bind]
      refine bind_congr fun value => ?_
      change (fun p => (p.1.1, p.2)) <$> liftS (((fun r => (r, some coords)) <$>
        buildFocus (hidden value) session payload coords).run x) = _
      rw [StateT.run_map]
      simp only [buildFocus, liftS, StateT.run, map_eq_bind_pure_comp, Function.comp_def, OracleComp.liftComp_bind,
        OracleComp.liftComp_pure, bind_assoc, pure_bind, marked]
    · simp only [Functor.map_map]
      exact id_map _

/-- The published Server peer in the extended state gets the World's Server kernel of a seed. -/
noncomputable def buildApply (seed : PqxdhRecordLiftSeed.Seed)
    (r : (Option PqxdhServerRegistrationPublication.Response × Option Coord) × XState KemSK IdealCore 2) :
    (Option PqxdhServerRegistrationPublication.Response × Option Coord) × XState KemSK IdealCore 2 :=
  (r.1, { r.2 with base := { r.2.base with native := { r.2.base.native with
    shared := peerFix r.1.1 r.2.base.native.shared (PqxdhRecordLiftWorld.kernel .server seed) } } })

end BuildStepC

end KernelIdentities

/-! ### Supports of lazy queries and of the split service -/

section Supports
open PqxdhDeploymentHiddenLayout (joinOutput splitOutput)
open PqxdhDeploymentHiddenSplit (dummySeed)
open PqxdhRegistrationJointKemSecondEntry (slot_some slot_none)
variable {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec ι₀} [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]

/-- After a lazy query, the cache holds the answer at the queried point. -/
theorem query_support (u : spec₀.Domain) (cache : spec₀.QueryCache) :
    ∀ r ∈ support ((spec₀.randomOracle u).run cache), r.2 u = some r.1 := by
  intro r member
  rcases found : cache u with _ | w
  · rw [LazyOracleDiscard.query_of_none found] at member
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at member
    obtain ⟨y, _, rfl⟩ := member
    exact QueryCache.cacheQuery_self cache u y
  · rw [LazyOracleDiscard.query_of_some found, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact found

/-- After the split service at a slot, the seed table holds the seed half of the returned output at that slot. -/
theorem splitService_support (j : PqxdhRecordLiftInterface.Slot n) (state : MatCache n × SeedCache n) :
    ∀ q ∈ support ((splitService j).run state), q.2.2 j = some (splitOutput q.1).2 := by
  intro q member
  simp only [splitService, StateT.run_bind, support_bind, Set.mem_iUnion] at member
  obtain ⟨first, _, second, secondMember, final⟩ := member
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at final
  subst final
  simp only [StateLens.query, StateLens.snd, StateT.run, support_map, Set.mem_image] at secondMember
  obtain ⟨answer, answerMember, rfl⟩ := secondMember
  rw [PqxdhDeploymentHiddenLayout.split_join]
  exact query_support (spec₀ := PqxdhRecordLiftWorld.SeedSpec n) j _ answer answerMember

/-- After a value read through the allocator in front of the split service, the seed table holds the seed half of the read value at the slot of the coordinates, if they have one. -/
theorem slotImpl_split_support (coords : Coord) (state : Alloc Coord n × (MatCache n × SeedCache n)) :
    ∀ p ∈ support ((slotImpl splitService (.inr coords)).run state),
      ∀ j, p.2.1.1 coords = some j → p.2.2.2 j = some (splitOutput p.1).2 := by
  intro p member j allocated
  rcases found : state.1.1 coords with _ | slot
  · by_cases room : state.1.2 < n
    · rw [slot_none _ _ _ found room, support_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      have same : j = ⟨state.1.2, room⟩ := by
        simp only [Function.update_self, Option.some.injEq] at allocated
        exact allocated.symm
      subst same
      exact splitService_support _ _ inner innerMember
    · simp only [slotImpl, QueryImpl.add_apply_inr, StateT.run_mk, found, room, _root_.dite_false, support_map,
        Set.mem_image] at member
      obtain ⟨answer, _, rfl⟩ := member
      rw [found] at allocated
      cases allocated
  · rw [slot_some _ _ _ _ found, support_map] at member
    obtain ⟨inner, innerMember, rfl⟩ := member
    have same : j = slot := by
      rw [found] at allocated
      exact (Option.some.inj allocated).symm
    subst same
    exact splitService_support _ _ inner innerMember

/-- A value read through the allocator in front of the eager service with dummy values is the read in front of the split service, with the read value's seed half replaced by the dummy seed when the coordinates have a slot. -/
theorem slotImpl_eagerDummy (coords : Coord) (state : Alloc Coord n × (MatCache n × SeedCache n)) :
    (slotImpl eagerDummy (.inr coords)).run state =
      (fun p => ((match p.2.1.1 coords with
        | some _ => joinOutput (splitOutput p.1).1 dummySeed
        | none => p.1), p.2)) <$> (slotImpl splitService (.inr coords)).run state := by
  rcases found : state.1.1 coords with _ | slot
  · by_cases room : state.1.2 < n
    · rw [slot_none _ _ _ found room, slot_none _ _ _ found room, Functor.map_map]
      simp only [eagerDummy, StateT.run_map, Functor.map_map, Function.update_self]
    · simp only [slotImpl, QueryImpl.add_apply_inr, StateT.run_mk, found, room, _root_.dite_false, Functor.map_map]
  · rw [slot_some _ _ _ _ found, slot_some _ _ _ _ found, Functor.map_map]
    simp only [eagerDummy, StateT.run_map, Functor.map_map, found]

end Supports

/-! ### Seed fixes on pairs -/

section PairFix
variable {σ α M : Type}

/-- A seed fix on pairs, read without drawing: when `coords` names coordinates that have a slot whose seed is present in the service state's seed table, `apply` puts that seed in; otherwise nothing changes. -/
def pairPeek (coords : α × σ → Option Coord) (apply : PqxdhRecordLiftSeed.Seed → α × σ → α × σ)
    (r : α × (σ × (Alloc Coord n × (M × SeedCache n)))) : α × (σ × (Alloc Coord n × (M × SeedCache n))) :=
  match coords (r.1, r.2.1) with
  | none => r
  | some c => match r.2.2.1.1 c with
    | none => r
    | some j => match r.2.2.2.2 j with
      | none => r
      | some seed => ((apply seed (r.1, r.2.1)).1, ((apply seed (r.1, r.2.1)).2, r.2.2))

/-- A map of the value and the slot program's state, on pairs. -/
def liftPair {β τ R : Type} (g : α × σ → β × τ) (r : α × (σ × R)) : β × (τ × R) :=
  ((g (r.1, r.2.1)).1, ((g (r.1, r.2.1)).2, r.2.2))

/-- A seed fix commutes with a map of value and state that carries its coordinates and its effect. -/
theorem pairPeek_map {β τ : Type} (g : α × σ → β × τ) (coords₁ : α × σ → Option Coord) (coords₂ : β × τ → Option Coord)
    (apply₁ : PqxdhRecordLiftSeed.Seed → α × σ → α × σ) (apply₂ : PqxdhRecordLiftSeed.Seed → β × τ → β × τ)
    (hc : ∀ r, coords₂ (g r) = coords₁ r) (ha : ∀ seed r, g (apply₁ seed r) = apply₂ seed (g r))
    (r : α × (σ × (Alloc Coord n × (M × SeedCache n)))) :
    liftPair g (pairPeek coords₁ apply₁ r) = pairPeek coords₂ apply₂ (liftPair g r) := by
  unfold pairPeek liftPair
  simp only []
  rw [hc]
  rcases coords₁ (r.1, r.2.1) with _ | c
  · rfl
  · simp only []
    rcases r.2.2.1.1 c with _ | j
    · rfl
    · simp only []
      rcases r.2.2.2.2 j with _ | seed
      · rfl
      · simp only [ha]

/-- A value read at fixed coordinates, on pairs. -/
theorem onPair_readAt {S : Type} (svc : SlotService S n) (coords : Coord) (z : σ × (Alloc Coord n × S)) :
    (PqxdhDeploymentIdealErase.onPair svc (readAt coords : StateT σ (OracleComp SlotSpec) _)).run z =
      (fun p => (p.1, (z.1, p.2))) <$> (slotImpl svc (.inr coords)).run z.2 := by
  rw [PqxdhDeploymentIdealErase.onPair_run]
  change (fun r => (r.1.1, (r.1.2, r.2))) <$> (simulateQ (slotImpl svc) ((fun v => (v, z.1)) <$>
    (SlotSpec.query (.inr coords) : OracleComp SlotSpec _))).run z.2 = _
  rw [simulateQ_map, StateT.run_map, Functor.map_map, simulateQ_spec_query]

end PairFix

/-! ### Kernel identities of owner k's challenge finish, on pairs -/

section FinishKernel
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhDeploymentIdealSteps (groupCE erasedHidden)
open PqxdhDeploymentIdealErase (onPair groupExplicit groupCE_explicit onPair_bind onPair_onSlots onPair_pure onPair_map)
open PqxdhRegistrationJointKemPostSkeleton (Pending embed message)
open PqxdhDeploymentHiddenLayout (joinOutput splitOutput)
open PqxdhDeploymentHiddenSplit (dummySeed withKernel)

/-- The staged registration of a grouped finish gets the World's Beacon kernel of a seed. -/
noncomputable def groupApply (seed : PqxdhRecordLiftSeed.Seed)
    (r : Option PqxdhBeaconPhase2Publication.Staged × (NativeState KemSK × Option Coord)) :
    Option PqxdhBeaconPhase2Publication.Staged × (NativeState KemSK × Option Coord) :=
  (r.1.map (withKernel (PqxdhRecordLiftWorld.kernel .beacon seed)), r.2)

/-- The erased hidden finish on the shared native state at a material and a seed is the one at the material and the dummy seed, with the World's Beacon kernel of the seed staged. -/
theorem nativeCtx_erased_seed (m : PqxdhDeploymentHiddenLayout.Material) (seed : PqxdhRecordLiftSeed.Seed)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (s : NativeState KemSK) :
    (PqxdhServerAuthNative.nativeCtx (PqxdhDeploymentHiddenEntry.finishErasedSvc setup codec m seed pending)).run s =
      (fun r => (r.1.map (withKernel (PqxdhRecordLiftWorld.kernel .beacon seed)), r.2)) <$>
        (PqxdhServerAuthNative.nativeCtx (PqxdhDeploymentHiddenEntry.finishErasedSvc setup codec m dummySeed
          pending)).run s := by
  have split := PqxdhDeploymentHiddenSplit.erased_split (PqxdhServerAuthBeaconFactor.nativePrim setup codec)
    (fun entry _ => pure (entry, none)) setup.source (fun response => pure (codec.application response)) codec.frameRead
    (PqxdhPhase2DhRootConsumer.cleared pending) m seed dummySeed
  change (fun result => (result.1, PqxdhDeploymentBackend.gameLens.set s result.2)) <$>
      (PqxdhDeploymentHiddenEntry.finishErasedSvc setup codec m seed pending).run
        (PqxdhDeploymentBackend.gameLens.get s) =
    (fun r => (r.1.map (withKernel (PqxdhRecordLiftWorld.kernel .beacon seed)), r.2)) <$>
      ((fun result => (result.1, PqxdhDeploymentBackend.gameLens.set s result.2)) <$>
        (PqxdhDeploymentHiddenEntry.finishErasedSvc setup codec m dummySeed pending).run
          (PqxdhDeploymentBackend.gameLens.get s))
  unfold PqxdhDeploymentHiddenEntry.finishErasedSvc PqxdhDeploymentHiddenEntry.finishPointed
  rw [split, StateT.run_map, StateT.run_map]
  simp only [Functor.map_map]

/-- Kernel identity of the grouped finish, on pairs: in front of the split service the grouped finish with the erased hidden services is, exactly, the grouped finish in front of the eager service with dummy values followed by the seed fix of its recorded coordinates. -/
theorem group_seed (pending : Pending Response) (s : NativeState KemSK)
    (state : Alloc Coord 2 × (MatCache 2 × SeedCache 2)) :
    (onPair splitService (groupCE (KemSK := KemSK) setup codec (erasedHidden setup codec checks) pending)).run
        ((s, none), state) =
      pairPeek (fun r => r.2.2) groupApply <$>
        (onPair eagerDummy (groupCE (KemSK := KemSK) setup codec (erasedHidden setup codec checks) pending)).run
          ((s, none), state) := by
  rw [groupCE_explicit]
  unfold groupExplicit
  rcases shared : pending.root.shared with _ | secret
  · simp only []
    split
    · rw [onPair_bind, onPair_bind, StateT.run_bind, StateT.run_bind, onPair_readAt, onPair_readAt,
        slotImpl_eagerDummy, Functor.map_map, bind_map_left, bind_map_left]
      simp only [map_bind]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun p member => ?_
      rw [onPair_onSlots, onPair_onSlots]
      simp only [StateLens.lift, StateT.run, StateLens.fst, Functor.map_map]
      rcases allocated : p.2.1.1 (message pending.root.dh1 pending.root.dh2 pending.root.dh3 pending.root.dh4)
        with _ | j
      · simp only []
        congr 1
        funext a
        simp only [pairPeek, allocated]
      · have seeded := slotImpl_split_support _ _ p member j allocated
        have native := nativeCtx_erased_seed setup codec (splitOutput p.1).1 (splitOutput p.1).2 (embed pending) s
        simp only [StateT.run] at native
        simp only [PqxdhDeploymentIdealSteps.erasedHidden, PqxdhDeploymentHiddenLayout.split_join, native,
          Functor.map_map]
        congr 1
        funext a
        simp only [pairPeek, allocated, seeded, groupApply]
    · rw [onPair_pure, onPair_pure, StateT.run_pure, map_pure]
      rfl
  · rw [onPair_onSlots, onPair_onSlots]
    simp only [StateLens.lift, StateT.run, StateLens.fst, Functor.map_map]
    rfl

/-- A step lifted through a lens runs the step on the focused part. -/
theorem lift_run {σ' ρ α : Type} (E : StateLens σ' ρ) (step : StateT ρ ProbComp α) (s : σ') :
    (E.lift step).run s = (fun r => (r.1, E.set s r.2)) <$> step.run (E.get s) := rfl

/-- A coins-only slot step that does not touch the state, on pairs. -/
theorem onPair_onSlots_lift {σ S α : Type} (svc : SlotService S n) (work : ProbComp α) (z : σ × (Alloc Coord n × S)) :
    (onPair svc (onSlots (StateT.lift work : StateT σ ProbComp α))).run z = (fun a => (a, z)) <$> work := by
  rw [onPair_onSlots]
  simp only [StateLens.lift, StateT.run, StateLens.fst, StateT.lift, map_bind, map_pure]
  rw [map_eq_bind_pure_comp]
  rfl

/-- An established owner's kernel replaced; every other owner is unchanged. -/
def setOwnerKernel (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) : PqxdhRegistrationSchedule.Owner KemSK :=
  match owner.beacon.phase with
  | .established control associatedData _ =>
      { owner with beacon := { owner.beacon with phase := .established control associatedData kernel } }
  | _ => owner

/-- The source commit of a finish with a staged kernel replaced is the commit with the established owner's kernel replaced. -/
theorem finish_withKernel (control : beaconcrypt_core.pqxdh.BeaconInitSent) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged)
    (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) :
    PqxdhBeaconPhase2Publication.finish control owner (staged.map (withKernel kernel)) =
      ((PqxdhBeaconPhase2Publication.finish control owner staged).1,
        setOwnerKernel (PqxdhBeaconPhase2Publication.finish control owner staged).2 kernel) := by
  rcases staged with _ | staged
  · rfl
  · simp only [Option.map_some, PqxdhBeaconPhase2Publication.finish, withKernel]
    split_ifs <;> rfl

/-- The returned owner of a grouped owner gets the World's Beacon kernel of a seed. -/
noncomputable def ownerApply (seed : PqxdhRecordLiftSeed.Seed)
    (r : (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × (NativeState KemSK × Option Coord)) :
    (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × (NativeState KemSK × Option Coord) :=
  ((r.1.1, setOwnerKernel r.1.2 (PqxdhRecordLiftWorld.kernel .beacon seed)), r.2)

/-- Kernel identity of the grouped owner, on pairs: in front of the split service the grouped owner with the erased hidden services is, exactly, the grouped owner in front of the eager service with dummy values followed by the seed fix of its recorded coordinates. -/
theorem owner_seed (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (s : NativeState KemSK)
    (state : Alloc Coord 2 × (MatCache 2 × SeedCache 2)) :
    (onPair splitService (simulateQ (PqxdhDeploymentIdealSteps.ownerImplCE setup codec (erasedHidden setup codec checks)
        challenge) (PqxdhDeploymentIdealSteps.groupedOwnerCE (Response := Response) raw owner))).run ((s, none), state) =
      pairPeek (fun r => r.2.2) ownerApply <$>
        (onPair eagerDummy (simulateQ (PqxdhDeploymentIdealSteps.ownerImplCE setup codec (erasedHidden setup codec checks)
          challenge) (PqxdhDeploymentIdealSteps.groupedOwnerCE (Response := Response) raw owner))).run ((s, none), state) := by
  rw [PqxdhDeploymentIdealErase.owner_explicit]
  unfold PqxdhDeploymentIdealErase.ownerExplicit
  split
  · rename_i control prekey oneTime kem phase
    rw [onPair_bind, onPair_bind, StateT.run_bind, StateT.run_bind, onPair_onSlots_lift, onPair_onSlots_lift,
      bind_map_left, bind_map_left]
    simp only [map_bind]
    refine bind_congr fun prepared => ?_
    cases prepared with
    | none =>
        rw [onPair_pure, onPair_pure, StateT.run_pure, map_pure]
        rfl
    | some prepared =>
        rw [onPair_map, onPair_map, StateT.run_map, StateT.run_map, group_seed, Functor.map_map, Functor.map_map]
        congr 1
        funext r
        exact pairPeek_map (fun q : Option PqxdhBeaconPhase2Publication.Staged × (NativeState KemSK × Option Coord) =>
          (PqxdhBeaconPhase2Publication.finish control owner q.1, q.2)) (fun r => r.2.2) (fun r => r.2.2) groupApply
          ownerApply (fun _ => rfl) (fun seed q => by
            simp only [groupApply, ownerApply]
            rw [finish_withKernel]) r
  · rw [onPair_pure, onPair_pure, StateT.run_pure, map_pure]
    rfl

/-- Modifying a list at an index after setting it there applies the modification to the set value. -/
theorem set_modify {β : Type} (l : List β) (i : ℕ) (a : β) (f : β → β) : (l.set i a).modify i f = l.set i (f a) := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_modify, List.getElem?_set', List.getElem?_set']
  by_cases same : i = k
  · subst same
    rcases l[i]? with _ | b <;> simp [Function.const]
  · simp only [same, ↓reduceIte, id_map']

/-- An owner's established kernel replaced by the World's Beacon kernel of a seed. -/
noncomputable def setKernelAt (seed : PqxdhRecordLiftSeed.Seed) (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    PqxdhRegistrationSchedule.Owner KemSK :=
  setOwnerKernel owner (PqxdhRecordLiftWorld.kernel .beacon seed)

/-- The registration state after a grouped owner: the returned owner reinstalled at its index. -/
def reinstall (sched : PqxdhRegistrationSchedule.State KemSK) (index : ℕ)
    (b : Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) (q : NativeState KemSK × Option Coord) :
    Option Pqxdh.Bytes × (PqxdhRegistrationSchedule.State KemSK × Option Coord) :=
  (b.1, ({ shared := q.1, owners := sched.owners.set index b.2 }, q.2))

/-- Owner k's established kernel, at its index in the registration state, gets the World's Beacon kernel of a seed. -/
noncomputable def challengeApply (index : ℕ) (seed : PqxdhRecordLiftSeed.Seed)
    (r : Option Pqxdh.Bytes × (PqxdhRegistrationSchedule.State KemSK × Option Coord)) :
    Option Pqxdh.Bytes × (PqxdhRegistrationSchedule.State KemSK × Option Coord) :=
  (r.1, ({ r.2.1 with owners := r.2.1.owners.modify index (setKernelAt seed) }, r.2.2))

/-- Owner k's challenge finish dispatches on the addressed owner (`PqxdhDeploymentIdealErase.challengeBranch`). -/
theorem finishChallenge_branch (hidden : PqxdhServerAuthKeySchedule.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (index : ℕ) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationSchedule.State KemSK × Option Coord) :
    (PqxdhDeploymentIdealSteps.finishChallenge setup codec hidden challenge index raw).run state =
      (PqxdhDeploymentIdealErase.challengeBranch setup codec hidden challenge index raw (state.1.owners[index]?)).run
        state := by
  unfold PqxdhDeploymentIdealSteps.finishChallenge PqxdhDeploymentIdealErase.challengeBranch
  simp only [StateT.run]
  rcases state.1.owners[index]? with _ | owner
  · rfl
  · simp only [map_eq_bind_pure_comp, Function.comp_def]

/-- Kernel identity of owner k's challenge finish, on pairs. -/
theorem challenge_seed (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (index : ℕ) (raw : Pqxdh.Bytes)
    (sched : PqxdhRegistrationSchedule.State KemSK) (state : Alloc Coord 2 × (MatCache 2 × SeedCache 2)) :
    (onPair splitService (PqxdhDeploymentIdealSteps.finishChallenge setup codec (erasedHidden setup codec checks)
        challenge index raw)).run ((sched, none), state) =
      pairPeek (fun r => r.2.2) (challengeApply index) <$>
        (onPair eagerDummy (PqxdhDeploymentIdealSteps.finishChallenge setup codec (erasedHidden setup codec checks)
          challenge index raw)).run ((sched, none), state) := by
  rw [PqxdhDeploymentIdealErase.onPair_dispatch _ _ (fun st => st.1.owners[index]?)
      (PqxdhDeploymentIdealErase.challengeBranch setup codec (erasedHidden setup codec checks) challenge index raw)
      (finishChallenge_branch setup codec _ challenge index raw),
    PqxdhDeploymentIdealErase.onPair_dispatch _ _ (fun st => st.1.owners[index]?)
      (PqxdhDeploymentIdealErase.challengeBranch setup codec (erasedHidden setup codec checks) challenge index raw)
      (finishChallenge_branch setup codec _ challenge index raw)]
  rcases found : sched.owners[index]? with _ | owner
  · simp only [PqxdhDeploymentIdealErase.challengeBranch]
    rw [onPair_pure, onPair_pure, StateT.run_pure, map_pure]
    rfl
  · have shape : ∀ st : PqxdhRegistrationSchedule.State KemSK × Option Coord,
        (PqxdhDeploymentIdealErase.challengeBranch setup codec (erasedHidden setup codec checks) challenge index raw
          (some owner)).run st =
        (fun r => reinstall st.1 index r.1 r.2) <$>
          (simulateQ (PqxdhDeploymentIdealSteps.ownerImplCE setup codec (erasedHidden setup codec checks) challenge)
            (PqxdhDeploymentIdealSteps.groupedOwnerCE (Response := Response) raw owner)).run (st.1.shared, st.2) :=
      fun _ => rfl
    have focused := fun svc : SlotService (MatCache 2 × SeedCache 2) 2 =>
      PqxdhDeploymentIdealErase.onPair_focus svc
        (PqxdhDeploymentIdealErase.challengeBranch setup codec (erasedHidden setup codec checks) challenge index raw
          (some owner))
        (simulateQ (PqxdhDeploymentIdealSteps.ownerImplCE setup codec (erasedHidden setup codec checks) challenge)
          (PqxdhDeploymentIdealSteps.groupedOwnerCE (Response := Response) raw owner))
        (fun st => (st.1.shared, st.2)) (fun st b q => reinstall st.1 index b q) shape ((sched, none), state)
    rw [focused, focused]
    simp only []
    rw [owner_seed, Functor.map_map, Functor.map_map]
    congr 1
    funext r
    exact pairPeek_map (fun q => reinstall sched index q.1 q.2) (fun r => r.2.2) (fun r => r.2.2) ownerApply
      (challengeApply index) (fun _ => rfl)
      (fun seed q => by simp only [ownerApply, challengeApply, reinstall, setKernelAt, set_modify]) r

/-- Replacing an established owner's kernel keeps whether each owner is established. -/
theorem establishedAt_modify (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (index : ℕ)
    (seed : PqxdhRecordLiftSeed.Seed) (other : ℕ) :
    PqxdhDeploymentIdealSteps.establishedAt (owners.modify index (setKernelAt seed)) other =
      PqxdhDeploymentIdealSteps.establishedAt owners other := by
  unfold PqxdhDeploymentIdealSteps.establishedAt
  rw [List.getElem?_modify]
  rcases owners[other]? with _ | owner
  · rfl
  · by_cases same : index = other
    · simp only [same, ↓reduceIte, Option.map_eq_map, Option.map_some, setKernelAt, setOwnerKernel]
      rcases phase : owner.beacon.phase <;> simp only [phase]
    · simp only [same, ↓reduceIte, Option.map_eq_map, Option.map_some]

section FinishStepC
variable (route : RawCtxServerRouting.SenderDecoder) {count : ℕ}
open PqxdhDeploymentIdealSteps (finishStep finishChallenge initSentAt establishedAt IdealCore)
open PqxdhDeploymentIdealParams (Target Params)

/-- The extended state after owner k's challenge finish (as `finishStep` assembles it). -/
def assembleF (x : XState KemSK IdealCore 2) (owner : ℕ)
    (r : PqxdhRegistrationSchedule.State KemSK × Option Coord) : XState KemSK IdealCore 2 :=
  { x with
    base := { x.base with native := r.1 }
    snap := PqxdhDeploymentLater.snapshotAt x.snap x.base.native.owners (some owner)
    backend := { x.backend with
      beacon := if establishedAt r.1.owners owner then r.2.or x.backend.beacon else x.backend.beacon } }

/-- Owner k's challenge finish on the extended state, reporting the coordinates of its hidden read. -/
noncomputable def finishHiddenC (p : Params KemSK count)
    (hidden : PqxdhServerAuthKeySchedule.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (owner : ℕ) (raw : Pqxdh.Bytes) :
    StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) (Option Pqxdh.Bytes × Option Coord) := fun x =>
  (fun r => ((r.1, r.2.2), assembleF x owner r.2)) <$>
    (finishChallenge setup codec hidden p.challenge owner raw).run (x.base.native, none)

/-- The finish of the ideal registration that also reports the coordinates of its hidden read (`finishStep` with the recorded coordinates returned). -/
noncomputable def finishStepC (t : Target count) (p : Params KemSK count)
    (hidden : PqxdhServerAuthKeySchedule.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (created : PqxdhLiveServerConstruction.Created Unit) (owner : ℕ) (raw : Pqxdh.Bytes) :
    StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) (Option Pqxdh.Bytes × Option Coord) := fun x =>
  if x.backend.active = true ∧ owner = t.kem.val ∧ initSentAt x.base.native.owners owner = true then
    (finishHiddenC setup codec p hidden owner raw).run x
  else (fun r => ((r.1, none), r.2)) <$>
    onSlots (realRegAt setup codec route checks created ⟨.finish owner raw, trivial⟩) x

/-- Without the reported coordinates, `finishStepC` is `finishStep`. -/
theorem finishStepC_fst (t : Target count) (p : Params KemSK count)
    (hidden : PqxdhServerAuthKeySchedule.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (created : PqxdhLiveServerConstruction.Created Unit) (owner : ℕ) (raw : Pqxdh.Bytes) :
    (fun r => r.1) <$> finishStepC setup codec checks route t p hidden created owner raw =
      finishStep setup codec route checks t p hidden created owner raw := by
  apply StateT.ext
  intro x
  rw [StateT.run_map]
  unfold finishStepC finishStep finishHiddenC
  simp only [StateT.run]
  split
  · simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    rfl
  · simp only [Functor.map_map]
    exact id_map _

/-- The established kernel of owner k in the extended state gets the World's Beacon kernel of a seed. -/
noncomputable def stepApply (owner : ℕ) (seed : PqxdhRecordLiftSeed.Seed)
    (r : (Option Pqxdh.Bytes × Option Coord) × XState KemSK IdealCore 2) :
    (Option Pqxdh.Bytes × Option Coord) × XState KemSK IdealCore 2 :=
  (r.1, { r.2 with base := { r.2.base with native := { r.2.base.native with
    owners := r.2.base.native.owners.modify owner (setKernelAt seed) } } })

/-- Kernel identity of the ideal registration's finish (with its coordinates reported), on pairs. -/
theorem finishStepC_seed (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (owner : ℕ) (raw : Pqxdh.Bytes)
    (z : XState KemSK IdealCore 2 × (Alloc Coord 2 × (MatCache 2 × SeedCache 2))) :
    (onPair splitService (finishStepC setup codec checks route t p (erasedHidden setup codec checks) created owner
        raw)).run z =
      pairPeek (fun r => r.1.2) (stepApply owner) <$>
        (onPair eagerDummy (finishStepC setup codec checks route t p (erasedHidden setup codec checks) created owner
          raw)).run z := by
  by_cases chosen : z.1.backend.active = true ∧ owner = t.kem.val ∧ initSentAt z.1.base.native.owners owner = true
  · have shape : ∀ x : XState KemSK IdealCore 2,
        (finishHiddenC setup codec p (erasedHidden setup codec checks) owner raw).run x =
          (fun r => (fun x (b : Option Pqxdh.Bytes) (q : PqxdhRegistrationSchedule.State KemSK × Option Coord) =>
            (((b, q.2), assembleF x owner q) : (Option Pqxdh.Bytes × Option Coord) × XState KemSK IdealCore 2)) x r.1
              r.2) <$>
            (finishChallenge setup codec (erasedHidden setup codec checks) p.challenge owner raw).run
              ((fun x : XState KemSK IdealCore 2 => (x.base.native, (none : Option Coord))) x) := fun _ => rfl
    have branch : ∀ svc : SlotService (MatCache 2 × SeedCache 2) 2,
        (onPair svc (finishStepC setup codec checks route t p (erasedHidden setup codec checks) created owner raw)).run z =
          (onPair svc (finishHiddenC setup codec p (erasedHidden setup codec checks) owner raw)).run z := by
      intro svc
      rw [PqxdhDeploymentIdealErase.onPair_run, PqxdhDeploymentIdealErase.onPair_run]
      simp only [finishStepC, StateT.run, ite_eq_left chosen]
    have focused := fun svc : SlotService (MatCache 2 × SeedCache 2) 2 =>
      PqxdhDeploymentIdealErase.onPair_focus svc (finishHiddenC setup codec p (erasedHidden setup codec checks) owner raw)
        (finishChallenge setup codec (erasedHidden setup codec checks) p.challenge owner raw)
        (fun x : XState KemSK IdealCore 2 => (x.base.native, (none : Option Coord)))
        (fun x (b : Option Pqxdh.Bytes) (q : PqxdhRegistrationSchedule.State KemSK × Option Coord) =>
          (((b, q.2), assembleF x owner q) : (Option Pqxdh.Bytes × Option Coord) × XState KemSK IdealCore 2)) shape z
    rw [branch, branch, focused, focused]
    simp only []
    rw [challenge_seed, Functor.map_map, Functor.map_map]
    congr 1
    funext r
    exact pairPeek_map (fun q => ((q.1, q.2.2), assembleF z.1 owner q.2)) (fun r => r.2.2) (fun r => r.1.2)
      (challengeApply owner) (stepApply owner) (fun _ => rfl)
      (fun seed q => by
        simp only [challengeApply, stepApply, assembleF, establishedAt_modify]) r
  · have branch : ∀ svc : SlotService (MatCache 2 × SeedCache 2) 2,
        (onPair svc (finishStepC setup codec checks route t p (erasedHidden setup codec checks) created owner raw)).run z =
          (onPair svc ((fun r => (r, (none : Option Coord))) <$>
            onSlots (realRegAt setup codec route checks created ⟨.finish owner raw, trivial⟩))).run z := by
      intro svc
      rw [PqxdhDeploymentIdealErase.onPair_run, PqxdhDeploymentIdealErase.onPair_run, StateT.run_map]
      simp only [finishStepC, StateT.run, ite_eq_right chosen]
    rw [branch, branch, onPair_map, onPair_map, onPair_onSlots, onPair_onSlots, StateT.run_map, Functor.map_map]
    congr 1

end FinishStepC

section BuildSeed
variable (route : RawCtxServerRouting.SenderDecoder)
open PqxdhDeploymentIdealSteps (buildHidden IdealCore)
open PqxdhDeploymentIdealErase (buildFocus)

/-- The marked build after its value request, unfolded. -/
theorem buildFocus_run (hidden : PqxdhRegistrationJointKemPostSkeleton.Hidden Response) (session : ℕ)
    (payload : Option Pqxdh.Bytes) (coords : Coord) (x : XState KemSK IdealCore 2) :
    (buildFocus hidden session payload coords).run x =
      (fun r => (r.1, { x with
        base := { x.base with native := { x.base.native with shared := r.2 } }
        backend := { x.backend with
          peer := ((PqxdhDeploymentIdealSteps.publishedKey r.1 r.2.2.server).map fun keyId => (keyId, coords)).or
            x.backend.peer } })) <$>
        (buildHidden hidden session payload).run x.base.native.shared := rfl

/-- Putting a kernel on a published peer keeps which build responses name a published peer. -/
theorem publishedKey_peerFix (response : Option PqxdhServerRegistrationPublication.Response)
    (state : PqxdhServerAuthNative.NativeState KemSK) (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) :
    PqxdhDeploymentIdealSteps.publishedKey response (peerFix response state kernel).2.server =
      PqxdhDeploymentIdealSteps.publishedKey response state.2.server := by
  rcases response with _ | response
  · rfl
  · simp only [peerFix, PqxdhDeploymentIdealSteps.publishedKey, PqxdhDeploymentHiddenSplit.setPeerKernel,
      Function.update_self]
    rcases state.2.server.server.peers response.keyId with _ | peer <;> rfl

/-- Kernel identity of the ideal registration's build (with its coordinates reported), on pairs. -/
theorem buildStepC_seed (created : PqxdhLiveServerConstruction.Created Unit) (session : ℕ) (payload : Option Pqxdh.Bytes)
    (z : XState KemSK IdealCore 2 × (Alloc Coord 2 × (MatCache 2 × SeedCache 2))) :
    (onPair splitService (buildStepC setup codec checks route (erasedHidden setup codec checks) created session
        payload)).run z =
      pairPeek (fun r => r.1.2) buildApply <$>
        (onPair eagerDummy (buildStepC setup codec checks route (erasedHidden setup codec checks) created session
          payload)).run z := by
  rcases marked : z.1.backend.marks with _ | ⟨index, coords⟩
  · have branch : ∀ svc : SlotService (MatCache 2 × SeedCache 2) 2,
        (onPair svc (buildStepC setup codec checks route (erasedHidden setup codec checks) created session payload)).run z =
          (onPair svc ((fun r => (r, (none : Option Coord))) <$>
            onSlots (realRegAt setup codec route checks created ⟨.build session payload, trivial⟩))).run z := by
      intro svc
      rw [PqxdhDeploymentIdealErase.onPair_run, PqxdhDeploymentIdealErase.onPair_run, StateT.run_map]
      simp only [buildStepC, StateT.run, marked]
    rw [branch, branch, onPair_map, onPair_map, onPair_onSlots, onPair_onSlots, StateT.run_map, Functor.map_map]
    rfl
  · by_cases chosen : index = session ∧ (z.1.base.native.shared.2.pending session).isSome = true
    · have branch : ∀ svc : SlotService (MatCache 2 × SeedCache 2) 2,
          (onPair svc (buildStepC setup codec checks route (erasedHidden setup codec checks) created session
            payload)).run z =
            (onPair svc (buildHiddenC (erasedHidden setup codec checks) session payload coords)).run z := by
        intro svc
        rw [PqxdhDeploymentIdealErase.onPair_run, PqxdhDeploymentIdealErase.onPair_run]
        simp only [buildStepC, StateT.run, marked, chosen, and_self, ↓reduceIte]
      rw [branch, branch, buildHiddenC, onPair_bind, onPair_bind, StateT.run_bind, StateT.run_bind, onPair_readAt,
        onPair_readAt, slotImpl_eagerDummy, Functor.map_map, bind_map_left, bind_map_left]
      simp only [map_bind]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun p member => ?_
      rw [onPair_onSlots, onPair_onSlots, lift_run, lift_run, StateT.run_map, StateT.run_map, Functor.map_map,
        Functor.map_map, Functor.map_map]
      rcases allocated : p.2.1.1 coords with _ | j
      · congr 1
        funext a
        simp only [StateLens.fst, pairPeek, allocated]
      · have seeded := slotImpl_split_support _ _ p member j allocated
        have native := buildHidden_seed setup codec checks (splitOutput p.1).1 (splitOutput p.1).2 session payload
          z.1.base.native.shared
        rw [PqxdhDeploymentHiddenLayout.join_split] at native
        have same : ∀ value, buildHidden (KemSK := KemSK) (erasedHidden setup codec checks value) session payload =
            buildHidden (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks value) session payload := by
          intro value
          have field : (erasedHidden setup codec checks value).hiddenBuild =
              (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks value).hiddenBuild := rfl
          unfold buildHidden
          rw [field]
        rw [buildFocus_run, buildFocus_run]
        simp only [StateLens.fst, same]
        rw [native, Functor.map_map, Functor.map_map, Functor.map_map]
        congr 1
        funext r
        simp only [pairPeek, allocated, seeded, buildApply, publishedKey_peerFix]
    · have branch : ∀ svc : SlotService (MatCache 2 × SeedCache 2) 2,
          (onPair svc (buildStepC setup codec checks route (erasedHidden setup codec checks) created session
            payload)).run z =
            (onPair svc ((fun r => (r, (none : Option Coord))) <$>
              onSlots (realRegAt setup codec route checks created ⟨.build session payload, trivial⟩))).run z := by
        intro svc
        rw [PqxdhDeploymentIdealErase.onPair_run, PqxdhDeploymentIdealErase.onPair_run, StateT.run_map]
        simp only [buildStepC, StateT.run, marked, chosen, ↓reduceIte]
      rw [branch, branch, onPair_map, onPair_map, onPair_onSlots, onPair_onSlots, StateT.run_map, Functor.map_map]
      rfl

end BuildSeed

end FinishKernel

/-! ### The eager split form with dummy values and seed fixes -/

section EagerSplit
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentIdealSteps (idealProg erasedHidden IdealCore SplitBk splitInit)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealErase (onPair onPair_map)

/-- A slot step run against the allocator in front of a service on the backend's material cache and the extended state's seed table. -/
noncomputable def slotRunX {β : Type} (svc : SlotService (MatCache 2 × SeedCache 2) 2)
    (step : StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) β) : StateT (XState KemSK SplitBk 2) ProbComp β :=
  fun x => (fun r => (r.1, attachX r.2.1 r.2.2.1 r.2.2.2)) <$>
    (onPair svc step).run (detachX x, (x.backend.2.1, (x.backend.1, x.seeds)))

/-- A command of a slot core with the seeds in the extended state is its slot program run by `slotRunX`. -/
theorem slotCoreX_run (prog : PqxdhLiveServerConstruction.Created Unit → SlotProgram KemSK IdealCore 2)
    (svc : SlotService (MatCache 2 × SeedCache 2) 2) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : EnvQuery) : slotCoreX prog svc created query = slotRunX svc (prog created query) := by
  apply StateT.ext
  intro x
  change _ = (fun r => (r.1, attachX r.2.1 r.2.2.1 r.2.2.2)) <$>
    (onPair svc (prog created query)).run (detachX x, (x.backend.2.1, (x.backend.1, x.seeds)))
  rw [PqxdhDeploymentIdealErase.onPair_run, Functor.map_map]
  rfl

/-- A seed fix read without drawing, on the extended state: when `coords` names coordinates that have a slot whose seed is present in the seed table, `apply` puts it in. -/
def xPeek {β : Type} (coords : β × XState KemSK IdealCore 2 → Option Coord)
    (apply : PqxdhRecordLiftSeed.Seed → β × XState KemSK IdealCore 2 → β × XState KemSK IdealCore 2)
    (r : β × XState KemSK SplitBk 2) : β × XState KemSK SplitBk 2 :=
  match coords (r.1, detachX r.2) with
  | none => r
  | some c => match r.2.backend.2.1.1 c with
    | none => r
    | some j => match r.2.seeds j with
      | none => r
      | some seed => ((apply seed (r.1, detachX r.2)).1,
          attachX (apply seed (r.1, detachX r.2)).2 r.2.backend.2.1 (r.2.backend.1, r.2.seeds))

/-- A seed fix on pairs becomes, after attaching, the seed fix on the extended state. -/
theorem attach_pairPeek {β : Type} (coords : β × XState KemSK IdealCore 2 → Option Coord)
    (apply : PqxdhRecordLiftSeed.Seed → β × XState KemSK IdealCore 2 → β × XState KemSK IdealCore 2)
    (coords_seeds : ∀ b y, coords (b, seedPut y ∅) = coords (b, y))
    (apply_seeds : ∀ seed b y, apply seed (b, seedPut y ∅) = Prod.map id (fun y' => seedPut y' ∅) (apply seed (b, y)))
    (r : β × (XState KemSK IdealCore 2 × (Alloc Coord 2 × (MatCache 2 × SeedCache 2)))) :
    (fun r => (r.1, attachX r.2.1 r.2.2.1 r.2.2.2)) (pairPeek coords apply r) =
      xPeek coords apply ((fun r => (r.1, attachX r.2.1 r.2.2.1 r.2.2.2)) r) := by
  rcases r with ⟨b, y, alloc, m, seeds⟩
  have detached : detachX (attachX y alloc (m, seeds)) = seedPut y ∅ := rfl
  dsimp only
  unfold pairPeek xPeek
  simp only [detached, coords_seeds]
  have backAlloc : (attachX y alloc (m, seeds)).backend.2.1 = alloc := rfl
  have backSeeds : (attachX y alloc (m, seeds)).seeds = seeds := rfl
  have backMat : (attachX y alloc (m, seeds)).backend.1 = m := rfl
  simp only [backAlloc, backSeeds, backMat]
  rcases coords (b, y) with _ | c
  · simp only []
  · simp only []
    rcases alloc.1 c with _ | j
    · simp only []
    · simp only []
      rcases seeds j with _ | seed
      · simp only []
      · simp only [apply_seeds]
        rfl

/-- `slotRunX` maps maps to maps. -/
theorem slotRunX_map {β γ : Type} (svc : SlotService (MatCache 2 × SeedCache 2) 2) (f : β → γ)
    (step : StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) β) (x : XState KemSK SplitBk 2) :
    (slotRunX svc (f <$> step)).run x = (fun r => (f r.1, r.2)) <$> (slotRunX svc step).run x := by
  change (fun r => (r.1, attachX r.2.1 r.2.2.1 r.2.2.2)) <$> (onPair svc (f <$> step)).run _ =
    (fun r => (f r.1, r.2)) <$> ((fun r => (r.1, attachX r.2.1 r.2.2.1 r.2.2.2)) <$> (onPair svc step).run _)
  rw [onPair_map, StateT.run_map, Functor.map_map, Functor.map_map]

/-- A kernel identity on pairs becomes one on the extended state. -/
theorem slotRunX_seed {β : Type} (step : StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) β)
    (coords : β × XState KemSK IdealCore 2 → Option Coord)
    (apply : PqxdhRecordLiftSeed.Seed → β × XState KemSK IdealCore 2 → β × XState KemSK IdealCore 2)
    (coords_seeds : ∀ b y, coords (b, seedPut y ∅) = coords (b, y))
    (apply_seeds : ∀ seed b y, apply seed (b, seedPut y ∅) = Prod.map id (fun y' => seedPut y' ∅) (apply seed (b, y)))
    (seeded : ∀ z : XState KemSK IdealCore 2 × (Alloc Coord 2 × (MatCache 2 × SeedCache 2)),
      (onPair splitService step).run z = pairPeek coords apply <$> (onPair eagerDummy step).run z)
    (x : XState KemSK SplitBk 2) :
    (slotRunX splitService step).run x = xPeek coords apply <$> (slotRunX eagerDummy step).run x := by
  change (fun r => (r.1, attachX r.2.1 r.2.2.1 r.2.2.2)) <$> (onPair splitService step).run _ =
    xPeek coords apply <$> ((fun r => (r.1, attachX r.2.1 r.2.2.1 r.2.2.2)) <$> (onPair eagerDummy step).run _)
  rw [seeded, Functor.map_map, Functor.map_map]
  congr 1
  funext r
  exact attach_pairPeek coords apply coords_seeds apply_seeds r

/-- The eager split form of the ideal registration (design-v2 section 5.2, after step 3): the C7-erased slot program in front of the eager service with dummy values (the material and the seed of a slot read at every hidden read, the value returned with the dummy seed), with the marked build and owner k's challenge finish followed by the seed fix that puts the World's kernel of the slot's seed on the published peer and on the established owner. -/
noncomputable def idealSplitEager (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) : RegImpl KemSK SplitBk 2
  | ⟨.build session payload, _⟩ => fun x => (fun r => (r.1.1, r.2)) <$> (xPeek (fun r => r.1.2) buildApply <$>
      (slotRunX eagerDummy (buildStepC setup codec checks route (erasedHidden setup codec checks) created session
        payload)).run x)
  | ⟨.finish owner raw, _⟩ => fun x => (fun r => (r.1.1, r.2)) <$> (xPeek (fun r => r.1.2) (stepApply owner) <$>
      (slotRunX eagerDummy (finishStepC setup codec checks route t p (erasedHidden setup codec checks) created owner
        raw)).run x)
  | query => slotCoreX (idealProg setup codec route checks t p (erasedHidden setup codec checks)) eagerDummy created query

/-- Kernel identities of the ideal registration (design-v2 section 5.2, step 3): the first-touch split form `idealSplitX` is exactly the eager split form with dummy values and seed fixes, command by command. -/
theorem split_kernel (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : EnvQuery) :
    PqxdhDeploymentIdealKeys.idealSplitX setup codec route checks t p created query =
      idealSplitEager setup codec route checks t p created query := by
  rcases query with ⟨command, isEnv⟩
  cases command
  case build session payload =>
    apply StateT.ext
    intro x
    unfold PqxdhDeploymentIdealKeys.idealSplitX
    rw [slotCoreX_run]
    change (slotRunX splitService (PqxdhDeploymentIdealSteps.buildStep setup codec route checks
      (erasedHidden setup codec checks) created session payload)).run x = _
    rw [← buildStepC_fst setup codec checks route, slotRunX_map,
      slotRunX_seed _ _ _ (fun _ _ => rfl) (fun _ _ _ => rfl) (buildStepC_seed setup codec checks route created session
        payload), Functor.map_map]
    change _ = (fun r => (r.1.1, r.2)) <$> (xPeek (fun r => r.1.2) buildApply <$>
      (slotRunX eagerDummy (buildStepC setup codec checks route (erasedHidden setup codec checks) created session
        payload)).run x)
    rw [Functor.map_map]
  case finish owner raw =>
    apply StateT.ext
    intro x
    unfold PqxdhDeploymentIdealKeys.idealSplitX
    rw [slotCoreX_run]
    change (slotRunX splitService (PqxdhDeploymentIdealSteps.finishStep setup codec route checks t p
      (erasedHidden setup codec checks) created owner raw)).run x = _
    rw [← finishStepC_fst setup codec checks route, slotRunX_map,
      slotRunX_seed _ _ _ (fun _ _ => rfl) (fun _ _ _ => rfl) (finishStepC_seed setup codec checks route t p created
        owner raw), Functor.map_map]
    change _ = (fun r => (r.1.1, r.2)) <$> (xPeek (fun r => r.1.2) (stepApply owner) <$>
      (slotRunX eagerDummy (finishStepC setup codec checks route t p (erasedHidden setup codec checks) created owner
        raw)).run x)
    rw [Functor.map_map]
  case accept raw =>
    exact slotCoreX_same _ _ _ (fun j => (eagerDummy_same j).symm) created _
      (acceptStep_ignores setup codec route checks t p created raw)
  case create pin keyId =>
    exact slotCoreX_same _ _ _ (fun j => (eagerDummy_same j).symm) created _ fun _ => Ignores.liftS _
  case bundle owner =>
    exact slotCoreX_same _ _ _ (fun j => (eagerDummy_same j).symm) created _ fun _ => Ignores.liftS _
  case hmac key message =>
    exact slotCoreX_same _ _ _ (fun j => (eagerDummy_same j).symm) created _ fun _ => Ignores.liftS _
  all_goals exact absurd isEnv id

/-- From `CE.idealGame g`'s registration to the eager split form: `PqxdhDeploymentIdealKeys.ideal_to_splitX` with the kernel identities, read through `splitView`. -/
theorem ideal_to_splitEager {A X : Type} (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A) :
    LawEq (outcomeMap PqxdhDeploymentIdealKeys.splitView <$> (gameWith setup codec route PqxdhDeploymentIdealSteps.idealInit
        (PqxdhDeploymentIdealSteps.idealReg setup codec route checks t p) ensureInit identityIndex bounds mode adversary).run
          runtime)
      (outcomeMap PqxdhDeploymentIdealKeys.splitView <$> (gameWith setup codec route splitInit
        (idealSplitEager setup codec route checks t p) ensureInit identityIndex bounds mode adversary).run runtime) := by
  have kernel : PqxdhDeploymentIdealKeys.idealSplitX setup codec route checks t p =
      idealSplitEager setup codec route checks t p := by
    funext created query
    exact split_kernel setup codec route checks t p created query
  rw [← kernel]
  exact PqxdhDeploymentIdealKeys.ideal_to_splitX setup codec route checks t p ensureInit identityIndex bounds mode
    adversary runtime

end EagerSplit

end BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.Ignores.pure' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.Ignores.pure

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.Ignores.bind' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.Ignores.bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.Ignores.map' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.Ignores.map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.Ignores.liftS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.Ignores.liftS

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.Ignores.read' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.Ignores.read

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.IgnoresS.pure' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.IgnoresS.pure

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.IgnoresS.bind' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.IgnoresS.bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.IgnoresS.simulateQ' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.IgnoresS.simulateQ

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.tailCE_ignores' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.tailCE_ignores

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.acceptActive_ignores' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.acceptActive_ignores

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.acceptStep_ignores' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.acceptStep_ignores

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.eagerDummy_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.eagerDummy_same

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.slotImpl_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.slotImpl_same

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.slotCoreX_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.slotCoreX_same

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.settle_replaceRaw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.settle_replaceRaw

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.buildHidden_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.buildHidden_seed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.buildStepC_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.buildStepC_fst

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.query_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.query_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.splitService_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.splitService_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.slotImpl_split_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.slotImpl_split_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.slotImpl_eagerDummy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.slotImpl_eagerDummy

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.pairPeek_map' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.pairPeek_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.onPair_readAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.onPair_readAt

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.nativeCtx_erased_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.nativeCtx_erased_seed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.group_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.group_seed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.lift_run' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.lift_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.onPair_onSlots_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.onPair_onSlots_lift

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.finish_withKernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.finish_withKernel

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.owner_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.owner_seed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.set_modify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.set_modify

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.finishChallenge_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.finishChallenge_branch

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.challenge_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.challenge_seed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.establishedAt_modify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.establishedAt_modify

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.finishStepC_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.finishStepC_fst

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.finishStepC_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.finishStepC_seed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.buildFocus_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.buildFocus_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.publishedKey_peerFix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.publishedKey_peerFix

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.buildStepC_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.buildStepC_seed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.slotCoreX_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.slotCoreX_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.attach_pairPeek' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.attach_pairPeek

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.slotRunX_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.slotRunX_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.slotRunX_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.slotRunX_seed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.split_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.split_kernel

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.ideal_to_splitEager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKernel.ideal_to_splitEager
