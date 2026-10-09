-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant

/-!
# The selected accept after encapsulation through item 2's layers (CE-11b, unit U6, fourth part)

On an active cut, item 2's post-challenge phase first resumes the Server's selected raw accept after the encapsulation (`PqxdhRegistrationJointKemOpaqueResume.resume` with the challenge ciphertext and the challenge marker, under the skeleton's `resumeImpl`), and the CE side runs the ideal registration's steps after encapsulation (`PqxdhDeploymentIdealActive.acceptAfter`) through the first-touch allocator. This module proves that the two agree: item 2's resumption through item 2's service layers is the projection of `acceptAfter`.

- The suffix: `run_free`, `compiled_free` (the candidate-free suffix compiled to the exposed encapsulation interface issues no KEM creation, reveal or decapsulation), `suffix_chain` (under the actual encapsulator and private services it is item 2's annotated native callbacks, as `PqxdhDeploymentIdealPostServer.prefix_chain` for the raw prefix), `annotated_slots`, and `stack_suffix`: through item 2's service layers it is the native callbacks with the Server's seed (`PqxdhDeploymentIdealSteps.prefixNative`), with item 2's view of the router state kept.
- The allocator: `slot_read_cached` (a read with a free slot or at an allocated point leaves the read value stored there).
- The tail: `marksOf` (item 2's mark of a CE mark, with the value stored at its coordinates), `Stored`, `SplitC` (a CE-native program on the native state and the CE mark through the allocator splits against a skeleton program through item 2's table layers, keeping the allocator good and the mark stored), `liftCE`, `liftCE_run`, `splitC_native`, `splitC_pure`, `splitC_bind`, `splitC_bindNative`, and the splits of the challenge-marked root request (`splitC_root`, from the read's support), of the Server's resumed client (`splitC_client`) and of the whole resumed tail (`splitC_tail`).
- `resume_accept`: item 2's resumption from the game state without observers, through item 2's service layers from a prefix pool whose identity slot holds the Server's seed and a good allocator state with a free slot, is `acceptAfter` on the native state through the allocator, projected (the returned session, the game state without observers, item 2's mark as the CE mark with its stored value, the table cache, the allocator and the table).
- Observers: `resumeTail_neverRead`, `tail_clean` and `resume_clean` (the resumption, cleaned of game observers, does not depend on the observers of the game state it starts from), which connect `resume_accept` to item 2's post-challenge phase, which resumes from the game state with its observers.

These are program equalities and support facts. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext MlKemSharedSecret)
open PqxdhDeploymentIdealParams (Target Params)

/-! ### Stateful simulations without a class of requests -/

section Free
variable {ιA ιB σ : Type} {spec : OracleSpec ιA} {target : OracleSpec ιB}

/-- A stateful simulation whose every step issues no request of a class issues none along a whole program. -/
theorem run_free (impl : QueryImpl spec (StateT σ (OracleComp target))) (predicate : ιB → Prop)
    [DecidablePred predicate] (step : ∀ query state, ((impl query).run state).IsQueryBoundP predicate 0) {α : Type}
    (work : OracleComp spec α) (state : σ) : ((simulateQ impl work).run state).IsQueryBoundP predicate 0 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, isQueryBoundP_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [show (0 : ℕ) = 0 + 0 from rfl]
      exact isQueryBoundP_bind (step query state) fun result _ => ih result.1 result.2

end Free

/-! ### The suffix of the selected accept through item 2's layers -/

section Suffix
open PqxdhRegistrationJointServiceCosts (Kind poolClass)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- A program of the Server's native callbacks, compiled to the private services and the exposed encapsulation interface and run by the actual encapsulator, issues no private request of a class other than coins and the static DH. -/
theorem compiled_free (identityIndex : ℕ) (raw : Pqxdh.Bytes) {α : Type}
    (work : OracleComp (PqxdhRegistrationJointServerPrefix.NativeSpec Reader) α) (consumed : List Pqxdh.Bytes)
    (kind : Kind) (nonuniform : kind ≠ .uniform) (notDh : kind ≠ .staticDh) :
    (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
      ((simulateQ (PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw) work).run
        consumed)).IsQueryBoundP (fun query => poolClass (KemSK := KemSK) query = kind) 0 := by
  rw [show PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw =
      PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw ∘ₛ
        PqxdhRegistrationJointServerPrefix.compiler identityIndex from rfl, QueryImpl.simulateQ_compose,
    PqxdhRegistrationJointKemEncapsulation.prefix_program, ← QueryImpl.simulateQ_compose]
  refine run_free _ _ (fun query state => ?_) work consumed
  have step := PqxdhRegistrationJointOpenCosts.prefix_step (KemSK := KemSK) setup codec checks identityIndex query state
    kind nonuniform
  simp only [notDh, false_and, ↓reduceIte] at step
  simpa only [QueryImpl.apply_compose] using step

/-- The Server's native callbacks compiled to the private services and the exposed encapsulation interface, run by the actual encapsulator and the actual private services from a state whose identity slot holds the Server's seed, are the annotated native callbacks (`PqxdhRegistrationJointServerPrefix.annotated`), for every program (as `PqxdhDeploymentIdealPostServer.prefix_chain` for the raw prefix). -/
theorem suffix_chain (seed : PqxdhJointIdentity.IdentitySeed) (identityIndex : ℕ) (raw : Pqxdh.Bytes) {α : Type}
    (work : OracleComp (PqxdhRegistrationJointServerPrefix.NativeSpec Reader) α)
    (pool : PqxdhRegistrationJointPreparation.Pool KemSK) (consumed : List Pqxdh.Bytes)
    (owned : pool.1.seeds[identityIndex]? = some seed) :
    (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          ((simulateQ (PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw) work).run
            consumed))).run pool =
      (fun result => ((result.1, result.2.2), result.2.1)) <$>
        (simulateQ (PqxdhRegistrationJointServerPrefix.annotated setup.joint seed identityIndex
          (PqxdhServerAuthExperiment.serverAux setup codec checks)) work).run (pool, consumed) := by
  rw [show PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw =
      PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw ∘ₛ
        PqxdhRegistrationJointServerPrefix.compiler identityIndex from rfl, QueryImpl.simulateQ_compose,
    PqxdhRegistrationJointKemEncapsulation.prefix_program]
  have chain := PqxdhRegistrationJointOpenBackend.prefix_program setup codec checks
    (simulateQ (PqxdhRegistrationJointServerPrefix.compiler (KemSK := KemSK) identityIndex) work) (pool, consumed)
  rw [PqxdhRegistrationJointServerPrefix.program_source setup (PqxdhServerAuthExperiment.serverAux setup codec checks)
    seed identityIndex work (pool, consumed) owned] at chain
  rw [← chain]
  simp only [PqxdhRegistrationJointOpenBackend.run, Functor.map_map]
  exact (id_map _).symm

/-- The annotated native callbacks keep the identity seeds and the KEM key pairs along a whole program. -/
theorem annotated_slots (seed : PqxdhJointIdentity.IdentitySeed) (identityIndex : ℕ) {α : Type}
    (work : OracleComp (PqxdhRegistrationJointServerPrefix.NativeSpec Reader) α)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK (List Pqxdh.Bytes))
    (result : α × PqxdhRegistrationJointServerPrefix.State KemSK (List Pqxdh.Bytes))
    (member : result ∈ support ((simulateQ (PqxdhRegistrationJointServerPrefix.annotated setup.joint seed identityIndex
      (PqxdhServerAuthExperiment.serverAux setup codec checks)) work).run state)) :
    result.2.1.1.seeds = state.1.1.seeds ∧ result.2.1.2.keys = state.1.2.keys := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, rfl⟩
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨middle, first, rest⟩ := member
      have head := PqxdhRegistrationJointServerPrefix.query_slots setup.joint seed identityIndex
        (PqxdhServerAuthExperiment.serverAux setup codec checks) query state middle first
      have tail := ih middle.1 middle.2 rest
      exact ⟨tail.1.trans head.1, tail.2.trans head.2⟩

end Suffix

/-! ### The suffix through item 2's layers -/

section SuffixStack
open PqxdhDeploymentIdealPostHidden (lowerEC eraseServiceC)
open PqxdhDeploymentIdealPostSim (SlotState)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : ℕ}
  (t : Target count) (p : Params KemSK count)

/-- A program of the Server's native callbacks, compiled to the exposed encapsulation interface and sent by the skeleton to item 2's service layers from the erased router state of a prefix pool whose identity slot holds the Server's seed, is the native callbacks with the seed (`PqxdhDeploymentIdealSteps.prefixNative`), without stopping, with item 2's view of the service state kept. -/
theorem stack_suffix (seed : PqxdhJointIdentity.IdentitySeed) (identityIndex : ℕ) (raw : Pqxdh.Bytes) {α : Type}
    (work : OracleComp (PqxdhRegistrationJointServerPrefix.NativeSpec Reader) α) (consumed : List Pqxdh.Bytes)
    (joint : PqxdhDynamicIdentityPool.SourceState) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) pool)
    (owned : joint.seeds[identityIndex]? = some seed) (tables : PqxdhSecretInputKdf.HmacOracle.QueryCache × SlotState) :
    ((simulateQ (lowerEC setup t p) (simulateQ (PqxdhRegistrationJointKemPostSkeleton.encLift
        (V := PqxdhRegistrationJointKemEntryFactor.Output))
        ((simulateQ (PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw) work).run
          consumed))).run).run (eraseServiceC ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables)) =
      (fun result => (some result, eraseServiceC ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables))) <$>
        (simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec checks seed) work).run consumed := by
  have noCreate : (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
      ((simulateQ (PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw) work).run
        consumed)).IsQueryBoundP (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) 0 := by
    refine (isQueryBoundP_congr_pred (fun query => ?_)).mpr
      (compiled_free setup codec checks identityIndex raw work consumed .kemCreate (by decide) (by decide))
    rw [PqxdhDeploymentIdealPoolSource.isCreate_class]
  have noReveal := compiled_free setup codec checks identityIndex raw work consumed .other (by decide) (by decide)
  have fresh := PqxdhDeploymentIdealPostRequests.fresh_of_noDecaps t.kem.val p.challenge _
    (compiled_free setup codec checks identityIndex raw work consumed .decapsulate (by decide) (by decide))
  rw [PqxdhDeploymentIdealPostFinish.lowerEC_run,
    show PqxdhDeploymentIdealPostSim.eraseService ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables) =
      (PqxdhRegistrationJointKemObserverFree.eraseJoint (joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables)
      from rfl,
    PqxdhDeploymentIdealPostServer.lowerE_enc setup t p _ noCreate noReveal fresh joint pool prefixed tables,
    suffix_chain setup codec checks seed identityIndex raw work (joint, pool) consumed owned,
    ← PqxdhRegistrationJointServerPrefix.program_projection setup.joint seed identityIndex
      (PqxdhServerAuthExperiment.serverAux setup codec checks) work ((joint, pool), consumed)]
  simp only [Functor.map_map]
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  refine bind_congr_of_forall_mem_support _ fun result member => ?_
  have slots := annotated_slots setup codec checks seed identityIndex work ((joint, pool), consumed) result member
  simp only [Function.comp_apply, Prod.map, id_eq, eraseServiceC]
  congr 3
  simp only [PqxdhRegistrationJointKemObserverFree.eraseJoint, PqxdhRegistrationJointKemObserverFree.eraseIdentity,
    PqxdhRegistrationJointKemObserverFree.eraseRouter, PqxdhDeploymentIdealPoolSource.routerOf, slots.1, slots.2]

end SuffixStack

/-! ### A read of the allocator stores its value -/

section Read
open PqxdhRegistrationJointKemSecondEntry (SlotGood cacheOf slotImpl)
open PqxdhDeploymentIdealSlots (Coord)

/-- A value read at a point that is allocated or has a free slot, from a good state, leaves the read value stored at that point. -/
theorem slot_read_cached (point : Coord) (state : PqxdhDeploymentIdealPostSim.SlotState) (good : SlotGood state)
    (room : (state.1.1 point).isSome = true ∨ state.1.2 < 2)
    (result : PqxdhServerAuthKeySchedule.Output × PqxdhDeploymentIdealPostSim.SlotState)
    (member : result ∈ support ((slotImpl PqxdhDeploymentSeedSplit.tableService (.inr point)).run state)) :
    cacheOf result.2 point = some result.1 := by
  obtain ⟨below, unique, free⟩ := good
  rcases found : state.1.1 point with _ | slot
  · have spare : state.1.2 < 2 := by
      rcases room with allocated | spare
      · simp [found] at allocated
      · exact spare
    have empty : state.2.1 ⟨state.1.2, spare⟩ = none := free _ le_rfl
    rw [PqxdhRegistrationJointKemSecondEntry.slot_none _ _ _ found spare] at member
    change result ∈ support ((fun result => (result.1, ((Function.update state.1.1 point (some ⟨state.1.2, spare⟩),
      state.1.2 + 1), result.2))) <$> (PqxdhRecordLiftLazyTable.impl (spec := PqxdhDeploymentSeedSplit.OutputSpec 2)
        ⟨state.1.2, spare⟩).run state.2) at member
    rw [PqxdhRecordLiftLazyTable.run_miss _ _ empty, Functor.map_map, support_map] at member
    obtain ⟨answer, -, rfl⟩ := member
    simp [cacheOf]
  · rw [PqxdhRegistrationJointKemSecondEntry.slot_some _ _ _ _ found] at member
    change result ∈ support ((fun result => (result.1, (state.1, result.2))) <$>
      (PqxdhRecordLiftLazyTable.impl (spec := PqxdhDeploymentSeedSplit.OutputSpec 2) slot).run state.2) at member
    rcases stored : state.2.1 slot with _ | answer
    · rw [PqxdhRecordLiftLazyTable.run_miss _ _ stored, Functor.map_map, support_map] at member
      obtain ⟨answer, -, rfl⟩ := member
      simp [cacheOf, found]
    · rw [PqxdhRecordLiftLazyTable.run_hit _ _ _ stored, map_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      simp [cacheOf, found, stored]

end Read

/-! ### The Server's resumed tail: the CE-native interpreter against item 2's skeleton -/

section Split
open PqxdhRegistrationJointKemPostSkeleton (NGame Marks SkelSpec clean)
open PqxdhRegistrationJointKemEntryFactor (Output)
open PqxdhDeploymentIdealPostSim (SlotState tableLayer)
open PqxdhDeploymentIdealSlots (Coord SlotSpec)
open PqxdhRegistrationJointKemSecondEntry (SlotGood cacheOf slotImpl)
variable {KemSK : Type}

/-- Item 2's mark of a CE mark: the session with the value stored at the mark's coordinates. -/
def marksOf (recorded : Option (ℕ × Coord)) (slots : SlotState) : Marks Output :=
  recorded.bind fun mark => (cacheOf slots mark.2).map fun value => (mark.1, value)

/-- A CE mark whose coordinates hold a stored value. -/
def Stored (recorded : Option (ℕ × Coord)) (slots : SlotState) : Prop :=
  ∀ mark, recorded = some mark → (cacheOf slots mark.2).isSome

/-- A CE-native program on the native state with a recorded mark, through the allocator, splits against a skeleton program through item 2's table layers: from a good allocator state (with a free slot when `room` is set) and a stored mark, the skeleton run from the game state without observers and item 2's mark of the CE mark is the CE run with the observers dropped and the mark read off the final table, and the CE run keeps the allocator good and the mark stored. -/
def SplitC {α : Type}
    (ce : StateT (PqxdhServerAuthNative.NativeState KemSK × Option (ℕ × Coord)) (OracleComp SlotSpec) α)
    (free : NGame KemSK Output α) (room : Bool) : Prop :=
  ∀ (native : PqxdhServerAuthNative.NativeState KemSK) (recorded : Option (ℕ × Coord)) (slots : SlotState),
    SlotGood slots → (room = true → slots.1.2 < 2) → Stored recorded slots →
    (simulateQ tableLayer (free.run (clean native.2, marksOf recorded slots))).run (native.1.cache, slots) =
      (fun z => ((z.1.1, (clean z.1.2.1.2, marksOf z.1.2.2 z.2)), (z.1.2.1.1.cache, z.2))) <$>
        (simulateQ (slotImpl PqxdhDeploymentSeedSplit.tableService) (ce.run (native, recorded))).run slots ∧
    ∀ z ∈ support ((simulateQ (slotImpl PqxdhDeploymentSeedSplit.tableService) (ce.run (native, recorded))).run slots),
      SlotGood z.2 ∧ Stored z.1.2.2 z.2

/-- A native step lifted to the CE state (`PqxdhDeploymentIdealSteps.tailCE`'s form for auxiliary and mutation requests). -/
def liftCE {α : Type} (work : PqxdhServerAuthNative.NativeGame KemSK α) :
    StateT (PqxdhServerAuthNative.NativeState KemSK × Option (ℕ × Coord)) (OracleComp SlotSpec) α :=
  fun s => (fun r => (r.1, (r.2, s.2))) <$> PqxdhDeploymentIdealSteps.liftS (work.run s.1)

/-- A lifted native step runs past the allocator as the native step, with the allocator state and the CE mark kept. -/
theorem liftCE_run {α : Type} (work : PqxdhServerAuthNative.NativeGame KemSK α)
    (native : PqxdhServerAuthNative.NativeState KemSK) (recorded : Option (ℕ × Coord)) (slots : SlotState) :
    (simulateQ (slotImpl PqxdhDeploymentSeedSplit.tableService) ((liftCE work).run (native, recorded))).run slots =
      (fun r => ((r.1, (r.2, recorded)), slots)) <$> work.run native := by
  change (simulateQ (slotImpl PqxdhDeploymentSeedSplit.tableService) ((fun r => (r.1, (r.2, recorded))) <$>
    PqxdhDeploymentIdealSteps.liftS (work.run native))).run slots = _
  rw [simulateQ_map, StateT.run_map, PqxdhDeploymentIdealCut.slotImpl_lift, Functor.map_map]

/-- A native step that splits against a skeleton step at the factored value type (`PqxdhDeploymentIdealPostServer.SplitT`) splits on the CE state, without touching the allocator or the mark. -/
theorem splitC_native {α : Type} (work : PqxdhServerAuthNative.NativeGame KemSK α) (free : NGame KemSK Output α)
    (split : PqxdhDeploymentIdealPostServer.SplitT work free) (room : Bool) : SplitC (liftCE work) free room := by
  intro native recorded slots good _ stored
  refine ⟨?_, fun z member => ?_⟩
  · rw [split native (marksOf recorded slots) slots, liftCE_run, Functor.map_map]
  · rw [liftCE_run, support_map] at member
    obtain ⟨r, -, rfl⟩ := member
    exact ⟨good, stored⟩

/-- Returning a value splits. -/
theorem splitC_pure {α : Type} (value : α) (room : Bool) :
    SplitC (KemSK := KemSK) (pure value) (pure value) room := by
  intro native recorded slots good _ stored
  refine ⟨?_, fun z member => ?_⟩
  · simp only [StateT.run_pure, simulateQ_pure, map_pure]
  · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨good, stored⟩

/-- Splitting is closed under bind with a continuation that needs no free slot. -/
theorem splitC_bind {α β : Type}
    {ce : StateT (PqxdhServerAuthNative.NativeState KemSK × Option (ℕ × Coord)) (OracleComp SlotSpec) α}
    {free : NGame KemSK Output α}
    {next : α → StateT (PqxdhServerAuthNative.NativeState KemSK × Option (ℕ × Coord)) (OracleComp SlotSpec) β}
    {nextFree : α → NGame KemSK Output β} {room : Bool}
    (first : SplitC ce free room) (rest : ∀ value, SplitC (next value) (nextFree value) false) :
    SplitC (ce >>= next) (free >>= nextFree) room := by
  intro native recorded slots good spare stored
  obtain ⟨equation, keeps⟩ := first native recorded slots good spare stored
  refine ⟨?_, fun z member => ?_⟩
  · rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, equation, bind_map_left, StateT.run_bind, simulateQ_bind,
      StateT.run_bind, map_bind]
    refine bind_congr_of_forall_mem_support _ fun middle inner => ?_
    obtain ⟨goodMiddle, storedMiddle⟩ := keeps middle inner
    exact (rest middle.1.1 middle.1.2.1 middle.1.2.2 middle.2 goodMiddle (fun none => by cases none)
      storedMiddle).1
  · rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
    obtain ⟨middle, inner, outer⟩ := member
    obtain ⟨goodMiddle, storedMiddle⟩ := keeps middle inner
    exact (rest middle.1.1 middle.1.2.1 middle.1.2.2 middle.2 goodMiddle (fun none => by cases none)
      storedMiddle).2 z outer

/-- A split native step followed by a split continuation splits, keeping the continuation's need for a free slot. -/
theorem splitC_bindNative {α β : Type} {work : PqxdhServerAuthNative.NativeGame KemSK α} {free : NGame KemSK Output α}
    {next : α → StateT (PqxdhServerAuthNative.NativeState KemSK × Option (ℕ × Coord)) (OracleComp SlotSpec) β}
    {nextFree : α → NGame KemSK Output β} {room : Bool}
    (first : PqxdhDeploymentIdealPostServer.SplitT work free) (rest : ∀ value, SplitC (next value) (nextFree value) room) :
    SplitC (liftCE work >>= next) (free >>= nextFree) room := by
  intro native recorded slots good spare stored
  refine ⟨?_, fun z member => ?_⟩
  · rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, first native (marksOf recorded slots) slots, bind_map_left,
      StateT.run_bind, simulateQ_bind, StateT.run_bind, liftCE_run, bind_map_left, map_bind]
    refine bind_congr fun middle => ?_
    exact (rest middle.1 middle.2 recorded slots good spare stored).1
  · rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, liftCE_run, bind_map_left, mem_support_bind_iff] at member
    obtain ⟨middle, -, outer⟩ := member
    exact (rest middle.1 middle.2 recorded slots good spare stored).2 z outer

/-- The challenge-marked root request of the Server's resumed tail splits, with a free slot: the CE-native interpreter reads the hidden value at the root input's coordinates through the allocator and records the coordinates, item 2's skeleton reads the same value and records it; the read stores the value at the coordinates, so item 2's mark is the CE mark with its stored value. -/
theorem splitC_root {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type} (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks) (index : ℕ)
    (input : PqxdhRegistrationJointKemOpaqueClient.Input Reader) (marker : input.shared = .challenge) :
    SplitC (KemSK := KemSK) (PqxdhDeploymentIdealSteps.tailCE setup.hmac index (.inl (.inl input)))
      (PqxdhRegistrationJointKemPostSkeleton.resumeTail setup.hmac index
        (PqxdhRegistrationJointKemEntryFactor.factoredServices setup codec checks) (.inl (.inl input))) true := by
  intro native recorded slots good spare stored
  have left : (PqxdhDeploymentIdealSteps.tailCE (KemSK := KemSK) setup.hmac index (.inl (.inl input))).run
      (native, recorded) = (do
        let _ ← (SlotSpec.query (.inr (PqxdhDeploymentIdealSteps.coordsOf input)) : OracleComp SlotSpec _)
        pure (PqxdhServerAuthEntryFactor.sentinel, (native, some (index, PqxdhDeploymentIdealSteps.coordsOf input)))) := by
    simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run, marker]
  have right : (PqxdhRegistrationJointKemPostSkeleton.resumeTail (KemSK := KemSK) setup.hmac index
      (PqxdhRegistrationJointKemEntryFactor.factoredServices setup codec checks) (.inl (.inl input))).run
        (clean native.2, marksOf recorded slots) = (do
        let value ← ((SkelSpec Output).query (.inr (.inl (PqxdhDeploymentIdealSteps.coordsOf input))) :
          OracleComp (SkelSpec Output) _)
        pure (PqxdhServerAuthEntryFactor.sentinel, (clean native.2, some (index, value)))) := by
    simp only [PqxdhRegistrationJointKemPostSkeleton.resumeTail, marker, StateT.run]
    rfl
  have room : (slots.1.1 (PqxdhDeploymentIdealSteps.coordsOf input)).isSome = true ∨ slots.1.2 < 2 :=
    Or.inr (spare rfl)
  have readLocal : (PqxdhRegistrationJointKemEntryFactor.publicLocalV Output
      (.inr (.inl (PqxdhDeploymentIdealSteps.coordsOf input)))).run native.1.cache =
      (fun reply => (reply, native.1.cache)) <$> ((PqxdhRegistrationJointKemEntryFactor.EntrySpec Output).query
        (.inr (PqxdhDeploymentIdealSteps.coordsOf input)) : OracleComp (PqxdhRegistrationJointKemEntryFactor.EntrySpec Output) _) :=
    rfl
  have skelSide : (simulateQ tableLayer ((PqxdhRegistrationJointKemPostSkeleton.resumeTail (KemSK := KemSK) setup.hmac index
      (PqxdhRegistrationJointKemEntryFactor.factoredServices setup codec checks) (.inl (.inl input))).run
        (clean native.2, marksOf recorded slots))).run (native.1.cache, slots) =
      (fun pair => ((PqxdhServerAuthEntryFactor.sentinel, (clean native.2, some (index, pair.1))),
        (native.1.cache, pair.2))) <$>
        (slotImpl PqxdhDeploymentSeedSplit.tableService (.inr (PqxdhDeploymentIdealSteps.coordsOf input))).run slots := by
    rw [right, PqxdhDeploymentIdealPostChallenge.tableLayer_flat, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      readLocal, simulateQ_bind, simulateQ_map, simulateQ_spec_query, StateT.run_bind, StateT.run_map]
    simp only [simulateQ_pure, StateT.run_pure, bind_map_left, map_bind, map_pure]
    rw [map_eq_bind_pure_comp]
    rfl
  have ceSide : (simulateQ (slotImpl PqxdhDeploymentSeedSplit.tableService)
      ((PqxdhDeploymentIdealSteps.tailCE (KemSK := KemSK) setup.hmac index (.inl (.inl input))).run (native, recorded))).run
        slots =
      (fun pair => ((PqxdhServerAuthEntryFactor.sentinel, (native, some (index, PqxdhDeploymentIdealSteps.coordsOf input))),
        pair.2)) <$>
        (slotImpl PqxdhDeploymentSeedSplit.tableService (.inr (PqxdhDeploymentIdealSteps.coordsOf input))).run slots := by
    rw [left, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp only [simulateQ_pure, StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def]
  refine ⟨?_, fun z member => ?_⟩
  · rw [skelSide, ceSide, Functor.map_map, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
    refine bind_congr_of_forall_mem_support _ fun pair member => ?_
    have cached := slot_read_cached _ slots good room pair member
    simp only [Function.comp_apply, marksOf, Option.bind_some, cached, Option.map_some]
  · rw [ceSide, support_map] at member
    obtain ⟨pair, inner, rfl⟩ := member
    have cached := slot_read_cached _ slots good room pair inner
    refine ⟨(PqxdhDeploymentIdealPostChallenge.slot_keep _ slots good pair inner).1, fun mark found => ?_⟩
    simp only [Option.some.injEq] at found
    subst found
    simp [cached]

/-- The Server's resumed client (`PqxdhRegistrationJointKemOpaqueClient.client`) on a challenge-marked root input splits, with a free slot. -/
theorem splitC_client {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type} (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks) (index : ℕ) (control : beaconcrypt_core.pqxdh.ServerState)
    (binding : beaconcrypt_core.pqxdh.ServerBinding) (input : PqxdhRegistrationJointKemOpaqueClient.Input Reader)
    (marker : input.shared = .challenge) :
    SplitC (KemSK := KemSK) (simulateQ (PqxdhDeploymentIdealSteps.tailCE setup.hmac index)
        (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward
          (PqxdhRegistrationJointKemOpaqueClient.client control binding input)))
      (simulateQ (PqxdhRegistrationJointKemPostSkeleton.resumeTail setup.hmac index
        (PqxdhRegistrationJointKemEntryFactor.factoredServices setup codec checks))
        (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward
          (PqxdhRegistrationJointKemOpaqueClient.client control binding input))) true := by
  unfold PqxdhRegistrationJointKemOpaqueClient.client
  simp only [simulateQ_bind, simulateQ_spec_query, PqxdhRegistrationJointKemOpaqueTail.forward]
  refine splitC_bindNative (work := PqxdhRegistrationJointKemOpaqueClient.auxiliary KemSK .eraseShared) (free := pure ())
    (PqxdhDeploymentIdealPostServer.splitT_pure ()) fun _ => ?_
  cases accepted : PqxdhRegistrationJointKemOpaqueCore.accept control binding input with
  | ok result =>
      cases result with
      | Err error => exact splitC_pure _ true
      | Ok pair =>
          simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, PqxdhRegistrationJointKemOpaqueTail.forward]
          refine splitC_bind (splitC_root setup codec checks index input marker) fun root => ?_
          refine splitC_bindNative (work := PqxdhRegistrationJointKemOpaqueClient.auxiliary KemSK .eraseInput)
            (free := pure ()) (PqxdhDeploymentIdealPostServer.splitT_pure ()) fun _ => ?_
          refine splitC_bindNative (PqxdhDeploymentIdealPostServer.splitT_consume pair.2.registration_id) fun _ => ?_
          exact splitC_pure _ false
  | fail error => exact splitC_pure _ true
  | div => exact splitC_pure _ true

/-- The Server's resumed tail (`PqxdhRegistrationJointKemOpaqueTail.tail`) at a game state, with a challenge-marked root input if any, splits against the skeleton's tail at the same game state without observers, with a free slot. -/
theorem splitC_tail {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type} (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (state : PqxdhServerAuthExperiment.GameState KemSK)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes)
    (marker : ∀ input, collected.1 = some input → input.shared = .challenge) :
    SplitC (KemSK := KemSK) (simulateQ (PqxdhDeploymentIdealSteps.tailCE setup.hmac state.sessions)
        (PqxdhRegistrationJointKemOpaqueTail.tail setup.serverKeyId publicIdentity state collected))
      (simulateQ (PqxdhRegistrationJointKemPostSkeleton.resumeTail setup.hmac (clean state).sessions
        (PqxdhRegistrationJointKemEntryFactor.factoredServices setup codec checks))
        (PqxdhRegistrationJointKemOpaqueTail.tail setup.serverKeyId publicIdentity (clean state) collected)) true := by
  unfold PqxdhRegistrationJointKemOpaqueTail.tail
  simp only [simulateQ_bind, simulateQ_spec_query]
  refine splitC_bindNative (work := PqxdhServerAuthNative.nativeSet _)
    (PqxdhDeploymentIdealPostServer.splitT_set _ _ rfl) fun _ => ?_
  rcases found : collected.1 with _ | input
  · exact splitC_pure _ true
  · simp only [simulateQ_bind]
    refine splitC_bind (splitC_client setup codec checks state.sessions state.server.control _ input
      (marker input found)) fun returned => ?_
    rcases returned with (_ | token) | error | _
    · exact splitC_pure _ false
    · simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
      refine splitC_bindNative (PqxdhDeploymentIdealPostServer.splitT_modify
        (fun current => { current with pending := Function.update current.pending state.sessions (some token) })
        (fun current => { current with pending := Function.update current.pending state.sessions (some token) })
        fun _ => rfl) fun _ => ?_
      exact splitC_pure _ false
    · exact splitC_pure _ false
    · exact splitC_pure _ false

end Split

/-! ### The selected accept after encapsulation -/

section Resume
open PqxdhRegistrationJointKemPostSkeleton (clean)
open PqxdhRegistrationJointKemEntryFactor (Output factoredServices)
open PqxdhDeploymentIdealPostHidden (lowerEC eraseServiceC)
open PqxdhDeploymentIdealPostSim (SlotState)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : ℕ}
  (t : Target count) (p : Params KemSK count)

/-- The selected accept's steps after encapsulation through item 2's layers: item 2's resumption of the Server (`PqxdhRegistrationJointKemOpaqueResume.resume` with the challenge ciphertext and marker under the skeleton's `resumeImpl`), from the game state without observers and item 2's view of a prefix pool whose identity slot holds the Server's seed, a good allocator state with a free slot, runs without stopping as the ideal registration's steps after encapsulation (`PqxdhDeploymentIdealActive.acceptAfter`) on the native state through the allocator, projected: the returned session, the game state without observers, item 2's mark as the CE mark with its stored value, item 2's view of the router state kept, and the table cache, the allocator and the table the CE's. -/
theorem resume_accept (seed : PqxdhJointIdentity.IdentitySeed) (identityIndex : ℕ) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (logged : Option PqxdhJointGapDh.ScalarBytes) (native : PqxdhServerAuthNative.NativeState KemSK)
    (joint : PqxdhDynamicIdentityPool.SourceState) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) pool)
    (owned : joint.seeds[identityIndex]? = some seed) (slots : SlotState)
    (good : PqxdhRegistrationJointKemSecondEntry.SlotGood slots) (room : slots.1.2 < 2) :
    ((simulateQ (lowerEC setup t p) ((simulateQ (PqxdhRegistrationJointKemPostSkeleton.resumeImpl setup.hmac
        (clean native.2).sessions (factoredServices setup codec checks))
        (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks identityIndex (setup.joint.publicKeys seed) raw
          value ephemeral (PqxdhAcceptedRegistration.ciphertextArray p.challenge) .challenge (clean native.2)
          consumed)).run (clean native.2, none))).run).run
        (eraseServiceC ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), (native.1.cache, slots))) =
      (fun w => (some (w.1.1.1.1, (clean w.1.2.2, marksOf w.1.1.2.2 w.2)),
          eraseServiceC ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), (w.1.2.1.cache, w.2)))) <$>
        (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
          ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks seed p.challenge value ephemeral consumed
            logged).run native)).run slots := by
  unfold PqxdhRegistrationJointKemOpaqueResume.resume PqxdhRegistrationJointKemOpaqueSuffix.compiled
  rw [simulateQ_bind, StateT.run_bind, PqxdhRegistrationJointKemEntryFactor.resume_prefix_run, bind_map_left,
    simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind,
    stack_suffix setup codec checks t p seed identityIndex raw _ consumed joint pool prefixed owned (native.1.cache, slots),
    bind_map_left]
  simp only [Option.elim_some]
  have ceAccept : (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
      ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks seed p.challenge value ephemeral consumed
        logged).run native)).run slots =
      (simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec checks seed)
        (PqxdhRegistrationJointKemOpaqueSuffix.program (Shared := PqxdhBeaconPhase2Preparation.Word32) value ephemeral
          (PqxdhAcceptedRegistration.ciphertextArray p.challenge) .challenge)).run consumed >>= fun prepared =>
        (fun z => ((((z.1.1, logged), (true, z.1.2.2)), z.1.2.1), z.2)) <$>
          (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
            ((simulateQ (PqxdhDeploymentIdealSteps.tailCE setup.hmac native.2.sessions)
              (PqxdhRegistrationJointKemOpaqueTail.tail setup.serverKeyId (setup.joint.publicKeys seed) native.2
                prepared)).run (native, none))).run slots := by
    change (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
      (PqxdhDeploymentIdealSteps.liftS _ >>= _)).run slots = _
    rw [simulateQ_bind, StateT.run_bind, PqxdhDeploymentIdealCut.slotImpl_lift, bind_map_left]
    refine bind_congr fun prepared => ?_
    rw [simulateQ_bind, StateT.run_bind]
    simp only [simulateQ_pure, StateT.run_pure]
    rw [map_eq_bind_pure_comp]
    rfl
  rw [ceAccept, map_bind]
  refine bind_congr_of_forall_mem_support _ fun prepared member => ?_
  have marker := PqxdhDeploymentIdealKeymatch.program_marker _ value ephemeral
    (PqxdhAcceptedRegistration.ciphertextArray p.challenge) .challenge consumed prepared member
  rw [PqxdhRegistrationJointKemEntryFactor.resume_tail_run,
    show ∀ (work : PqxdhRegistrationJointKemPostSkeleton.NGame KemSK Output (Option ℕ))
      (state : PqxdhRegistrationJointKemPostSkeleton.SkelState KemSK Output),
      (PqxdhRegistrationJointKemPostSkeleton.liftT work).run state =
        simulateQ (PqxdhRegistrationJointKemPostSkeleton.fwd (T := PqxdhRegistrationJointKemPostSkeleton.TSpec Output)
          (PqxdhRegistrationJointKemPostSkeleton.coinLift (KemSK := KemSK))) (work.run state) from fun _ _ => rfl,
    PqxdhDeploymentIdealPostHidden.lowerEC_native,
    show ((clean native.2, none) : PqxdhRegistrationJointKemPostSkeleton.SkelState KemSK Output) =
      (clean native.2, marksOf none slots) from rfl,
    (splitC_tail setup codec checks (setup.joint.publicKeys seed) native.2 prepared marker native none slots good
      (fun _ => room) (fun mark none => by cases none)).1,
    Functor.map_map, Functor.map_map]
  rfl

end Resume

/-! ### The resumption does not read the game observers -/

section Clean
open PqxdhRegistrationJointKemPostSkeleton (clean)
open PqxdhDeploymentIdealPostItem (cleanSkel GhostFree)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response V : Type}

/-- The skeleton's resumed tail never reads the analysis observers of the game state. -/
theorem resumeTail_neverRead (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (services : PqxdhRegistrationJointKemPostSkeleton.Services V Response) :
    PqxdhRegistrationJointKemObserverFree.NeverRead cleanSkel
      (PqxdhRegistrationJointKemPostSkeleton.resumeTail (KemSK := KemSK) (Reader := Reader) hmac index services) := by
  intro query state
  rcases query with (input | auxiliary) | mutation
  · simp only [PqxdhRegistrationJointKemPostSkeleton.resumeTail]
    cases input.shared <;> dsimp only
    · exact PqxdhDeploymentIdealPostItem.ghostFree_bind _ _ (PqxdhDeploymentIdealPostItem.ghostFree_valueRead _)
        (fun value => PqxdhDeploymentIdealPostItem.ghostFree_bind _ _ (PqxdhDeploymentIdealPostItem.ghostFree_mark _ _)
          fun _ => PqxdhDeploymentIdealPostItem.ghostFree_pure _) state
    · exact PqxdhDeploymentIdealPostItem.ghostFree_bind _ _ (PqxdhDeploymentIdealPostItem.ghostFree_tableRead _)
        (fun _ => PqxdhDeploymentIdealPostItem.ghostFree_pure _) state
  · rcases auxiliary with _ | _ | rid
    · exact PqxdhDeploymentIdealPostItem.ghostFree_pure _ state
    · exact PqxdhDeploymentIdealPostItem.ghostFree_pure _ state
    · exact PqxdhDeploymentIdealPostItem.ghostFree_modifyGame
        (fun game => { game with server := { game.server with consumed := game.server.consumed ++ [PqxdhRefinement.absBytes rid.bytes] } })
        (fun _ => rfl) state
  · rcases mutation with game | ⟨slot, token⟩
    · exact PqxdhDeploymentIdealPostItem.ghostFree_setGame game state
    · exact PqxdhDeploymentIdealPostItem.ghostFree_modifyGame
        (fun current => { current with pending := Function.update current.pending slot (some token) }) (fun _ => rfl)
        state

/-- The skeleton's resumed tail on a game state, cleaned of observers, does not depend on the observers of that game state. -/
theorem tail_clean (hmac : PqxdhSecretInputKdf.HmacSha512) (services : PqxdhRegistrationJointKemPostSkeleton.Services V Response)
    (serverKeyId : Std.U64) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (game : PqxdhServerAuthExperiment.GameState KemSK)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes)
    (state : PqxdhRegistrationJointKemPostSkeleton.SkelState KemSK V)
    (state' : PqxdhRegistrationJointKemPostSkeleton.SkelState KemSK V) (marks : state'.2 = state.2) :
    Prod.map id cleanSkel <$> (simulateQ (PqxdhRegistrationJointKemPostSkeleton.resumeTail hmac game.sessions services)
        (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity game collected)).run state =
      Prod.map id cleanSkel <$> (simulateQ (PqxdhRegistrationJointKemPostSkeleton.resumeTail hmac (clean game).sessions
        services) (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity (clean game) collected)).run
          state' := by
  rw [PqxdhRegistrationJointKemObserverFree.run_erase cleanSkel PqxdhDeploymentIdealPostItem.cleanSkel_idem _
      (resumeTail_neverRead hmac game.sessions services),
    PqxdhRegistrationJointKemObserverFree.run_erase cleanSkel PqxdhDeploymentIdealPostItem.cleanSkel_idem _
      (resumeTail_neverRead hmac (clean game).sessions services)]
  unfold PqxdhRegistrationJointKemOpaqueTail.tail
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  simp only [PqxdhRegistrationJointKemObserverFree.eraseImpl, PqxdhRegistrationJointKemPostSkeleton.resumeTail,
    PqxdhRegistrationJointKemPostSkeleton.setGame, StateT.run, map_pure, cleanSkel, Prod.map, id_eq, marks]
  rfl

/-- The Server's resumption through the skeleton's native layer, cleaned of game observers, does not depend on the observers of the game state it starts from and resumes. -/
theorem resume_clean {ι : Type} {baseSpec : OracleSpec ι} (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks) (services : PqxdhRegistrationJointKemPostSkeleton.Services V Response)
    (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (game : PqxdhServerAuthExperiment.GameState KemSK)
    (consumed : List Pqxdh.Bytes) (marks : PqxdhRegistrationJointKemPostSkeleton.Marks V) :
    Prod.map id cleanSkel <$> (simulateQ (PqxdhRegistrationJointKemPostSkeleton.resumeImpl setup.hmac game.sessions services)
        (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks identityIndex publicIdentity raw value ephemeral
          ciphertext .challenge game consumed)).run (game, marks) =
      Prod.map id cleanSkel <$> (simulateQ (PqxdhRegistrationJointKemPostSkeleton.resumeImpl setup.hmac
        (clean game).sessions services) (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks identityIndex
          publicIdentity raw value ephemeral ciphertext .challenge (clean game) consumed)).run (clean game, marks) := by
  unfold PqxdhRegistrationJointKemOpaqueResume.resume
  simp only [simulateQ_bind, StateT.run_bind, PqxdhRegistrationJointKemEntryFactor.resume_prefix_run, bind_map_left,
    map_bind]
  refine bind_congr fun collected => ?_
  rw [PqxdhRegistrationJointKemEntryFactor.resume_tail_run, PqxdhRegistrationJointKemEntryFactor.resume_tail_run]
  change Prod.map id cleanSkel <$> simulateQ _ _ = Prod.map id cleanSkel <$> simulateQ _ _
  rw [← simulateQ_map, ← simulateQ_map, tail_clean setup.hmac services setup.serverKeyId publicIdentity game collected
    (game, marks) (clean game, marks) rfl]

end Clean

end BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.run_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.run_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.compiled_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.compiled_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.suffix_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.suffix_chain

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.annotated_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.annotated_slots

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.stack_suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.stack_suffix

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.slot_read_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.slot_read_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.liftCE_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.liftCE_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.splitC_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.splitC_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.splitC_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.splitC_pure

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.splitC_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.splitC_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.splitC_bindNative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.splitC_bindNative

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.splitC_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.splitC_root

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.splitC_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.splitC_client

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.splitC_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.splitC_tail

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.resume_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.resume_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.resumeTail_neverRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.resumeTail_neverRead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.tail_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.tail_clean

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.resume_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept.resume_clean
