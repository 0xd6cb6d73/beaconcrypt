-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer

/-!
# Item 2's view without table counters, and the marked build (CE-11b, unit U6, third part)

The ideal registration's marked build (`PqxdhDeploymentIdealSteps.buildStep`) re-reads the mark's value through the first-touch allocator and item 2's persistent lazy table, an allocator hit; `PqxdhRecordLiftLazyTable.run_hit` charges one table lookup for it. Item 2's skeleton reads the mark's value from its marks and does not touch the table. Item 2's view of the middle state `PqxdhDeploymentIdealPostSteps.encodeMid` keeps the whole table state with its counters, so the two runs differ there by one lookup. The counters are accounting observers that no step reads; this module erases them from item 2's view, carries every step proved at the old view over, and proves the marked build at the new view.

- Counters are never read: the lazy table (`table_neverRead`), the allocator in front of it (`slot_neverRead`, `eraseCounts`), item 2's table layers (`tableLayer_neverRead`, `eraseTables`, through `tableLayer_run`) and the lower service layers (`lower_neverRead`); `run_neverRead` lifts a single-step fact to programs, and `optionLower_neverRead_both` combines an observer of the optional layer with one of the interpreter below it.
- The view: `eraseServiceC` erases the router transcripts and the table counters (`serviceLayer_neverReadC`), `lowerEC` is item 2's service layers with both erasures, `encodeMidC` is `encodeMid` with the counters erased and `StepAtC` is `sim_option`'s step at this view. `stepAtC_of_stepAt` carries every step at the old view (`PqxdhDeploymentIdealPostSteps`, `PqxdhDeploymentIdealPostRequests`, `PqxdhDeploymentIdealPostServer`) to the new one. `itemPost_erasedC` states item 2's post-challenge phase with both erasures, in the form the assembly uses.
- The marked build: the middle source handler answers it by the ideal registration (`idealMid_run`, `buildStep_hidden_run`, `sourceMid_build_hidden` with `afterBuild` and `rejoin_source`), with the value stored at the mark's allocated slot; item 2's build runs the factored response tail at the mark's value (`lowerEC_native`, `skelMarks_afterBuild`), and `step_build_hidden` proves `StepAtC` for it when the allocator and the table hold the mark's value.

These are program equalities. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext)
open PqxdhRegistrationJointKemPostSkeleton (Enc TSpec SkelSpec SkelState fwd fwdOption coinLift clean evalLayer)
open PqxdhRegistrationJointKemEntryFactor (Output factoredServices publicLocalV)
open PqxdhDeploymentIdealPostSim (SlotState ServiceState tableLayer serviceLayer upperLayer eraseService optionLower)
open PqxdhDeploymentIdealPostSource (Mid sourceMid)
open PqxdhDeploymentIdealPostSteps (encodeMid upperE lowerE StepAt)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhRegistrationJointKemObserverFree (NeverRead NeverReadOption eraseImpl eraseOptionImpl run_erase run_eraseOption)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-! ### The table counters are never read -/

section Counts
open PqxdhRecordLiftLazyTable (Counts)

/-- A lazy table state with its counters erased. -/
def eraseTable {ι' : Type} {spec : OracleSpec ι'} (state : PqxdhRecordLiftLazyTable.State spec) :
    PqxdhRecordLiftLazyTable.State spec :=
  (state.1, ⟨0, 0⟩)

/-- The persistent lazy table never reads its counters. -/
theorem table_neverRead {ι' : Type} [DecidableEq ι'] {spec : OracleSpec ι'} [∀ t : spec.Domain, SampleableType (spec.Range t)] :
    NeverRead (eraseTable (spec := spec)) (PqxdhRecordLiftLazyTable.impl (spec := spec)) := by
  intro query state
  rcases found : state.1 query with _ | answer
  · rw [PqxdhRecordLiftLazyTable.run_miss _ _ found,
      PqxdhRecordLiftLazyTable.run_miss (s := eraseTable state) _ (by simpa [eraseTable] using found),
      Functor.map_map, Functor.map_map]
    rfl
  · rw [PqxdhRecordLiftLazyTable.run_hit _ _ _ found,
      PqxdhRecordLiftLazyTable.run_hit (s := eraseTable state) _ _ (by simpa [eraseTable] using found)]
    rfl

/-- A stateful handler that never reads some observers keeps their erasure along whole programs: the erased result of a run depends only on the erased start. -/
theorem run_neverRead {ι' σ : Type} {spec : OracleSpec ι'} (erase : σ → σ) (idem : ∀ state, erase (erase state) = erase state)
    (impl : QueryImpl spec (StateT σ ProbComp)) (never : NeverRead erase impl) {α : Type} (work : OracleComp spec α)
    (state : σ) :
    Prod.map id erase <$> (simulateQ impl work).run state = Prod.map id erase <$> (simulateQ impl work).run (erase state) := by
  rw [run_erase erase idem impl never, run_erase erase idem impl never, idem]

/-- The slot state with the table counters erased. -/
def eraseCounts (slots : SlotState) : SlotState := (slots.1, eraseTable slots.2)

/-- The first-touch allocator in front of item 2's table never reads the table counters. -/
theorem slot_neverRead :
    NeverRead eraseCounts (PqxdhRegistrationJointKemSecondEntry.slotImpl (D := PqxdhCorrelatedExtractFamily.Message)
      (PqxdhRegistrationJointKemSecondEntry.tableService (n := 2) (R := Output))) := by
  intro query state
  rcases query with coin | point
  · rw [PqxdhRegistrationJointKemSecondEntry.slot_coin, PqxdhRegistrationJointKemSecondEntry.slot_coin,
      Functor.map_map, Functor.map_map]
    rfl
  · rcases found : state.1.1 point with _ | slot
    · by_cases room : state.1.2 < 2
      · rw [PqxdhRegistrationJointKemSecondEntry.slot_none _ _ _ found room,
          PqxdhRegistrationJointKemSecondEntry.slot_none (state := eraseCounts state) _ _ found room]
        have inner := table_neverRead (spec := PqxdhRecordLiftInterface.Slot 2 →ₒ Output) ⟨state.1.2, room⟩ state.2
        have mapped := congrArg (fun work => (fun result : Output × PqxdhRecordLiftLazyTable.State
          (PqxdhRecordLiftInterface.Slot 2 →ₒ Output) => (result.1, ((Function.update state.1.1 point
            (some ⟨state.1.2, room⟩), state.1.2 + 1), result.2))) <$> work) inner
        simp only [Functor.map_map] at mapped
        simp only [Functor.map_map]
        exact mapped
      · have left : (PqxdhRegistrationJointKemSecondEntry.slotImpl (D := PqxdhCorrelatedExtractFamily.Message)
            (PqxdhRegistrationJointKemSecondEntry.tableService (n := 2) (R := Output)) (.inr point)).run state =
            (fun answer => (answer, state)) <$> ($ᵗ Output) := by
          simp only [PqxdhRegistrationJointKemSecondEntry.slotImpl, QueryImpl.add_apply_inr, StateT.run_mk, found, room,
            _root_.dite_false]
        have right : (PqxdhRegistrationJointKemSecondEntry.slotImpl (D := PqxdhCorrelatedExtractFamily.Message)
            (PqxdhRegistrationJointKemSecondEntry.tableService (n := 2) (R := Output)) (.inr point)).run
              (eraseCounts state) = (fun answer => (answer, eraseCounts state)) <$> ($ᵗ Output) := by
          simp only [PqxdhRegistrationJointKemSecondEntry.slotImpl, QueryImpl.add_apply_inr, StateT.run_mk, eraseCounts,
            found, room, _root_.dite_false]
        rw [left, right, Functor.map_map, Functor.map_map]
        rfl
    · rw [PqxdhRegistrationJointKemSecondEntry.slot_some _ _ _ _ found,
        PqxdhRegistrationJointKemSecondEntry.slot_some (state := eraseCounts state) _ _ _ found]
      have inner := table_neverRead (spec := PqxdhRecordLiftInterface.Slot 2 →ₒ Output) slot state.2
      have mapped := congrArg (fun work => (fun result : Output × PqxdhRecordLiftLazyTable.State
        (PqxdhRecordLiftInterface.Slot 2 →ₒ Output) => (result.1, (state.1, result.2))) <$> work) inner
      simp only [Functor.map_map] at mapped
      simp only [Functor.map_map]
      exact mapped

/-- The table layers' state with the table counters erased. -/
def eraseTables (state : PqxdhSecretInputKdf.HmacOracle.QueryCache × SlotState) :
    PqxdhSecretInputKdf.HmacOracle.QueryCache × SlotState :=
  (state.1, eraseCounts state.2)

/-- One step of the table layers: item 2's public-table layer on the public cache, then the allocator and the table on the slot state. -/
theorem tableLayer_run (query : (SkelSpec Output).Domain) (state : PqxdhSecretInputKdf.HmacOracle.QueryCache × SlotState) :
    (tableLayer query).run state =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl (D := PqxdhCorrelatedExtractFamily.Message)
          (PqxdhRegistrationJointKemSecondEntry.tableService (n := 2) (R := Output)))
          ((publicLocalV Output query).run state.1)).run state.2 := rfl

/-- The table layers never read the table counters. -/
theorem tableLayer_neverRead : NeverRead eraseTables tableLayer := by
  intro query state
  rw [tableLayer_run, tableLayer_run, Functor.map_map, Functor.map_map]
  have slots := run_neverRead eraseCounts (fun _ => rfl) _ slot_neverRead ((publicLocalV Output query).run state.1)
    state.2
  have mapped := congrArg (fun work => (fun result : ((SkelSpec Output).Range query ×
    PqxdhSecretInputKdf.HmacOracle.QueryCache) × SlotState => (result.1.1, (result.1.2, result.2))) <$> work) slots
  simp only [Functor.map_map] at mapped
  exact mapped

/-- The lower service layers (the CCA evaluation forwarding the table oracles, then the table layers) never read the table counters. -/
theorem lower_neverRead (setup : Setup baseSpec KemSK) (secret : KemSK) (challenge : MlKem768Ciphertext) :
    NeverRead eraseTables (tableLayer ∘ₛ fwd (T := TSpec Output) (evalLayer setup secret challenge)) := by
  intro query state
  simp only [QueryImpl.apply_compose]
  rw [run_neverRead eraseTables (fun _ => rfl) tableLayer tableLayer_neverRead]

end Counts

/-! ### Erasing both observers of the service layers -/

section Both
variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {J K : Type}

/-- An optional stateful layer followed by a stateful interpreter never reads the product of observers that each of them never reads. -/
theorem optionLower_neverRead_both (layer : QueryImpl spec₁ (OptionT (StateT J (OracleComp spec₂))))
    (lower : QueryImpl spec₂ (StateT K ProbComp)) (eraseJ : J → J) (eraseK : K → K)
    (idemK : ∀ state, eraseK (eraseK state) = eraseK state)
    (neverJ : NeverReadOption eraseJ layer) (neverK : NeverRead eraseK lower) :
    NeverReadOption (Prod.map eraseJ eraseK) (optionLower layer lower) := by
  intro query state
  simp only [optionLower, OptionT.run_mk, StateT.run_mk, Functor.map_map]
  show (fun result : (Option (spec₁.Range query) × J) × K => (result.1.1, (eraseJ result.1.2, eraseK result.2))) <$>
      (simulateQ lower (((layer query).run).run state.1)).run state.2 =
    (fun result : (Option (spec₁.Range query) × J) × K => (result.1.1, (eraseJ result.1.2, eraseK result.2))) <$>
      (simulateQ lower (((layer query).run).run (eraseJ state.1))).run (eraseK state.2)
  have lowered := run_neverRead eraseK idemK lower neverK (((layer query).run).run state.1) state.2
  have mappedK := congrArg (fun work => (fun result : (Option (spec₁.Range query) × J) × K =>
    (result.1.1, (eraseJ result.1.2, result.2))) <$> work) lowered
  simp only [Functor.map_map, Prod.map_fst, Prod.map_snd, id_eq] at mappedK
  rw [mappedK]
  have upper := congrArg (fun work => (simulateQ lower work).run (eraseK state.2)) (neverJ query state.1)
  simp only [simulateQ_map, StateT.run_map] at upper
  have mappedJ := congrArg (fun work => (fun result : (Option (spec₁.Range query) × J) × K =>
    (result.1.1, (result.1.2, eraseK result.2))) <$> work) upper
  simp only [Functor.map_map, Prod.map_fst, Prod.map_snd, id_eq] at mappedJ
  exact mappedJ

end Both

/-! ### Item 2's view with the table counters erased -/

section View

/-- A service state with the router transcripts and the table counters erased. -/
def eraseServiceC (state : ServiceState KemSK) : ServiceState KemSK :=
  Prod.map PqxdhRegistrationJointKemObserverFree.eraseJoint eraseTables state

/-- Erasing the router transcripts and the table counters is idempotent. -/
theorem eraseServiceC_idem (state : ServiceState KemSK) : eraseServiceC (eraseServiceC state) = eraseServiceC state := by
  simp only [eraseServiceC, Prod.map, PqxdhRegistrationJointKemObserverFree.eraseJoint_idem]
  rfl

/-- Erasing the counters after the transcripts is erasing both. -/
theorem eraseServiceC_eraseService (state : ServiceState KemSK) :
    eraseServiceC (eraseService state) = eraseServiceC state := by
  simp only [eraseServiceC, eraseService, Prod.map, PqxdhRegistrationJointKemObserverFree.eraseJoint_idem, id_eq]

/-- The service layers never read the router transcripts nor the table counters. -/
theorem serviceLayer_neverReadC (setup : Setup baseSpec KemSK) {count : ℕ} (selected : Fin (count + 1))
    (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK)
    (challenge : MlKem768Ciphertext) :
    NeverReadOption eraseServiceC (serviceLayer setup selected chosen others challenge) :=
  optionLower_neverRead_both _ _ PqxdhRegistrationJointKemObserverFree.eraseJoint eraseTables (fun _ => rfl)
    (PqxdhDeploymentIdealPostSim.compose_neverRead _ _ _ PqxdhRegistrationJointKemObserverFree.eraseJoint_idem
      (PqxdhDeploymentIdealPostSim.fwdOption_neverRead _ _ PqxdhRegistrationJointKemObserverFree.eraseJoint_idem
        (PqxdhRegistrationJointKemObserverFree.post_neverRead _ _ _ _ _ _)))
    (lower_neverRead setup chosen.2 challenge)

variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- Item 2's service layers with the router transcripts and the table counters erased. -/
noncomputable abbrev lowerEC :=
  eraseOptionImpl eraseServiceC (serviceLayer setup t.kem p.chosen p.others p.challenge)

/-- Item 2's view of a middle state with the table counters erased as well. -/
def encodeMidC (m : Mid KemSK) :
    (List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × SkelState KemSK Output) × ServiceState KemSK :=
  ((encodeMid setup m).1, eraseServiceC (encodeMid setup m).2)

/-- `StepAt` at item 2's view without table counters. -/
def StepAtC (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (m : Mid KemSK) : Prop :=
  ((simulateQ (lowerEC setup t p) ((upperE setup codec checks t p created query).run (encodeMidC setup m).1)).run).run
      (encodeMidC setup m).2 =
    (fun result => (some (result.1, (encodeMidC setup result.2).1), (encodeMidC setup result.2).2)) <$>
      (sourceMid setup codec route checks t p created query).run m

/-- Every step at item 2's view is a step at the view without table counters. -/
theorem stepAtC_of_stepAt (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (m : Mid KemSK)
    (step : StepAt setup codec route checks t p created query m) :
    StepAtC setup codec route checks t p created query m := by
  unfold StepAt at step
  unfold StepAtC
  have counted := run_eraseOption eraseServiceC eraseServiceC_idem _
    (serviceLayer_neverReadC setup t.kem p.chosen p.others p.challenge)
    ((upperE setup codec checks t p created query).run (encodeMid setup m).1) (encodeMid setup m).2
  have erased := run_eraseOption eraseService
    (fun state => by simp only [eraseService, Prod.map, PqxdhRegistrationJointKemObserverFree.eraseJoint_idem, id_eq])
    _ (PqxdhDeploymentIdealPostSim.serviceLayer_neverRead setup t.kem p.chosen p.others p.challenge)
    ((upperE setup codec checks t p created query).run (encodeMid setup m).1) (encodeMid setup m).2
  rw [PqxdhDeploymentIdealPostSteps.encodeMid_erased] at erased
  change _ = ((simulateQ (lowerE setup t p) _).run).run (encodeMid setup m).2 at erased
  change ((simulateQ (lowerEC setup t p) ((upperE setup codec checks t p created query).run
    (encodeMid setup m).1)).run).run (eraseServiceC (encodeMid setup m).2) = _
  have key := congrArg (fun work => Prod.map id eraseServiceC <$> work) erased
  have comp : ∀ {α : Type} (result : α × ServiceState KemSK),
      Prod.map id eraseServiceC (Prod.map id eraseService result) = Prod.map id eraseServiceC result :=
    fun result => by simp only [Prod.map, id_eq, eraseServiceC_eraseService]
  simp only [Functor.map_map, comp] at key
  rw [← counted, key, step, Functor.map_map]
  rfl

/-- Item 2's post-challenge phase on a pending prechallenge context whose verified PQ key is the selected one, with the router transcripts and the table counters erased after every step (`eraseServiceC`): the skeleton's decision reads neither. -/
theorem itemPost_erasedC {A Y : Type} (decision : Y × PqxdhDeploymentCompile.Local → Bool)
    (createdC : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (others : Fin count → MlKem768PublicKey × KemSK)
    (raw : Pqxdh.Bytes) (value : PqxdhServerRootPreparation.Verified Reader) (matched : value.keys.pqKey = p.chosen.1)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (native : PqxdhServerAuthNative.NativeState KemSK)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry)
    (next : Option ℕ → OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) (Y × PqxdhDeploymentCompile.Local))
    (state : PqxdhDynamicKemJointSource.State KemSK) (after : A) :
    PqxdhDeploymentIdealBranch.itemPost setup codec checks t p decision
        (.ready createdC others (some (.pending raw value ephemeral consumed native owners next)) state after) =
      PqxdhRegistrationJointKemPostSkeleton.skelDecide <$> ((simulateQ (eraseOptionImpl eraseServiceC
          (serviceLayer setup t.kem p.chosen others p.challenge))
        (PqxdhRegistrationJointKemPostSkeleton.skelResume setup codec checks createdC.server.server.metadata.identityIndex
          createdC.publicIdentity (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw value ephemeral consumed
          native.2 owners next t.kem.val p.challenge (factoredServices setup codec checks))).run).run
        (PqxdhRegistrationJointKemObserverFree.eraseJoint state,
          (native.1.cache, (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial))) := by
  rw [PqxdhDeploymentIdealPostSim.itemPost_active setup codec checks t p decision createdC others raw value matched
    ephemeral consumed native owners next state after]
  have erased := run_eraseOption eraseServiceC eraseServiceC_idem
    (serviceLayer setup t.kem p.chosen others p.challenge)
    (serviceLayer_neverReadC setup t.kem p.chosen others p.challenge)
    (PqxdhRegistrationJointKemPostSkeleton.skelResume setup codec checks createdC.server.server.metadata.identityIndex
      createdC.publicIdentity (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw value ephemeral consumed
      native.2 owners next t.kem.val p.challenge (factoredServices setup codec checks))
    (PqxdhRegistrationJointKemObserverFree.eraseJoint state,
      (native.1.cache, (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial)))
  have same : eraseServiceC (PqxdhRegistrationJointKemObserverFree.eraseJoint state,
      (native.1.cache, (PqxdhRegistrationJointKemSecondEntry.emptyAlloc,
        (PqxdhRecordLiftLazyTable.initial : PqxdhDeploymentIdealSteps.TableState)))) =
      (PqxdhRegistrationJointKemObserverFree.eraseJoint state,
        (native.1.cache, (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial))) := by
    simp only [eraseServiceC, Prod.map, PqxdhRegistrationJointKemObserverFree.eraseJoint_idem]
    rfl
  rw [same] at erased
  rw [← erased, Functor.map_map]
  rfl

end View

/-! ### The marked build -/

section Build
open PqxdhDeploymentIdealSteps (buildHidden publishedKey)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- A hidden request of the middle source handler: the ideal registration's slot program on the detached state of `toX m`, through the allocator and item 2's table from the middle's allocator and table, rejoined. -/
theorem idealMid_run (query : PqxdhRecordLiftInterface.EnvQuery) (m : Mid KemSK) :
    (PqxdhDeploymentIdealPostSource.idealMid setup codec route checks t p created query).run m =
      (fun result => (result.1.1, PqxdhDeploymentIdealPostSource.fromX m
          (PqxdhDeploymentIdealSlots.attach result.1.2 result.2.1 result.2.2))) <$>
        (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
          ((PqxdhDeploymentIdealSteps.idealProg setup codec route checks t p
            (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) created query).run
              (PqxdhDeploymentIdealSlots.detach (PqxdhDeploymentIdealPostSource.toX m)))).run
          (m.backend.2.1, m.backend.1) := by
  change (fun r => (r.1, PqxdhDeploymentIdealPostSource.fromX m r.2)) <$>
    (PqxdhDeploymentIdealSlots.slotCore _ PqxdhDeploymentSeedSplit.tableService created query).run
      (PqxdhDeploymentIdealPostSource.toX m) = _
  rw [PqxdhDeploymentIdealSlots.slotCore_run, Functor.map_map]
  rfl

/-- The ideal registration's build of the marked session while it has a pending token, unfolded. -/
theorem buildStep_hidden_run (session : ℕ) (payload : Option Pqxdh.Bytes)
    (y : PqxdhDeploymentBackend.XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2) (coords : PqxdhDeploymentIdealSlots.Coord)
    (marked : y.backend.marks = some (session, coords))
    (pending : (y.base.native.shared.2.pending session).isSome = true) :
    (PqxdhDeploymentIdealSteps.buildStep setup codec route checks
        (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) created session payload).run y =
      ((PqxdhDeploymentIdealSlots.SlotSpec.query (.inr coords) : OracleComp PqxdhDeploymentIdealSlots.SlotSpec _) >>=
        fun value => PqxdhDeploymentIdealSteps.liftS ((buildHidden (KemSK := KemSK)
          (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks value) session payload).run
            y.base.native.shared) >>= fun r =>
        pure (r.1, { y with
          base := { y.base with native := { y.base.native with shared := r.2 } }
          backend := { y.backend with
            peer := ((publishedKey r.1 r.2.2.server).map fun keyId => (keyId, coords)).or y.backend.peer } })) := by
  have hiddenY : session = session ∧ (y.base.native.shared.2.pending session).isSome = true := ⟨rfl, pending⟩
  change (match y.backend.marks with
    | some (index, coords) => _
    | none => _) = _
  rw [marked]
  dsimp only
  rw [ite_eq_left hiddenY]

/-- Rejoining an annotated source state with its own owners and a new shared native state replaces only the shared state. -/
theorem rejoin_source (old : PqxdhRegistrationJointSchedule.State KemSK) (shared : PqxdhServerAuthNative.NativeState KemSK) :
    PqxdhDeploymentIdealPostSource.rejoin old ⟨shared, old.owners.map PqxdhRegistrationJointOwnership.Entry.owner⟩ =
      { old with shared := shared } := by
  simp only [PqxdhDeploymentIdealPostSource.rejoin]
  congr 1
  apply List.ext_getElem
  · simp
  · intro index first second
    simp only [List.getElem_mapIdx, List.getElem_map]
    rw [List.getElem?_eq_getElem (by simpa using first)]

/-- The middle state after the hidden build: the new shared native state, one more table lookup, and the Server install ghost of a published peer. -/
def afterBuild (m : Mid KemSK) (coords : PqxdhDeploymentIdealSlots.Coord)
    (result : Option PqxdhServerRegistrationPublication.Response × PqxdhServerAuthNative.NativeState KemSK) :
    Mid KemSK where
  joint := { m.joint with shared := result.2 }
  backend := ((m.backend.1.1, ⟨m.backend.1.2.lookups + 1, m.backend.1.2.draws⟩), (m.backend.2.1,
    { m.backend.2.2 with
      peer := ((publishedKey result.1 result.2.2.server).map fun keyId => (keyId, coords)).or m.backend.2.2.peer }))
  seeds := m.seeds

/-- The hidden build keeps the mark and the value at its coordinates. -/
theorem skelMarks_afterBuild (m : Mid KemSK) (coords : PqxdhDeploymentIdealSlots.Coord)
    (result : Option PqxdhServerRegistrationPublication.Response × PqxdhServerAuthNative.NativeState KemSK) :
    PqxdhDeploymentIdealPostSteps.skelMarks (afterBuild m coords result) = PqxdhDeploymentIdealPostSteps.skelMarks m :=
  rfl

/-- On the build of the marked session while it has a pending token, the middle source handler is the ideal registration's hidden build: an allocator hit at the mark's coordinates (one more table lookup), the factored response tail at the stored value, and the Server install ghost. -/
theorem sourceMid_build_hidden (session : ℕ) (payload : Option Pqxdh.Bytes) (m : Mid KemSK)
    (coords : PqxdhDeploymentIdealSlots.Coord) (marked : m.backend.2.2.marks = some (session, coords))
    (pending : (m.joint.shared.2.pending session).isSome = true)
    (slot : PqxdhRecordLiftInterface.Slot 2) (allocated : m.backend.2.1.1 coords = some slot)
    (value : Output) (stored : m.backend.1.1 slot = some value) :
    (sourceMid setup codec route checks t p created (.inl (.inr (.build session payload)))).run m =
      (fun result => (result.1, afterBuild m coords result)) <$>
        (buildHidden (KemSK := KemSK) (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks value)
          session payload).run m.joint.shared := by
  have hidden : PqxdhDeploymentIdealPostSource.buildHiddenAt m session = true := by
    simp [PqxdhDeploymentIdealPostSource.buildHiddenAt, marked, pending]
  change (if PqxdhDeploymentIdealPostSource.buildHiddenAt m session then _ else _) = _
  rw [ite_eq_left_of_eq_true _ _ (eq_true hidden), idealMid_run]
  change _ <$> (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
    ((PqxdhDeploymentIdealSteps.buildStep setup codec route checks
    (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) created session payload).run
      (PqxdhDeploymentIdealSlots.detach (PqxdhDeploymentIdealPostSource.toX m)))).run _ = _
  rw [buildStep_hidden_run setup codec route checks created session payload _ coords marked pending]
  have read : (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService (.inr coords)).run
      (m.backend.2.1, m.backend.1) =
        pure (value, (m.backend.2.1, (m.backend.1.1, ⟨m.backend.1.2.lookups + 1, m.backend.1.2.draws⟩))) := by
    rw [PqxdhRegistrationJointKemSecondEntry.slot_some (state := (m.backend.2.1, m.backend.1)) _ _ _ allocated]
    change (fun result => (result.1, (m.backend.2.1, result.2))) <$>
      (PqxdhRecordLiftLazyTable.impl (spec := PqxdhDeploymentSeedSplit.OutputSpec 2) slot).run m.backend.1 = _
    rw [PqxdhRecordLiftLazyTable.run_hit _ _ _ stored, map_pure]
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, read, pure_bind, simulateQ_bind, StateT.run_bind,
    PqxdhDeploymentIdealCut.slotImpl_lift, bind_map_left]
  simp only [simulateQ_pure, StateT.run_pure, map_bind, map_pure]
  rw [map_eq_bind_pure_comp]
  refine bind_congr fun result => ?_
  simp only [Function.comp_apply]
  congr 2
  simp only [afterBuild, PqxdhDeploymentIdealPostSource.fromX, PqxdhDeploymentIdealSlots.attach,
    PqxdhDeploymentIdealSlots.detach, PqxdhDeploymentIdealPostSource.toX]
  rw [show (PqxdhRegistrationJointSchedule.source m.joint).owners =
    m.joint.owners.map PqxdhRegistrationJointOwnership.Entry.owner from rfl, rejoin_source]

/-- On a native skeleton step, item 2's service layers with both observers erased act as the table layers, with the router state kept and the table counters erased. -/
theorem lowerEC_native {α : Type} (work : OracleComp (SkelSpec Output) α) (state : ServiceState KemSK) :
    ((simulateQ (lowerEC setup t p) (simulateQ (fwd (T := TSpec Output) (coinLift (KemSK := KemSK))) work)).run).run
        (eraseServiceC state) =
      (fun result => (some result.1, (PqxdhRegistrationJointKemObserverFree.eraseJoint state.1, eraseTables result.2))) <$>
        (simulateQ tableLayer work).run state.2 := by
  have run := run_eraseOption eraseServiceC eraseServiceC_idem _
    (serviceLayer_neverReadC setup t.kem p.chosen p.others p.challenge)
    (simulateQ (fwd (T := TSpec Output) (coinLift (KemSK := KemSK))) work) state
  rw [← run, PqxdhDeploymentIdealPostItem.service_native, Functor.map_map]
  rfl

/-- The build of the marked session while it has a pending token: item 2's build with the mark's value (the value stored at the mark's allocated slot) runs the factored response tail, as the ideal registration's hidden build does after its allocator hit; item 2's view without table counters does not see the extra lookup. -/
theorem step_build_hidden (session : ℕ) (payload : Option Pqxdh.Bytes) (m : Mid KemSK)
    (coords : PqxdhDeploymentIdealSlots.Coord) (marked : m.backend.2.2.marks = some (session, coords))
    (pending : (m.joint.shared.2.pending session).isSome = true)
    (slot : PqxdhRecordLiftInterface.Slot 2) (allocated : m.backend.2.1.1 coords = some slot)
    (value : Output) (stored : m.backend.1.1 slot = some value) :
    StepAtC setup codec route checks t p created (.inl (.inr (.build session payload))) m := by
  have marks : PqxdhDeploymentIdealPostSteps.skelMarks m = some (session, value) := by
    simp [PqxdhDeploymentIdealPostSteps.skelMarks, marked, PqxdhRegistrationJointKemSecondEntry.cacheOf, allocated,
      stored]
  unfold StepAtC
  rw [show (encodeMidC setup m).1 = (encodeMid setup m).1 from rfl,
    PqxdhDeploymentIdealPostSteps.upperE_run setup codec checks t p created _ _
      (PqxdhDeploymentIdealPostSteps.encodeMid_clean setup m),
    PqxdhDeploymentIdealPostServer.upperLayer_build, Functor.map_map, simulateQ_map, OptionT.run_map, StateT.run_map,
    show (encodeMidC setup m).2 = eraseServiceC (encodeMid setup m).2 from rfl, lowerEC_native,
    sourceMid_build_hidden setup codec route checks t p created session payload m coords marked pending slot allocated
      value stored]
  rcases found : m.joint.shared.2.pending session with _ | token
  · simp [found] at pending
  · have skel : (encodeMid setup m).1.2 = (clean m.joint.shared.2, some (session, value)) := by
      rw [← marks]
      rfl
    have cleanFound : (clean m.joint.shared.2).pending session = some token := found
    rw [skel]
    change _ <$> _ <$> (simulateQ tableLayer (PqxdhRegistrationJointKemPostSkeleton.buildStep setup codec checks
      (factoredServices setup codec checks) session payload (clean m.joint.shared.2, some (session, value)))).run _ = _
    simp only [PqxdhRegistrationJointKemPostSkeleton.buildStep, cleanFound,
      PqxdhRegistrationJointKemPostSkeleton.buildService, ite_true]
    simp only [buildHidden, StateT.run, PqxdhServerAuthNative.native_bind_run, PqxdhServerAuthNative.nativeGet,
      PqxdhServerAuthNative.localState, pure_bind, found, PqxdhServerAuthNative.nativeCoins,
      PqxdhServerAuthNative.nativeSet, bind_pure_comp, simulateQ_map, Functor.map_map,
      PqxdhServerAuthNative.native_map_run, map_pure]
    change _ <$> StateT.run (_ <$> simulateQ tableLayer (OracleComp.liftComp _ (SkelSpec Output))) _ = _
    rw [StateT.run_map, PqxdhDeploymentIdealPostItem.tableLayer_lift, Functor.map_map, Functor.map_map]
    change _ <$> (((PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks value).hiddenBuild token payload
      m.joint.shared.2.server).run ([], m.joint.shared.2.ctx)) = _ <$> (((PqxdhRegistrationJointKemEntryFactor.factoredHidden
        setup codec checks value).hiddenBuild token payload m.joint.shared.2.server).run ([], m.joint.shared.2.ctx))
    refine congrArg (fun f => f <$> _) (funext fun result => ?_)
    simp only [encodeMidC, encodeMid, eraseServiceC, eraseTables, eraseCounts, eraseTable, Prod.map,
      PqxdhDeploymentIdealPostItem.cleanUpper, Option.map_some, id_eq, skelMarks_afterBuild, marks]
    rfl

end Build

end BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.table_neverRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.table_neverRead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.run_neverRead' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.run_neverRead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.slot_neverRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.slot_neverRead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.tableLayer_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.tableLayer_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.tableLayer_neverRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.tableLayer_neverRead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.lower_neverRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.lower_neverRead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.optionLower_neverRead_both' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.optionLower_neverRead_both

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.eraseServiceC_idem' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.eraseServiceC_idem

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.eraseServiceC_eraseService' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.eraseServiceC_eraseService

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.serviceLayer_neverReadC' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.serviceLayer_neverReadC

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.stepAtC_of_stepAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.stepAtC_of_stepAt

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.itemPost_erasedC' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.itemPost_erasedC

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.idealMid_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.idealMid_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.buildStep_hidden_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.buildStep_hidden_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.rejoin_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.rejoin_source

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.skelMarks_afterBuild' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.skelMarks_afterBuild

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.sourceMid_build_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.sourceMid_build_hidden

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.lowerEC_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.lowerEC_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.step_build_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden.step_build_hidden
