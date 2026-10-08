-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol
import BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory

/-! The source's private pre-query sealing history rules out the artificial selected-nonce stop before any reply is requested, retaining the complete bare source continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal
open PqxdhRecordLiftInterface PqxdhRecordLiftProtocol PqxdhRecordLiftCtxProtocol
open PqxdhRecordLiftProtocolHistory
variable {n : Nat} {Reader Response Result : Type}

/-- A previously used selected nonce must be justified by an earlier attempt at its exact structural coordinate. Other nonces are irrelevant to this guard. -/
def UsedSound (state : CutState n) (past : List (PqxdhRecordLiftWorldCompiler.Label n)) : Prop :=
  state.nonce ∈ state.used → state.coordinate ∈ past

/-- Source freshness is checked before asking the service, so it rules out refusal without conditioning on a successful stopped execution. -/
theorem fresh_no_refusal (query : Service n) (state : CutState n)
    (past : List (PqxdhRecordLiftWorldCompiler.Label n))
    (fresh : Fresh (past, query)) (sound : UsedSound state past) :
    ¬ (SelectedSeal state.coordinate query ∧ state.nonce ∈ state.used) := by
  intro refused
  cases query <;> simp only [SelectedSeal] at refused
  all_goals first
    | exact refused.1.elim
    | exact fresh (refused.1.2 ▸ sound refused.2)

/-- The literal attempt update maintains the selected nonce's provenance even on writer None; no source or primitive result is needed for this fact. -/
theorem advance_sound (query : Service n) (state : CutState n)
    (past : List (PqxdhRecordLiftWorldCompiler.Label n)) (sound : UsedSound state past)
    (native : Bare n) :
    UsedSound { state with native := native, used := advanceUsed state query }
      (past ++ PqxdhRecordLiftWorldProvenance.sealingCoordinates query) := by
  classical
  intro member
  by_cases selected : SelectedSeal state.coordinate query
  · cases query <;> simp only [SelectedSeal] at selected
    all_goals first
      | exact selected.elim
      | simp only [PqxdhRecordLiftWorldProvenance.sealingCoordinates, List.mem_append,
          List.mem_singleton, selected.2, or_true]
  · simp only [advanceUsed, selected, ite_false] at member
    exact List.mem_append_left _ (sound member)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- The total source interpreter carries the same selected-attempt ghost without adding a refusal branch or changing any source operation. -/
noncomputable def trackingInterpreter (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) :
    QueryImpl (ServiceSpec n) (StateT (CutState n) ProbComp) :=
  fun query state => do
    let result ← (bareInterpreter setup codec ideal query).run state.native
    pure (result.1, { state with native := result.2, used := advanceUsed state query })

/-- The complete stopped execution equals a successful total source execution whenever its actual private pre-query history is fresh. The statement retains the entire result and final ghost/native state. -/
theorem stop_free (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (client : OracleComp (ServiceSpec n) Result) (state : CutState n)
    (past : List (PqxdhRecordLiftWorldCompiler.Label n)) (sound : UsedSound state past)
    (fresh : (annotated client past).AllQueriesSatisfy Fresh) :
    (simulateQ (stoppedBareInterpreter setup codec ideal) client).run.run state =
      (fun result => (Except.ok result.1, result.2)) <$>
        (simulateQ (trackingInterpreter setup codec ideal) client).run state := by
  induction client using OracleComp.inductionOn generalizing state past with
  | pure value => rfl
  | query_bind query next ih =>
      rw [annotated_query_bind, allQueriesSatisfy_query_bind_iff] at fresh
      have allowed := fresh_no_refusal query state past fresh.1 sound
      simp only [simulateQ_bind, simulateQ_spec_query]
      rw [PqxdhRecordLiftCtxOracle.except_bind, StateT.run_bind]
      simp only [stoppedBareInterpreter, ExceptT.run, ExceptT.mk, trackingInterpreter,
        StateT.run, allowed, ite_false, bind_assoc, pure_bind, map_bind]
      apply bind_congr
      intro result
      exact ih result.1 _ (past ++ PqxdhRecordLiftWorldProvenance.sealingCoordinates query)
        (advance_sound query state past sound result.2) (fresh.2 result.1)

/-- Erasing only the selected-attempt ghost recovers the literal source service, with every bare field unchanged. -/
theorem tracking_query (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (query : Service n) (state : CutState n) :
    Prod.map id CutState.native <$> (trackingInterpreter setup codec ideal query).run state =
      (bareInterpreter setup codec ideal query).run state.native := by
  simp [trackingInterpreter, StateT.run, bind_pure_comp, Functor.map_map]

/-- The complete ghost-tracked execution erases exactly to the original bare source, retaining its full Result and source private state. -/
theorem tracking_schedule (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (client : OracleComp (ServiceSpec n) Result) (state : CutState n) :
    Prod.map id CutState.native <$>
      (simulateQ (trackingInterpreter setup codec ideal) client).run state =
      (simulateQ (bareInterpreter setup codec ideal) client).run state.native :=
  map_run_simulateQ_eq_of_query_map_eq _ _ CutState.native
    (tracking_query setup codec ideal) client state

/-- Removing the proof-side attempt ghost gives the actual bare source execution with an always-successful outer Except tag. Actual optional plaintext and writer failures remain inside their original replies. -/
theorem bare_no_refusal (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (client : OracleComp (ServiceSpec n) Result) (state : CutState n)
    (past : List (PqxdhRecordLiftWorldCompiler.Label n)) (sound : UsedSound state past)
    (fresh : (annotated client past).AllQueriesSatisfy Fresh) :
    Prod.map id CutState.native <$>
      (simulateQ (stoppedBareInterpreter setup codec ideal) client).run.run state =
      (fun result => (Except.ok result.1, result.2)) <$>
        (simulateQ (bareInterpreter setup codec ideal) client).run state.native := by
  rw [stop_free setup codec ideal client state past sound fresh, ← tracking_schedule setup codec ideal client state]
  simp only [Functor.map_map, Prod.map_def, id_eq]

/-- Every actual initialized adaptive schedule discharges freshness itself, for every selected coordinate and nonce and every supplied bare private state. -/
theorem initial_schedule_no_refusal (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (client : OracleComp (WorldSpec n) Result) (native : Bare n)
    (coordinate : PqxdhRecordLiftChainState.Coordinate (Slot n)) (nonce : CtxRomAuth.CtxNonce) :
    Prod.map id CutState.native <$>
      (simulateQ (stoppedBareInterpreter setup codec ideal)
        (PqxdhRecordLiftProtocol.schedule codec.frameRead route client initialControl)).run.run
          ⟨native, coordinate, nonce, []⟩ =
      (fun result => (Except.ok result.1, result.2)) <$>
        (simulateQ (bareInterpreter setup codec ideal)
          (PqxdhRecordLiftProtocol.schedule codec.frameRead route client initialControl)).run native :=
  bare_no_refusal setup codec ideal _ ⟨native, coordinate, nonce, []⟩ []
    (by intro member; cases member) (initial_schedule_fresh codec.frameRead route client)

/-- Both frozen protocol modes remove the artificial selected-nonce stop while retaining the complete environment, ledger, adversary result and source state. -/
theorem program_no_refusal {E X : Type} (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) (native : Bare n)
    (coordinate : PqxdhRecordLiftChainState.Coordinate (Slot n)) (nonce : CtxRomAuth.CtxNonce) :
    let client := PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary
    Prod.map id CutState.native <$>
      (simulateQ (stoppedBareInterpreter setup codec ideal) client).run.run
        ⟨native, coordinate, nonce, []⟩ =
      (fun result => (Except.ok result.1, result.2)) <$>
        (simulateQ (bareInterpreter setup codec ideal) client).run native :=
  initial_schedule_no_refusal setup codec route ideal _ native coordinate nonce

/-- Starting at the actual source initial state identifies the no-refusal experiment with the complete mixed World execution after the existing explicit counter projection. -/
theorem program_world_no_refusal {E X : Type} (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (coordinate : PqxdhRecordLiftChainState.Coordinate (Slot n)) (nonce : CtxRomAuth.CtxNonce) :
    Prod.map id CutState.native <$>
      (simulateQ (stoppedBareInterpreter setup codec ideal)
        (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run.run
          ⟨erasePrivate initialPrivate, coordinate, nonce, []⟩ =
      (fun result => (Except.ok (splitResult result).1, erasePrivate (splitResult result).2)) <$>
        PqxdhRecordLiftWorldCompiler.run (PqxdhRecordLiftChainOracle.lookup setup.source · ideal)
          setup codec route env serverKid bounds mode adversary := by
  rw [program_no_refusal setup codec route env serverKid bounds mode adversary ideal
    (erasePrivate initialPrivate) coordinate nonce, program_bare]
  simp only [Functor.map_map, Prod.map_def, id_eq]

open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxSharedModes AdaptiveCtxDynamicKnownKeys

/-- The actual ordinary selected-key reduction simulates the unstopped global source once its selected nonce history starts empty. Source syntax discharges later freshness; the selected already-ideal table condition remains explicit, and no key-distribution assumption is inferred. -/
theorem program_reduction_no_refusal {E X : Type} (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (slot : Nat)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) (key : CtxKey) (state : Secret n)
    (others : ReductionState) (selected : AdaptiveCtxSharedModes.State)
    (unused : selected.1.1.usedNonces = []) (parentIdeal : ideal state.masked.coordinate = true) :
    let client := PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary
    (fun result => Prod.map id CutState.native
      (Prod.map id (realizeCut key) (projectReply (AdaptiveCtxDynamicKnownKeys.erase result)))) <$>
      (simulateQ (targetImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
        (reduction slot setup.source ideal codec client state others)).run selected =
      (fun result => (Except.ok result.1, result.2)) <$>
        (simulateQ (bareInterpreter setup codec ideal) client).run
          (realizeCut key (projectSecret (state, AdaptiveCtxDynamicKnownKeys.project (others, selected)))).native := by
  have source := congrArg (fun work => Prod.map id CutState.native <$> work)
    (program_reduction_cut setup codec route slot env serverKid bounds mode adversary ideal key state others selected parentIdeal)
  have sound : UsedSound (realizeCut key
      (projectSecret (state, AdaptiveCtxDynamicKnownKeys.project (others, selected)))) [] := by
    intro member
    change state.masked.value.2 ∈ selected.1.1.usedNonces at member
    rw [unused] at member
    cases member
  simpa only [Functor.map_map] using source.trans
    (bare_no_refusal setup codec ideal _ _ [] sound
      (program_fresh env setup.source.crypto codec route serverKid bounds mode adversary))

end BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal.fresh_no_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal.fresh_no_refusal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal.advance_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal.advance_sound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal.stop_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal.stop_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal.tracking_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal.tracking_query

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal.tracking_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal.tracking_schedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal.bare_no_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal.bare_no_refusal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal.initial_schedule_no_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal.initial_schedule_no_refusal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal.program_no_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal.program_no_refusal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal.program_world_no_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal.program_world_no_refusal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal.program_reduction_no_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal.program_reduction_no_refusal
