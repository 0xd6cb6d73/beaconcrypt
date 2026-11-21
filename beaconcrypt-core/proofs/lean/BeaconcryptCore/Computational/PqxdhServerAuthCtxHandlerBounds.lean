import BeaconcryptCore.Computational.PqxdhServerAuthCtxHandler
import BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds
import BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds
import BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildBounds
import BeaconcryptCore.Computational.PqxdhServerAuthStopBudget

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhServerAuthCtxHandler PqxdhServerAuthCtxStop PqxdhServerAuthPendingBudget
open PqxdhSecretInputKdf PqxdhJointKdfGame
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader WireResponse Result : Type}

/-- Optional lifting preserves the exact source reply and local state in syntactic support. -/
theorem lift_support (work : Program KemSK Result) (state : Local KemSK) :
    support ((OptionT.lift work).run.run state) =
      (fun result => (some result.1, result.2)) '' support (work.run state) := by
  simp only [OptionT.run_lift, bind_pure_comp, StateT.run_map, support_map]

/-- Every normal complete route reply has the literal original allocation, phase, token and chronological mark footprint. -/
theorem route_footprint (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (select : Bool) (query : ServerAuthSpec.Domain) (state : Local KemSK)
    (result : Option (ServerAuthSpec.Range query) × Local KemSK)
    (supported : result ∈ support ((route setup codec checks context rest select query).run.run state))
    (reply : ServerAuthSpec.Range query) (normal : result.1 = some reply) :
    ResourceStep query state.1.1 result.2.1.1 ∧ MarkStep query state.1 result.2.1 := by
  cases query with
  | inr query =>
      cases query with
      | build session payload =>
          have facts := PqxdhServerAuthCtxBuildBounds.build_footprint setup.source codec checks rest session payload state result supported
          exact ⟨facts.1 (by simp only [normal, Option.isSome_some]), facts.2.1⟩
      | accept raw =>
          simp only [route, lift_support, Set.mem_image] at supported
          obtain ⟨output, actual, rfl⟩ := supported
          exact (PqxdhServerAuthCtxStateBounds.accept_footprint setup codec checks context select raw state output actual).imp_right And.left
      | finish raw =>
          simp only [route, lift_support, Set.mem_image] at supported
          obtain ⟨output, actual, rfl⟩ := supported
          exact (PqxdhServerAuthCtxFinishBounds.finish_footprint setup codec context rest select raw state output actual).imp_right And.left
      | hmac key message =>
          simp only [route, lift_support, Set.mem_image] at supported
          obtain ⟨output, actual, rfl⟩ := supported
          exact (PqxdhServerAuthCtxStateBounds.hmac_footprint setup context key message state output actual).imp_right And.left
      | hash bytes =>
          simp only [route, lift_support, Set.mem_image] at supported
          obtain ⟨output, actual, rfl⟩ := supported
          simp [PqxdhServerAuthCtxStateBounds.hash_state bytes state output actual, ResourceStep, MarkStep]
      | reveal keyId =>
          simp only [route, lift_support, Set.mem_image] at supported
          obtain ⟨output, actual, rfl⟩ := supported
          simp [PqxdhServerAuthCtxStateBounds.reveal_state keyId state output actual, ResourceStep, MarkStep]
  | inl coin =>
      simp only [route, lift_support, Set.mem_image] at supported
      obtain ⟨output, actual, rfl⟩ := supported
      simp [PqxdhServerAuthCtxStateBounds.coins_state (unifSpec.query coin) state output actual, ResourceStep, MarkStep]

/-- Actual designation and sticky refusal settlement changes neither the reply, the source resource state, nor the chronological marks. -/
theorem settle_fields (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (before : Local KemSK) (result : Result × Local KemSK) :
    (settle Q j query before result).1 = result.1 ∧
      (settle Q j query before result).2.1.1 = result.2.1.1 ∧
      (settle Q j query before result).2.1.2.1 = result.2.1.2.1 := by
  unfold PqxdhServerAuthCtxHandler.settle keepHiddenBad
  split <;> exact ⟨rfl, rfl, rfl⟩

/-- The literal complete executable handler discharges both operational footprint obligations for every normal syntactic reply. -/
theorem handler_footprint (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (state : Local KemSK)
    (result : Option (ServerAuthSpec.Range query) × Local KemSK)
    (supported : result ∈ support ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run state))
    (reply : ServerAuthSpec.Range query) (normal : result.1 = some reply) :
    ResourceStep query state.1.1 result.2.1.1 ∧ MarkStep query state.1 result.2.1 := by
  simp only [PqxdhServerAuthCtxHandler.handler, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨output, actual, rfl⟩ := supported
  have facts := route_footprint setup codec checks context rest
    (!state.2 && hiddenDesignated Q j query state.1) query state output actual reply
      ((settle_fields Q j query state output).1.symm.trans normal)
  simpa only [(settle_fields Q j query state output).2.1, MarkStep, (settle_fields Q j query state output).2.2] using facts

/-- Immediate selected record calls are paid by the actual marked pending token and one-shot Beacon phase, before optional refusal. -/
theorem route_record_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (select : Bool) (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    ((route setup codec checks context rest select query).run.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) (buildBill query state.1) ∧
    ((route setup codec checks context rest select query).run.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) (rawBill query state.1.1) := by
  cases query with
  | inl coin =>
      simpa only [route, OptionT.run_lift, bind_pure_comp, StateT.run_map, isQueryBoundP_map_iff, buildBill, rawBill] using
        (PqxdhServerAuthCtxStateBounds.coin_bills coin state).2.2.2
  | inr query =>
      cases query with
      | accept raw =>
          simp only [route, OptionT.run_lift, bind_pure_comp, StateT.run_map, isQueryBoundP_map_iff, buildBill, rawBill]
          exact (localCoins_other _ state).2
      | build session payload =>
          simp only [route, buildBill, rawBill]
          exact ⟨(PqxdhServerAuthCtxBuildBounds.build_bills setup.source codec checks rest session payload state).2.1, (PqxdhServerAuthCtxBuildBounds.build_bills setup.source codec checks rest session payload state).2.2.2.1⟩
      | finish raw =>
          simp only [route, OptionT.run_lift, bind_pure_comp, StateT.run_map, isQueryBoundP_map_iff, buildBill, rawBill]
          exact (PqxdhServerAuthCtxFinishBounds.finish_record_bills setup codec context rest select raw state).2
      | hmac key message =>
          simp only [route, OptionT.run_lift, bind_pure_comp, StateT.run_map, isQueryBoundP_map_iff, buildBill, rawBill]
          exact (localCoins_other _ state).2
      | hash bytes =>
          simp only [route, OptionT.run_lift, bind_pure_comp, StateT.run_map, isQueryBoundP_map_iff, buildBill, rawBill]
          exact ⟨(PqxdhServerAuthCtxStateBounds.hash_bills bytes state).2.1, (PqxdhServerAuthCtxStateBounds.hash_bills bytes state).2.2.1⟩
      | reveal keyId =>
          simp only [route, OptionT.run_lift, bind_pure_comp, StateT.run_map, isQueryBoundP_map_iff, buildBill, rawBill]
          exact ⟨IsQueryBoundP.of_imp (fun _ _ => True.intro) ((isQueryBoundP_true_iff _ _).2 (PqxdhServerAuthCtxStateBounds.reveal_total keyId state)), IsQueryBoundP.of_imp (fun _ _ => True.intro) ((isQueryBoundP_true_iff _ _).2 (PqxdhServerAuthCtxStateBounds.reveal_total keyId state))⟩

/-- The complete handler adds no selected call during designation or refusal settlement; its immediate ledger remains the literal source token and phase bill. -/
theorem handler_record_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) (buildBill query state.1) ∧
    ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) (rawBill query state.1.1) := by
  simpa only [PqxdhServerAuthCtxHandler.handler, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff] using
    route_record_bills setup codec checks context rest (!state.2 && hiddenDesignated Q j query state.1) query state

/-- Every complete stopped adaptive execution of the actual compiler makes at most one selected seal and one selected raw opening. All callback footprints and immediate bills are discharged by the concrete handler, including work before refusal. -/
theorem stopped_record_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (client : OracleComp ServerAuthSpec Result)
    (state : Local KemSK × Option Nat) (valid : ControlValid (fun localState : Local KemSK => localState.1) state) :
    (((simulateQ (stopped (fun localState : Local KemSK => localState.1.1.sessions)
      (fun localState : Local KemSK => localState.1.2.1)
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) client).run).run state).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 ∧
    (((simulateQ (stopped (fun localState : Local KemSK => localState.1.1.sessions)
      (fun localState : Local KemSK => localState.1.2.1)
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) client).run).run state).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 1 := by
  exact ⟨stopped_callback_one (fun localState : Local KemSK => localState.1)
    (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)
    (handler_footprint setup codec checks context rest Q j) false _
    (fun query localState => (handler_record_bills setup codec checks context rest Q j query localState).1)
    client state valid,
    stopped_callback_one (fun localState : Local KemSK => localState.1)
    (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)
    (handler_footprint setup codec checks context rest Q j) true _
    (fun query localState => (handler_record_bills setup codec checks context rest Q j query localState).2)
    client state valid⟩

/-- The actual sampled experiment context starts with empty marks, table and monitor, so the executable control invariant needs no source honesty or freshness assumption. -/
theorem initial_control (setup : Setup baseSpec KemSK) (context : Context KemSK) :
    ControlValid (fun localState : Local KemSK => localState.1)
      (((contextState setup context, fun _ => false, ⟨∅, none, false⟩), false), none) := by
  exact ⟨⟨by simp, by simp⟩, by simp [Below]⟩

/-- The actual original adversary and context projection, with identity-seed disclosure disabled, have global selected seal and raw-opening caps of one in the concrete stopped compiler. Every pre-refusal attempted call is counted. -/
theorem initial_record_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (adversary : Adversary) :
    let run := (((simulateQ (stopped (fun localState : Local KemSK => localState.1.1.sessions)
      (fun localState : Local KemSK => localState.1.2.1)
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j))
      (adversary (contextInput setup false context))).run).run
      (((contextState setup context, fun _ => false, ⟨∅, none, false⟩), false), none))
    run.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 ∧
      run.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 1 := by
  exact stopped_record_bills setup codec checks context rest Q j
    (adversary (contextInput setup false context)) _ (initial_control setup context)

end BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds.lift_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds.lift_support
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds.route_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds.route_footprint
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds.settle_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds.settle_fields
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds.handler_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds.handler_footprint
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds.route_record_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds.route_record_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds.handler_record_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds.handler_record_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds.stopped_record_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds.stopped_record_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds.initial_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds.initial_control
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds.initial_record_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds.initial_record_bills
