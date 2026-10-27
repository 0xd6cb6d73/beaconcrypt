import BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame
import BeaconcryptCore.Computational.PqxdhServerAuthCtxResources

/-! The explicit publication comparison changes only the selected builder's frame writer. Its adaptive selected seal/raw query bill is checked independently of the actual writer's outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhServerAuthCtxBuild (Compiler)
open PqxdhServerAuthPendingBudget PqxdhServerAuthCtxStop
variable {ι KemSK Reader WireResponse Result : Type} {baseSpec : OracleSpec ι}

/-- The original pending-token dispatch uses the reference inner writer only for the marked selected token. Ordinary builders and absent-token behavior remain literal source operations. -/
noncomputable def build (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual) (session : Nat)
    (payload : Option Pqxdh.Bytes) : Compiler KemSK (Option PqxdhServerAuthCtxBuild.Response) :=
  OptionT.mk fun state =>
    match state.1.1.pending session with
    | none => pure (some none, state)
    | some token =>
        if state.1.2.1 session then
          (PqxdhServerAuthCtxBuild.selected source (PqxdhServerAuthPublicationForcedFrame.referenceCodec codec)
            checks rest session token payload state.1.1.server).run state
        else (PqxdhServerAuthCtxBuild.known source codec checks session token payload state.1.1.server).run state

/-- All public operations keep their original callbacks; only build uses the mixed selected/ordinary dispatch. -/
noncomputable def route (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (select : Bool) : QueryImpl ServerAuthSpec (Compiler KemSK)
  | .inr (.build session payload) => build setup.source codec checks rest session payload
  | query => PqxdhServerAuthCtxHandler.route setup codec checks context rest select query

/-- The same designation and sticky refusal settlement follows every complete mixed callback. -/
noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) : QueryImpl ServerAuthSpec (Compiler KemSK) :=
  fun query => OptionT.mk fun before =>
    PqxdhServerAuthCtxHandler.settle Q j query before <$>
      (route setup codec checks context rest
        (!before.2 && hiddenDesignated Q j query before.1) query).run before

/-- Retain the existing monitor, including its complete callback execution before a second-session stop. -/
noncomputable def stopped (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) :=
  PqxdhServerAuthCtxReserve.stopped (handler setup codec checks context rest Q j)

/-- The actual adversary and existing monitor run from the same full initial local state. This reference retains every optional answer and operational poststate. -/
noncomputable def execution (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) :=
  ((simulateQ (stopped setup codec checks context rest Q j)
    (adversary (contextInput setup false context))).run).run (PqxdhServerAuthCtxReserve.initial setup context).1

/-- The reference samples the same complete context and residual material, retaining both beside the full optional execution result for later event observations. -/
noncomputable def client (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) := do
  let context ← simulateQ PqxdhServerAuthCtxAmbient.coin (contextSample setup codec)
  let rest ← simulateQ PqxdhServerAuthCtxAmbient.coin ($ᵗ PqxdhServerAuthCtxCalls.Residual)
  let result ← execution setup codec checks adversary Q j context rest
  pure (context, rest, result)

/-- Actual pending-token lookup and the session mark select the entire concrete callback bill, retaining work before optional refusal. -/
theorem build_query_bound (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual) (session : Nat)
    (payload : Option Pqxdh.Bytes) (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop)
    [DecidablePred predicate] (selectedBill knownBill : Nat)
    (selectedBound : ∀ token server (state : Local KemSK),
      ((PqxdhServerAuthCtxBuild.selected source (PqxdhServerAuthPublicationForcedFrame.referenceCodec codec) checks rest session token payload server).run.run state).IsQueryBoundP predicate selectedBill)
    (knownBound : ∀ token server (state : Local KemSK),
      ((PqxdhServerAuthCtxBuild.known source codec checks session token payload server).run.run state).IsQueryBoundP predicate knownBill)
    (state : Local KemSK) :
    ((build source codec checks rest session payload).run.run state).IsQueryBoundP predicate
      ((if state.1.2.1 session then selectedBill else knownBill) * slotWeight (state.1.1.pending session)) := by
  simp only [build, OptionT.run_mk, StateT.run]
  cases found : state.1.1.pending session with
  | none => trivial
  | some token =>
      simp only [slotWeight, Nat.mul_one]
      split_ifs
      · exact selectedBound token _ state
      · exact knownBound token _ state


/-- The original marked pending token pays the only possible selected seal; all builds retain their exact hash and zero raw/uniform component classes. -/
theorem build_bills (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual) (session : Nat)
    (payload : Option Pqxdh.Bytes) (state : Local KemSK) :
    ((build source codec checks rest session payload).run.run state).IsTotalQueryBound (slotWeight (state.1.1.pending session)) ∧
    ((build source codec checks rest session payload).run.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal)
      (if state.1.2.1 session then slotWeight (state.1.1.pending session) else 0) ∧
    ((build source codec checks rest session payload).run.run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute
      (slotWeight (state.1.1.pending session)) ∧
    ((build source codec checks rest session payload).run.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 ∧
    ((build source codec checks rest session payload).run.run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply (isQueryBoundP_true_iff _ _).1
    simpa only [ite_self, Nat.one_mul] using build_query_bound source codec checks rest session payload
      (fun _ => True) 1 1
      (fun token server state => (isQueryBoundP_true_iff _ _).2 (PqxdhServerAuthCtxBuildBounds.selected_bills source (PqxdhServerAuthPublicationForcedFrame.referenceCodec codec) checks rest session token payload server state).1)
      (fun token server state => (isQueryBoundP_true_iff _ _).2 (PqxdhServerAuthCtxBuildBounds.known_bills source codec checks session token payload server state).1) state
  · simpa only [ite_mul, Nat.one_mul, Nat.zero_mul] using build_query_bound source codec checks rest session payload
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 0
      (fun token server state => (PqxdhServerAuthCtxBuildBounds.selected_bills source (PqxdhServerAuthPublicationForcedFrame.referenceCodec codec) checks rest session token payload server state).2.1)
      (fun token server state => (PqxdhServerAuthCtxBuildBounds.known_bills source codec checks session token payload server state).2.2.1) state
  · simpa only [ite_self, Nat.one_mul] using build_query_bound source codec checks rest session payload
      AdaptiveCtxDynamicKnownBounds.HashRoute 1 1
      (fun token server state => (PqxdhServerAuthCtxBuildBounds.selected_bills source (PqxdhServerAuthPublicationForcedFrame.referenceCodec codec) checks rest session token payload server state).2.2.1)
      (fun token server state => (PqxdhServerAuthCtxBuildBounds.known_bills source codec checks session token payload server state).2.1) state
  · simpa only [ite_self, Nat.zero_mul] using build_query_bound source codec checks rest session payload
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 0
      (fun token server state => (PqxdhServerAuthCtxBuildBounds.selected_bills source (PqxdhServerAuthPublicationForcedFrame.referenceCodec codec) checks rest session token payload server state).2.2.2.1)
      (fun token server state => (PqxdhServerAuthCtxBuildBounds.known_bills source codec checks session token payload server state).2.2.2.1) state
  · simpa only [ite_self, Nat.zero_mul] using build_query_bound source codec checks rest session payload
      AdaptiveCtxDynamicKnownBounds.UniformRoute 0 0
      (fun token server state => (PqxdhServerAuthCtxBuildBounds.selected_bills source (PqxdhServerAuthPublicationForcedFrame.referenceCodec codec) checks rest session token payload server state).2.2.2.2)
      (fun token server state => (PqxdhServerAuthCtxBuildBounds.known_bills source codec checks session token payload server state).2.2.2.2) state


/-- Actual pending-token dispatch supplies the resource and mark footprints for every dynamic reply, including optional component refusal and native writer failure. -/
theorem build_footprint (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual) (session : Nat)
    (payload : Option Pqxdh.Bytes) (state : Local KemSK)
    (result : Option (Option PqxdhServerRegistrationPublication.Response) × Local KemSK)
    (supported : result ∈ support ((build source codec checks rest session payload).run.run state)) :
    (result.1.isSome → ResourceStep (.inr (.build session payload)) state.1.1 result.2.1.1) ∧
      result.2.1.2.1 = state.1.2.1 ∧ result.2.2 = state.2 := by
  simp only [build, OptionT.run_mk, StateT.run] at supported
  cases found : state.1.1.pending session with
  | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨fun _ => ⟨rfl, rfl, by rw [← found, Function.update_eq_self]⟩, rfl, rfl⟩
  | some token =>
      simp only [found] at supported
      split_ifs at supported
      · exact PqxdhServerAuthCtxBuildBounds.after_footprint session payload _ state result supported
      · exact PqxdhServerAuthCtxBuildBounds.after_footprint session payload _ state result supported


/-- Every normal complete route reply has the literal original allocation, phase, token and chronological mark footprint. -/
theorem route_footprint (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (select : Bool) (query : ServerAuthSpec.Domain) (state : Local KemSK)
    (result : Option (ServerAuthSpec.Range query) × Local KemSK)
    (supported : result ∈ support ((route setup codec checks context rest select query).run.run state))
    (reply : ServerAuthSpec.Range query) (normal : result.1 = some reply) :
    ResourceStep query state.1.1 result.2.1.1 ∧ MarkStep query state.1 result.2.1 := by
  cases query with
  | inl coin => exact PqxdhServerAuthCtxHandlerBounds.route_footprint setup codec checks context rest select _ state result supported reply normal
  | inr query =>
      cases query with
      | build session payload =>
          have facts := build_footprint setup.source codec checks rest session payload state result supported
          exact ⟨facts.1 (by simp only [normal, Option.isSome_some]), facts.2.1⟩
      | _ => exact PqxdhServerAuthCtxHandlerBounds.route_footprint setup codec checks context rest select _ state result supported reply normal


/-- The literal complete executable handler discharges both operational footprint obligations for every normal syntactic reply. -/
theorem handler_footprint (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (state : Local KemSK)
    (result : Option (ServerAuthSpec.Range query) × Local KemSK)
    (supported : result ∈ support ((handler setup codec checks context rest Q j query).run.run state))
    (reply : ServerAuthSpec.Range query) (normal : result.1 = some reply) :
    ResourceStep query state.1.1 result.2.1.1 ∧ MarkStep query state.1 result.2.1 := by
  simp only [handler, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨output, actual, rfl⟩ := supported
  have facts := route_footprint setup codec checks context rest
    (!state.2 && hiddenDesignated Q j query state.1) query state output actual reply
      ((PqxdhServerAuthCtxHandlerBounds.settle_fields Q j query state output).1.symm.trans normal)
  simpa only [(PqxdhServerAuthCtxHandlerBounds.settle_fields Q j query state output).2.1, MarkStep, (PqxdhServerAuthCtxHandlerBounds.settle_fields Q j query state output).2.2] using facts


/-- Immediate selected record calls are paid by the actual marked pending token and one-shot Beacon phase, before optional refusal. -/
theorem route_record_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (select : Bool) (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    ((route setup codec checks context rest select query).run.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) (buildBill query state.1) ∧
    ((route setup codec checks context rest select query).run.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) (rawBill query state.1.1) := by
  cases query with
  | inl coin => exact PqxdhServerAuthCtxHandlerBounds.route_record_bills setup codec checks context rest select (.inl coin) state
  | inr query =>
      cases query with
      | build session payload =>
          simp only [route, buildBill, rawBill]
          exact ⟨(build_bills setup.source codec checks rest session payload state).2.1,
            (build_bills setup.source codec checks rest session payload state).2.2.2.1⟩
      | accept raw => exact PqxdhServerAuthCtxHandlerBounds.route_record_bills setup codec checks context rest select (.inr (.accept raw)) state
      | finish raw => exact PqxdhServerAuthCtxHandlerBounds.route_record_bills setup codec checks context rest select (.inr (.finish raw)) state
      | hmac key message => exact PqxdhServerAuthCtxHandlerBounds.route_record_bills setup codec checks context rest select (.inr (.hmac key message)) state
      | hash bytes => exact PqxdhServerAuthCtxHandlerBounds.route_record_bills setup codec checks context rest select (.inr (.hash bytes)) state
      | reveal keyId => exact PqxdhServerAuthCtxHandlerBounds.route_record_bills setup codec checks context rest select (.inr (.reveal keyId)) state


/-- The complete handler adds no selected call during designation or refusal settlement; its immediate ledger remains the literal source token and phase bill. -/
theorem handler_record_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    ((handler setup codec checks context rest Q j query).run.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) (buildBill query state.1) ∧
    ((handler setup codec checks context rest Q j query).run.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) (rawBill query state.1.1) := by
  simpa only [handler, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff] using
    route_record_bills setup codec checks context rest (!state.2 && hiddenDesignated Q j query state.1) query state



/-- The complete mixed reference still makes at most one selected seal and one selected raw call under the original control invariant. Every callback and pre-refusal request is included, for all adaptive replies. -/
theorem stopped_record_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result)
    (state : Local KemSK × Option Nat) (valid : ControlValid (fun localState : Local KemSK => localState.1) state) :
    ((simulateQ (stopped setup codec checks context rest Q j) work).run.run state).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 ∧
    ((simulateQ (stopped setup codec checks context rest Q j) work).run.run state).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 1 := by
  exact ⟨stopped_callback_one (fun localState : Local KemSK => localState.1)
    (handler setup codec checks context rest Q j)
    (handler_footprint setup codec checks context rest Q j) false _
    (fun query localState => (handler_record_bills setup codec checks context rest Q j query localState).1)
    work state valid,
    stopped_callback_one (fun localState : Local KemSK => localState.1)
    (handler setup codec checks context rest Q j)
    (handler_footprint setup codec checks context rest Q j) true _
    (fun query localState => (handler_record_bills setup codec checks context rest Q j query localState).2)
    work state valid⟩


/-- The literal initial state discharges the control invariant for the actual reference adversary, without a key, honesty or successful-writer premise. -/
theorem execution_record_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) :
    (execution setup codec checks adversary Q j context rest).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 ∧
    (execution setup codec checks adversary Q j context rest).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 1 := by
  exact stopped_record_bills setup codec checks context rest Q j
    (adversary (contextInput setup false context)) _ (PqxdhServerAuthCtxHandlerBounds.initial_control setup context)

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference.build_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference.build_query_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference.build_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference.build_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference.build_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference.build_footprint

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference.route_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference.route_footprint

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference.handler_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference.handler_footprint

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference.route_record_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference.route_record_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference.handler_record_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference.handler_record_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference.stopped_record_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference.stopped_record_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference.execution_record_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference.execution_record_bills
