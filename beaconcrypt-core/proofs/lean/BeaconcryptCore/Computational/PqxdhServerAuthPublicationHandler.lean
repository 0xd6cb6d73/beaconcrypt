import BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff
import BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds
import BeaconcryptCore.Computational.PqxdhServerAuthCtxResources

/-! Private builder observations are inserted in the literal complete selected-key client. Erasure retains every original source field, optional reply, component query and adaptive continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhJointKdfGame
open PqxdhServerAuthPublicationTrace (AnnotatedSpec liftDynamic erase)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader WireResponse Result : Type}

abbrev Program (KemSK : Type) := StateT (Local KemSK) (OracleComp AnnotatedSpec)
abbrev Compiler (KemSK : Type) := OptionT (Program KemSK)

/-- Forward an unchanged complete optional callback to the annotated component interface. -/
noncomputable def liftOld (work : PqxdhServerAuthCtxBuild.Compiler KemSK Result) : Compiler KemSK Result :=
  OptionT.mk fun state => simulateQ liftDynamic (work.run.run state)

/-- The actual selected builder is bracketed by private observations before the original token, log and Server settlement. The annotation coordinate is its reached source session. -/
noncomputable def selected (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual) (session : Nat)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : ServerState) : Compiler KemSK (Option PqxdhServerAuthCtxBuild.Response) :=
  OptionT.mk fun state => PqxdhServerAuthCtxBuild.post session state <$>
    PqxdhServerAuthPublicationTrace.annotated source codec checks rest session token.pending payload () server []

/-- The actual optional result, source settlement and component program are identical after private observations are erased. -/
theorem selected_erase (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual) (session : Nat)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : ServerState) (state : Local KemSK) :
    simulateQ erase ((selected source codec checks rest session token payload server).run.run state) =
      (PqxdhServerAuthCtxBuild.selected source codec checks rest session token payload server).run.run state := by
  simp only [selected, OptionT.run_mk, StateT.run, simulateQ_map,
    PqxdhServerAuthPublicationTrace.annotated_erase,
    PqxdhServerAuthCtxBuild.selected, PqxdhServerAuthCtxBuild.after]

/-- Forwarding an unchanged callback erases to that complete callback, for every starting local state. -/
theorem lift_erase (work : PqxdhServerAuthCtxBuild.Compiler KemSK Result) (state : Local KemSK) :
    simulateQ erase ((liftOld work).run.run state) = work.run.run state :=
  PqxdhServerAuthPublicationTrace.erase_lift _

/-- The original token lookup and selected/ordinary dispatch are unchanged. Only a reached selected builder emits publication annotations. -/
noncomputable def build (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual) (session : Nat)
    (payload : Option Pqxdh.Bytes) : Compiler KemSK (Option PqxdhServerAuthCtxBuild.Response) :=
  OptionT.mk fun state =>
    match state.1.1.pending session with
    | none => pure (some none, state)
    | some token =>
        if state.1.2.1 session then
          (selected source codec checks rest session token payload state.1.1.server).run state
        else (liftOld (PqxdhServerAuthCtxBuild.known source codec checks session token payload state.1.1.server)).run state

/-- Complete build erasure includes absent tokens, ordinary roots and every selected optional outcome. No source success or unused-nonce condition is required for this syntactic equality. -/
theorem build_erase (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual) (session : Nat)
    (payload : Option Pqxdh.Bytes) (state : Local KemSK) :
    simulateQ erase ((build source codec checks rest session payload).run.run state) =
      (PqxdhServerAuthCtxBuild.build source codec checks rest session payload).run.run state := by
  cases found : state.1.1.pending session with
  | none => simp only [build, PqxdhServerAuthCtxBuild.build, OptionT.run_mk, StateT.run, found, simulateQ_pure]
  | some token =>
      by_cases marked : state.1.2.1 session = true
      · simpa only [build, PqxdhServerAuthCtxBuild.build, OptionT.run_mk, StateT.run,
          found, marked, ite_true] using
          selected_erase source codec checks rest session token payload state.1.1.server state
      · simpa only [build, PqxdhServerAuthCtxBuild.build, OptionT.run_mk, StateT.run,
          found, marked, Bool.false_eq_true, ite_false] using
          lift_erase (PqxdhServerAuthCtxBuild.known source codec checks session token payload state.1.1.server) state

/-- The original complete dispatch is retained; only its build branch uses the privately annotated builder. -/
noncomputable def route (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (select : Bool) : QueryImpl ServerAuthSpec (Compiler KemSK)
  | .inr (.build session payload) => build setup.source codec checks rest session payload
  | query => liftOld (PqxdhServerAuthCtxHandler.route setup codec checks context rest select query)

/-- Every API route erases to the actual optional component program, retaining source state and all arbitrary component replies. -/
theorem route_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (select : Bool) (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    simulateQ erase ((route setup codec checks context rest select query).run.run state) =
      (PqxdhServerAuthCtxHandler.route setup codec checks context rest select query).run.run state := by
  cases query with
  | inl coin => exact lift_erase _ state
  | inr query =>
      cases query with
      | build session payload => exact build_erase setup.source codec checks rest session payload state
      | _ => exact lift_erase _ state

/-- The original designation latch and sticky refusal are settled after the complete actual annotated callback. -/
noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) : QueryImpl ServerAuthSpec (Compiler KemSK) :=
  fun query => OptionT.mk fun before =>
    PqxdhServerAuthCtxHandler.settle Q j query before <$>
      (route setup codec checks context rest
        (!before.2 && hiddenDesignated Q j query before.1) query).run before

/-- Private observation erasure recovers the entire original handler without a caller state, success, freshness or nonce premise. -/
theorem handler_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    simulateQ erase ((handler setup codec checks context rest Q j query).run.run state) =
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run state := by
  change simulateQ erase (PqxdhServerAuthCtxHandler.settle Q j query state <$>
    (route setup codec checks context rest (!state.2 && hiddenDesignated Q j query state.1) query).run.run state) = _
  rw [simulateQ_map, route_erase]
  rfl

/-- The existing executable second-selected-session monitor is applied after the same complete handler. -/
noncomputable def stopped (compiler : QueryImpl ServerAuthSpec (Compiler KemSK)) :=
  PqxdhServerAuthCtxStop.stopped
    (fun localState : Local KemSK => localState.1.1.sessions)
    (fun localState : Local KemSK => localState.1.2.1) compiler

/-- Erasure commutes with the unchanged stopped monitor, retaining its exact source poststate on both ordinary replies and refusal. -/
theorem stopped_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (state : Local KemSK × Option Nat) :
    simulateQ erase ((stopped (handler setup codec checks context rest Q j) query).run.run state) =
      (PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run state := by
  have same := congrArg (Functor.map (PqxdhServerAuthCtxStop.observe
    (fun localState : Local KemSK => localState.1.1.sessions)
    (fun localState : Local KemSK => localState.1.2.1) query state))
      (handler_erase setup codec checks context rest Q j query state.1)
  simpa only [stopped, PqxdhServerAuthCtxReserve.stopped, PqxdhServerAuthCtxStop.stopped,
    OptionT.run_mk, StateT.run, bind_pure_comp, simulateQ_map] using same

/-- Exact query erasure extends through every optional adaptive continuation and the complete retained local state. -/
theorem optional_erase {Input State Result : Type} {spec : OracleSpec Input}
    (annotated : QueryImpl spec (OptionT (StateT State (OracleComp AnnotatedSpec))))
    (original : QueryImpl spec (OptionT (StateT State (OracleComp AdaptiveCtxDynamicKnownKeys.Spec))))
    (same : ∀ query state, simulateQ erase ((annotated query).run.run state) =
      (original query).run.run state)
    (work : OracleComp spec Result) (state : State) :
    simulateQ erase ((simulateQ annotated work).run.run state) =
      (simulateQ original work).run.run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind,
        Option.elimM, StateT.run_bind, same]
      refine bind_congr fun ⟨reply, after⟩ => ?_
      cases reply with
      | none => simp only [Option.elim_none, StateT.run_pure, simulateQ_pure]
      | some value => exact ih value after

/-- Execute the literal adversary and original stop monitor from the original complete initial state, adding only the reached private builder observations. -/
noncomputable def execution (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) :=
  ((simulateQ (stopped (handler setup codec checks context rest Q j))
    (adversary (contextInput setup false context))).run).run (PqxdhServerAuthCtxReserve.initial setup context).1

/-- The entire adaptive stopped execution, including all original private source fields and optional replies, is recovered by observation erasure. -/
theorem execution_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) :
    simulateQ erase (execution setup codec checks adversary Q j context rest) =
      PqxdhServerAuthCtxExperiment.execution setup codec checks adversary Q j context rest :=
  optional_erase _ _ (stopped_erase setup codec checks context rest Q j) _ _

/-- The literal executable context and residual samplers precede the annotated complete adaptive execution. The original terminal decision remains unchanged. -/
noncomputable def client (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    OracleComp AnnotatedSpec Bool := do
  let context ← simulateQ liftDynamic
    (simulateQ PqxdhServerAuthCtxAmbient.coin (contextSample setup codec))
  let rest ← simulateQ liftDynamic
    (simulateQ PqxdhServerAuthCtxAmbient.coin ($ᵗ PqxdhServerAuthCtxCalls.Residual))
  PqxdhServerAuthCtxExperiment.decision setup context Q j <$>
    execution setup codec checks adversary Q j context rest

/-- The complete sampled annotated client erases to the existing ordinary one-key client, with its identical generator order and evaluated continuation. -/
theorem client_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    simulateQ erase (client setup codec checks adversary Q j) =
      PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j := by
  simp only [client, simulateQ_bind, PqxdhServerAuthPublicationTrace.erase_lift,
    simulateQ_map, execution_erase, PqxdhServerAuthCtxExperiment.client,
    PqxdhServerAuthCtxExperiment.continuation]

/-- The actual sampled client stops before its first selected raw request; its candidate and private journal are returned only to the terminal observer. -/
noncomputable def cutoff (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option PqxdhServerAuthPublicationCutoff.Candidate) :=
  PqxdhServerAuthPublicationCutoff.beforeRaw (client setup codec checks adversary Q j) []

/-- Every existing component query-class certificate transfers to the concrete pre-opening client. Private annotation bookkeeping is not an extra component query. -/
theorem cutoff_class (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate]
    (bound : Nat)
    (bounded : (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j).IsQueryBoundP predicate bound) :
    (cutoff setup codec checks adversary Q j).IsQueryBoundP predicate bound :=
  PqxdhServerAuthPublicationCutoff.beforeRaw_class _ predicate bound []
    (by rw [client_erase]; exact bounded)

/-- The concrete cutoff submits at most one selected seal and no selected raw request, including malformed raw candidates and every rejected source branch. -/
theorem cutoff_record_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    (cutoff setup codec checks adversary Q j).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 ∧
      (cutoff setup codec checks adversary Q j).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 := by
  exact ⟨cutoff_class setup codec checks adversary Q j _ 1
      (PqxdhServerAuthCtxExperiment.client_record_bills setup codec checks adversary Q j).1,
    PqxdhServerAuthPublicationCutoff.beforeRaw_zero_raw _ []⟩

/-- The production checked-addition plaintext cap transfers to the actual pre-opening client, with no caller-supplied byte bound. -/
theorem cutoff_plaintext (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    AdaptiveCtxDynamicKnownBounds.PlaintextBound
      (cutoff setup codec checks adversary Q j) Usize.max :=
  PqxdhServerAuthPublicationCutoff.beforeRaw_plaintext _ Usize.max []
    (by rw [client_erase]; exact PqxdhServerAuthCtxByteBounds.client_plaintext setup codec checks adversary Q j)

open PqxdhServerAuthSourceCosts PqxdhServerAuthGapDh PqxdhServerAuthBodyCosts

/-- Actual source coin, KEM and public-query costs remain billed through the cutoff. This consumes the complete original client ledger; the stopping observer introduces no cryptographic query. -/
theorem cutoff_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) :
    let work := cutoff setup codec checks adversary Q j
    work.IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute
        (entryReductionBudget caps qCoin Q qHash qH + 76) ∧
      work.IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute
        (entryReductionBudget caps qCoin Q qHash qH + 76) ∧
      work.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 ∧
      work.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 := by
  have bills := PqxdhServerAuthCtxResources.client_bills setup codec checks caps bounded adversary
    qCoin Q qHash qH coins accepts hashes rom j
  exact ⟨cutoff_class setup codec checks adversary Q j _ _ bills.1,
    cutoff_class setup codec checks adversary Q j _ _ bills.2.1,
    cutoff_record_bills setup codec checks adversary Q j⟩

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.selected_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.selected_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.lift_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.lift_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.build_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.build_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.route_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.route_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.handler_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.handler_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.stopped_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.stopped_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.optional_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.optional_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.execution_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.execution_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.client_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.client_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.cutoff_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.cutoff_class
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.cutoff_record_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.cutoff_record_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.cutoff_plaintext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.cutoff_plaintext
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.cutoff_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler.cutoff_bills
