-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor

/-! The exact source projection of the actual private challenge designation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeMonitorSource
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry PqxdhFirstRecordConfidentiality
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) (monitor : Fin B)


/-- Material interpretation preserves the actual pre-request send-chain condition at the same owner. No key or chain injectivity is used. -/
theorem selected_native (target key : RootOutput) (owner : RawCtxProtocolReveals.Owner S B)
    (before : InsState M P I D K A N C S B) :
    PqxdhLaterChallengeMonitor.Selected target owner before ↔
      ∀ kernel, RawCtxProtocolReveals.selectedKernel owner
        (RawCtxGenericRoleFamily.nativeRoles (RawCtxSelectedMessageReveals.nativeKernel key) before.1.1.roles.1) = some kernel →
        RawCtxSelectedPendingCut.requestAddress kernel.refined.send_chain = RawCtxSelectedParentPrivatePatch.targetAddress target := by
  rw [RawCtxGenericRoleFamily.native_selected]
  cases lookup : RawCtxGenericRoleFamily.selectedKernel owner before.1.1.roles.1 <;>
    simp [PqxdhLaterChallengeMonitor.Selected, lookup, RawCtxSelectedMessageReveals.nativeKernel]
  rfl

/-- The source wrapper state includes the literal public challenge state, complete callback state and private request marker. -/
abbrev State (σ : Type) := PqxdhRecordConfidentialityChallenge.State × (σ × Option Bool)

def project {σ τ : Type} (projection : σ → τ) (state : State σ) : State τ :=
  (state.1, (projection state.2.1, state.2.2))

/-- The same request-time rule as the executable monitor, evaluated on the original full source state. -/
noncomputable def record {σ : Type} (selected : σ → Prop) (query : (AdvSpec extra S B).Domain) (before : State σ) : Option Bool := by
  classical
  exact match before.2.2 with
  | some value => some value
  | none => match query with
    | .inl _ => none
    | .inr (left, right) =>
        if before.1.pair.isSome ∨ left.length ≠ right.length then none
        else some (decide (selected before.2.1))

/-- Execute the literal wrapper callback through the supplied operational source interpreter before recording its exact input condition. Optional source refusal retains its completed state. -/
noncomputable def step {σ : Type}
    (impl : QueryImpl (RawCtxSelectedFamilyNonceCoupling.Optional (ConfPostSpec extra S B)) (StateT σ ProbComp))
    (selected : σ → Prop) (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool) :
    QueryImpl (RawCtxSelectedFamilyNonceCoupling.Optional (AdvSpec extra S B)) (StateT (State σ) ProbComp) :=
  fun query before =>
    (fun result => (result.1.map Prod.fst,
      (result.1.elim before.1 Prod.snd, (result.2, record (extra := extra) selected query before)))) <$>
      (simulateQ impl (RawCtxSelectedFamilyNonceCoupling.optionalClient
        ((PqxdhRecordConfidentialityChallenge.handler owner number bit query).run before.1))).run before.2.1

/-- Exact callback-state projection commutes with the original wrapper and the private request marker. This is an operational equality, not an event or security premise. -/
theorem step_project {σ τ : Type}
    (impl : QueryImpl (RawCtxSelectedFamilyNonceCoupling.Optional (ConfPostSpec extra S B)) (StateT σ ProbComp))
    (original : QueryImpl (RawCtxSelectedFamilyNonceCoupling.Optional (ConfPostSpec extra S B)) (StateT τ ProbComp))
    (projection : σ → τ)
    (law : ∀ query before, Prod.map id projection <$> (impl query).run before = (original query).run (projection before))
    (selected : τ → Prop) (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (query : (AdvSpec extra S B).Domain) (before : State σ) :
    Prod.map id (project projection) <$> (step impl (selected ∘ projection) owner number bit query).run before =
      (step original selected owner number bit query).run (project projection before) := by
  have same := map_run_simulateQ_eq_of_query_map_eq impl original projection law
    (RawCtxSelectedFamilyNonceCoupling.optionalClient
      ((PqxdhRecordConfidentialityChallenge.handler owner number bit query).run before.1)) before.2.1
  simp only [step, StateT.run, project, Functor.map_map]
  simp only [StateT.run] at same
  rw [← same, Functor.map_map]
  rfl

/-- The actual source condition inspects the same reached labelled role; material interpretation changes none of its send-chain fields. -/
def Selected (target : RootOutput) (owner : RawCtxProtocolReveals.Owner S B)
    (before : PqxdhSelectedFirstRecord.Traced M P I D K A N C S B) : Prop :=
  ∀ kernel, RawCtxGenericRoleFamily.selectedKernel owner before.1.1.roles.1 = some kernel →
    RawCtxSelectedPendingCut.requestAddress kernel.send_chain = RawCtxSelectedParentPrivatePatch.targetAddress target

/-- The actual source and executable annotation agree at this exact pre-request state, including the shared-cache projection. -/
theorem record_executable (owner : RawCtxProtocolReveals.Owner S B) (query : (AdvSpec extra S B).Domain)
    (current : PqxdhRecordConfidentialityChallenge.State) (before : InsFull M P I D K A N C S B) (choice : Option Bool) :
    record (extra := extra) (Selected target owner ∘ insProject) query (current, (before, choice)) =
      PqxdhLaterChallengeMonitor.record (extra := extra) target owner query current (before.1, choice) := by
  rfl

/-- The complete original adaptive wrapper and private request marker project from the actual augmented interpreter to the stopped source with every reply and full source state retained. -/
theorem augmented_source {Result : Type} (key : RootOutput) (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (work : OracleComp (AdvSpec extra S B) Result) (before : State (InsFull M P I D K A N C S B)) :
    Prod.map id (project insProject) <$>
      (simulateQ (step
        (insAugmented pre application initial selector aux source writer prior (some parent) key target nonce next sender route read mark monitor)
        (Selected target owner ∘ insProject) owner number bit) (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run before =
    (simulateQ (step
      (PqxdhFirstRecordConfidentiality.trOriginal pre application initial selector aux source writer prior (some parent) key target nonce next sender route read mark)
      (Selected target owner) owner number bit) (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run (project insProject before) := by
  apply map_run_simulateQ_eq_of_query_map_eq
  exact step_project _ _ insProject
    (insAugmented_step pre application initial selector aux source writer prior (some parent) key target nonce next sender route read mark monitor)
    (Selected target owner) owner number bit

/-- Retain the public wrapper state on normal return and all private/component state on every return; an outer refusal has no continuing wrapper reply. -/
def close {Result : Type} (current : PqxdhRecordConfidentialityChallenge.State)
    (result : (Option (Result × PqxdhRecordConfidentialityChallenge.State) ×
      PqxdhLaterChallengeMonitor.State M P I D K A N C S B) × AdaptiveCtxDynamicKnownKeys.SourceState) :
    Option Result × State (InsFull M P I D K A N C S B) :=
  (result.1.1.map Prod.fst, (result.1.1.elim current Prod.snd, ((result.1.2.1, result.2), result.1.2.2)))

/-- Evaluating the executable marker callback gives the literal source-wrapper callback under the existing complete component interpreter. -/
theorem query_evaluated (key : RootOutput) (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (query : (AdvSpec extra S B).Domain) (current : PqxdhRecordConfidentialityChallenge.State)
    (before : InsFull M P I D K A N C S B) (choice : Option Bool) :
    close current <$> (simulateQ
      (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
      (runStepper (PqxdhLaterChallengeMonitor.handler pre application initial selector aux source writer prior parent target nonce next sender
        route read mark monitor owner number bit query) current (before.1, choice))).run before.2 =
    (step (insEvaluated pre application initial selector aux source writer prior (some parent) key target nonce next sender route read mark monitor)
      (Selected target owner ∘ insProject) owner number bit query).run (current, (before, choice)) := by
  have same := congrArg (fun action => action.run before)
    (insEvaluated_program pre application initial selector aux source writer prior (some parent) key target nonce next sender route read mark
      monitor ((PqxdhRecordConfidentialityChallenge.handler owner number bit query).run current))
  simp only [PqxdhSelectedStateInterpreter.evaluate, StateT.run] at same
  simp only [step, StateT.run]
  rw [← same]
  simp only [PqxdhLaterChallengeMonitor.handler, runStepper, OptionT.run_mk, simulateQ_map, Functor.map_map,
    PqxdhLaterChallengeTwin.handler, StateT.run, PqxdhSelectedFirstRecord.state_map_apply]
  rfl

/-- The existing optional translation executes a callback completely before either retaining refusal or entering the original reply-dependent continuation. -/
theorem optional_bind {κ σ Result : Type} {spec : OracleSpec κ}
    (impl : QueryImpl (RawCtxSelectedFamilyNonceCoupling.Optional spec) (StateT σ ProbComp))
    (query : spec.Domain) (continuation : spec.Range query → OracleComp spec Result) (before : σ) :
    (simulateQ impl (RawCtxSelectedFamilyNonceCoupling.optionalClient
      ((liftM (spec.query query)) >>= continuation))).run before =
    (do let result ← (impl query).run before
        match result.1 with
        | none => pure (none, result.2)
        | some reply => (simulateQ impl (RawCtxSelectedFamilyNonceCoupling.optionalClient (continuation reply))).run result.2) := by
  simp only [RawCtxSelectedFamilyNonceCoupling.optionalClient, simulateQ_bind, simulateQ_spec_query,
    OptionT.run_bind, Option.elimM, RawCtxSelectedFamilyNonceCoupling.optionalRequests, OptionT.run_mk, StateT.run_bind]
  congr 1
  funext result
  rcases result with ⟨_ | reply, after⟩ <;> rfl

/-- Reassociate the complete executable private and component state without removing any of its fields. -/
def pair {Result : Type}
    (result : (Option (Result × PqxdhRecordConfidentialityChallenge.State) ×
      PqxdhLaterChallengeMonitor.State M P I D K A N C S B) × AdaptiveCtxDynamicKnownKeys.SourceState) :
    Option (Result × PqxdhRecordConfidentialityChallenge.State) × (InsFull M P I D K A N C S B × Option Bool) :=
  (result.1.1, ((result.1.2.1, result.2), result.1.2.2))

/-- The original optional interface returns its wrapper state only on a normal reply. All private state, marker and component effects remain on refusal. -/
def finish {σ Result : Type} (result : Option Result × State σ) :
    Option (Result × PqxdhRecordConfidentialityChallenge.State) × (σ × Option Bool) :=
  (result.1.map (fun reply => (reply, result.2.1)), result.2.2)

/-- The full evaluated executable and original optional wrapper have the same complete result and private/component poststate, including every effect before refusal. -/
theorem program_evaluated {Result : Type} (key : RootOutput) (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (work : OracleComp (AdvSpec extra S B) Result) (current : PqxdhRecordConfidentialityChallenge.State)
    (before : InsFull M P I D K A N C S B) (choice : Option Bool) :
    pair <$> (simulateQ
      (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
      (runStepper (simulateQ (PqxdhLaterChallengeMonitor.handler pre application initial selector aux source writer prior parent target nonce next
        sender route read mark monitor owner number bit) work) current (before.1, choice))).run before.2 =
    finish <$> (simulateQ (step
      (insEvaluated pre application initial selector aux source writer prior (some parent) key target nonce next sender route read mark monitor)
      (Selected target owner ∘ insProject) owner number bit) (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run
      (current, (before, choice)) := by
  induction work using OracleComp.inductionOn generalizing current before choice with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, runStepper_bind, StateT.run_bind, map_bind, optional_bind]
    rw [← query_evaluated pre application initial selector aux source writer prior parent target nonce _ sender route read mark monitor
      key owner number bit query current before choice, bind_map_left]
    congr 1
    funext result
    rcases result with ⟨⟨_ | ⟨reply, current'⟩, ⟨inner, choice'⟩⟩, component⟩
    · rfl
    · exact ih reply current' (inner, component) choice'

end BeaconcryptCore.Computational.PqxdhLaterChallengeMonitorSource

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMonitorSource.selected_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMonitorSource.selected_native
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMonitorSource.step_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMonitorSource.step_project
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMonitorSource.record_executable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMonitorSource.record_executable
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMonitorSource.augmented_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMonitorSource.augmented_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMonitorSource.query_evaluated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMonitorSource.query_evaluated
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMonitorSource.optional_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMonitorSource.optional_bind
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMonitorSource.program_evaluated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMonitorSource.program_evaluated
