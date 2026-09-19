import BeaconcryptCore.Computational.PqxdhInitialParentObserverCompiler
import BeaconcryptCore.Computational.RawCtxSelectedParentPrivateRealization
import BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets

/-!
The ordinary later-parent observer keeps complete shared, identity and root-cache state. Its primitive interface has no selected-input argument: the unavailable chain is represented by a label, the challenger supplies the child output, and current-chain reads use the established mask. The original external callbacks and audited initializer remain explicit computations. Native-read interpretation is used only for the source equation. Candidate logging includes every audited initializer input and returned chain; the direct flag concerns only actual unavailable-chain reads.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialParentObserver
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open PqxdhInitialBeaconAmbient PqxdhInitialParentObserverCompiler
variable {ι I D K X Response Shared A N C α β Result : Type} {extra : OracleSpec ι} {S B : Nat}

abbrev State (A N C : Type) := (RawCtxSharedPrimitive.SharedState A × N) × C

def flatten (work : Ambient A N C α) : StateT (State A N C) ProbComp α := fun state =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$> work state.1 state.2

/-- Reassociation retains every ambient field on a pure source reply. -/
theorem flatten_pure (value : α) : flatten (pure value : Ambient A N C α) = pure value := rfl

/-- Every original effect and its source order are retained by the complete ambient reassociation. -/
theorem flatten_bind (work : Ambient A N C α) (next : α → Ambient A N C β) :
    flatten (work >>= next) = (flatten work >>= fun value => flatten (next value)) := by
  funext state
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (work state.1 state.2 >>= fun first => next first.1.1 first.1.2 first.2) =
    (((fun result => (result.1.1, (result.1.2, result.2))) <$> work state.1 state.2) >>=
      fun first => (fun result => (result.1.1, (result.1.2, result.2))) <$>
        next first.1 first.2.1 first.2.2)
  simp only [map_bind, bind_map_left]

/-- The complete adaptive source program retains all state and callbacks under the same tuple reassociation. -/
theorem flatten_program {κ : Type} {spec : OracleSpec κ}
    (impl : QueryImpl spec (Ambient A N C)) (client : OracleComp spec α) :
    simulateQ (fun query => flatten (impl query)) client = flatten (simulateQ impl client) := by
  induction client using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, flatten_bind, ih]

noncomputable def inputs : (Spec extra I D K X Response Shared).Domain → List RootOutput
  | .inl query => RawCtxSelectedLiveCompiler.inputs query
  | .inr (.inl _) => []
  | .inr (.inr reply) => candidates reply

def direct : (Spec extra I D K X Response Shared).Domain → Bool
  | .inl query => RawCtxSelectedParentReadMask.direct query
  | .inr _ => false

/-- Every available candidate is billed on the extended domain: initializer audits add at most three, primitive/read callbacks at most one, and external effects have their separate actual audit. -/
theorem inputs_length (query : (Spec extra I D K X Response Shared).Domain) :
    (inputs query).length ≤ 3 := by
  rcases query with query | (query | reply)
  · apply (RawCtxFamilyObservationBudgets.inputs_length query).trans
    cases RawCtxFamilyPrimitiveBudgets.liveClass query <;> decide
  · simp [inputs]
  · exact candidates_bound reply

section Interpreter
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
  (output : FullOutput)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))

noncomputable def old (reader : RawCtxSelectedLiveTrace.Reader) :
    QueryImpl RawCtxSelectedLiveCompiler.Spec (Ambient A N C) :=
  fun query => PqxdhInitialBeaconAmbient.lift
    (RawCtxSelectedParentLive.handler source writer prior entry output reader
      (RawCtxSelectedParentPrivateRealization.realView source) query)

noncomputable def handler (reader : RawCtxSelectedLiveTrace.Reader) :
    QueryImpl (Spec extra I D K X Response Shared) (StateT (State A N C) ProbComp) :=
  fun query => flatten (PqxdhInitialParentObserverCompiler.handler
    (old source writer prior entry output reader) pre application initial selector aux query)

noncomputable def observed (reader : RawCtxSelectedLiveTrace.Reader) :=
  RawCtxFlaggedQueryTrace.trace
    (handler source writer prior entry output pre application initial selector aux reader) inputs direct

/-- Every non-exposing original callback retains its complete reply and ambient effects; only actual unavailable-chain reads need the mask. -/
theorem query_safe (target : RootOutput) (query : (Spec extra I D K X Response Shared).Domain)
    (safe : direct query = false) :
    handler source writer prior entry output pre application initial selector aux
        (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) query =
      handler source writer prior entry output pre application initial selector aux RawCtxSelectedLiveRead.labelRead query := by
  cases query with
  | inl query =>
      change flatten (PqxdhInitialBeaconAmbient.lift (RawCtxSelectedParentLive.handler source writer prior entry output
          (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target))
          (RawCtxSelectedParentPrivateRealization.realView source) query)) = _
      rw [RawCtxSelectedParentReadMask.query_safe source writer prior entry output target
        (RawCtxSelectedParentPrivateRealization.realView source) query safe]
      rfl
  | inr query =>
      rcases query with (query | (reply | (secrets | (query | query)))) | reply
      all_goals rfl

/-- The complete original event agrees with its executable masked observer on the same unconditioned clear-bit event, including all initializer, selector and publication effects. -/
theorem event_good (target : RootOutput) (client : OracleComp (Spec extra I D K X Response Shared) Result)
    (state : (State A N C × List RootOutput) × Bool)
    (event : Result × ((State A N C × List RootOutput) × Bool) → Prop) :
    Pr[fun result => event result ∧ result.2.2 = false |
      (simulateQ (observed source writer prior entry output pre application initial selector aux
        (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target))) client).run state] =
      Pr[fun result => event result ∧ result.2.2 = false |
        (simulateQ (observed source writer prior entry output pre application initial selector aux
          RawCtxSelectedLiveRead.labelRead) client).run state] :=
  RawCtxFlaggedQueryAgreement.event_good _ _ inputs direct
    (query_safe source writer prior entry output pre application initial selector aux target) client state event

/-- The observer's pending primitive callbacks are exactly the existing retained-parent source interpreter, with full ambient state and real public HKDF. -/
theorem primitive_source (reader : RawCtxSelectedLiveTrace.Reader) :
    old (A := A) (N := N) (C := C) source writer prior entry output reader ∘ₛ RawCtxFamilyPendingCompiler.primitive =
      PqxdhInitialParentPost.labelPrimitive source writer prior entry (RawCtxKdfRequestTable.fullResponse output) := by
  funext query
  change simulateQ (fun query => PqxdhInitialBeaconAmbient.lift
      (RawCtxSelectedParentLive.handler source writer prior entry output reader
        (RawCtxSelectedParentPrivateRealization.realView source) query))
      (RawCtxFamilyPendingCompiler.primitive query) = _
  rw [PqxdhInitialBeaconAmbient.simulate_lift]
  apply congrArg PqxdhInitialBeaconAmbient.lift
  rcases query with (pending | opening) | ((pending | sealing) | (coin | (hash | view)))
  all_goals rfl

/-- Every original optional family read is the same native source lookup under the private label interpretation; missing owners still reject without a read callback. -/
theorem reader_source (target : RootOutput) :
    old (A := A) (N := N) (C := C) source writer prior entry output
        (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) ∘ₛ
      RawCtxFamilyReadCompiler.compiler (serverCount := S) (beaconCount := B) =
        PqxdhInitialParentPost.labelReader target := by
  funext query
  rcases query with ⟨request, kernel⟩
  cases request <;> cases kernel <;> rfl

/-- The literal audited full pending continuation equals the exact source label interpreter, retaining every ambient component and original native optional read. -/
theorem compiled_source (target : RootOutput)
    (client : OracleComp (PqxdhInitialPendingPost.Spec extra RawCtxSelectedChain.Slot I D K X Response Shared S B) Result) :
    simulateQ (handler source writer prior entry output pre application initial selector aux
      (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)))
      (simulateQ PqxdhInitialParentObserverCompiler.compiler client) =
      flatten (simulateQ (PqxdhInitialParentPost.labelHandler source writer prior entry target
        pre application (fun secrets => Prod.snd <$> initial secrets) selector aux
        (RawCtxKdfRequestTable.fullResponse output)) client) := by
  unfold handler
  rw [flatten_program, PqxdhInitialParentObserverCompiler.program_source,
    primitive_source, reader_source]
  congr 2
  funext query
  rcases query with query | (query | (reply | (secrets | (query | query))))
  all_goals try rfl
  simp only [PqxdhInitialParentPost.labelHandler, PqxdhInitialPendingPost.handler,
    PqxdhInitialParentPost.knownInitial, Functor.map_map]

end Interpreter

end BeaconcryptCore.Computational.PqxdhInitialParentObserver

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserver.flatten_pure' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserver.flatten_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserver.flatten_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserver.flatten_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserver.flatten_program' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserver.flatten_program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserver.inputs_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserver.inputs_length

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserver.query_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserver.query_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserver.event_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserver.event_good

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserver.primitive_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserver.primitive_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserver.reader_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserver.reader_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserver.compiled_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserver.compiled_source
