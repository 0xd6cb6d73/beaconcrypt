import BeaconcryptCore.Computational.PqxdhInitialHalfObserverCompiler
import BeaconcryptCore.Computational.PqxdhInitialParentObserver
import BeaconcryptCore.Computational.RawCtxSelectedParentPrivateRealization
import BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets

/-!
The first-half observer keeps the exact full source builder and post program, original ambient effects, and the known/hidden optional kernels returned by the selected initializer service. Available initializer inputs and chains are audited without interpreting the unavailable half. Only original reads of that half set the direct flag; the public HKDF view remains the real source function.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialHalfObserver
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open PqxdhInitialBeaconAmbient PqxdhInitialHalfObserverCompiler
variable {ι I D K X Response Shared A N C α β Result : Type} {extra : OracleSpec ι} {S B : Nat}

open PqxdhInitialParentObserver (State flatten flatten_program)

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
  fun query => flatten (PqxdhInitialHalfObserverCompiler.handler
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
      (simulateQ PqxdhInitialHalfObserverCompiler.compiler client) =
      flatten (simulateQ (PqxdhInitialPendingPost.handler
        (PqxdhInitialParentPost.labelPrimitive source writer prior entry (RawCtxKdfRequestTable.fullResponse output))
        (PqxdhInitialParentPost.labelReader target) pre application
        (fun secrets => Prod.snd <$> initial secrets) selector aux) client) := by
  unfold handler
  rw [flatten_program, PqxdhInitialHalfObserverCompiler.program_source,
    primitive_source, reader_source]

end Interpreter

end BeaconcryptCore.Computational.PqxdhInitialHalfObserver

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfObserver.inputs_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfObserver.inputs_length

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfObserver.query_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfObserver.query_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfObserver.event_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfObserver.event_good

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfObserver.primitive_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfObserver.primitive_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfObserver.reader_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfObserver.reader_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfObserver.compiled_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfObserver.compiled_source
