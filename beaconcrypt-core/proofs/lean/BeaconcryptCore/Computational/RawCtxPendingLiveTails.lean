import BeaconcryptCore.Computational.RawCtxGenericLiveRead
import BeaconcryptCore.Computational.RawCtxPendingOwnerTails
import BeaconcryptCore.Computational.RawCtxQueryOccurrenceComposition

/-!
The generic live frontend retains the original owner program, its full history and exposure state, and the original external live client. Selected pending continuations are classified from the actual compiled source syntax; no arbitrary retaggable native callback is supplied. This is source continuation provenance, separate from freshness and the cryptographic hybrid bound.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingLiveTails
open RawCtxGenericLiveRead RawCtxQueryOccurrence RawCtxQueryOccurrenceComposition

abbrev SourceSpec := RawCtxSelectedLiveTrace.SourceSpec
abbrev OwnerSourceSpec := RawCtxSelectedPublicTrace.SourceSpec

def selected {Chain : Type} : (Spec Chain).Domain → Bool
  | .inl query => RawCtxPendingMixedPrefix.ownerSelected query
  | .inr _ => false

noncomputable def program {Chain Metadata Result : Type} {serverCount beaconCount : Nat}
    (exposure : Exposure Chain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (client : OracleComp SourceSpec Result) (state : OuterState Chain Metadata serverCount beaconCount) :
    OracleComp (Spec Chain) (Result × OuterState Chain Metadata serverCount beaconCount) :=
  (simulateQ (compiler exposure sender decode owner) client).run state

noncomputable def afterOwner {Chain Metadata Value Result : Type} {serverCount beaconCount : Nat}
    (exposure : Exposure Chain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (history : RawCtxProtocolReveals.History serverCount beaconCount) (bad : Bool)
    (outside : Value → OracleComp SourceSpec Result)
    (result : Value × RawCtxChainOwner.State (RawCtxPendingOwnerQueries.Kernel Chain) Metadata) :
    OracleComp (Spec Chain) (Result × OuterState Chain Metadata serverCount beaconCount) :=
  program exposure sender decode owner (outside result.1) ((result.2, RawCtxProtocolReveals.tick history), bad)

noncomputable def liftOwner {Chain Metadata Value Result : Type} {serverCount beaconCount : Nat}
    (exposure : Exposure Chain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (history : RawCtxProtocolReveals.History serverCount beaconCount) (bad : Bool)
    (outside : Value → OracleComp SourceSpec Result)
    (run : OracleComp (RawCtxPendingOwnerQueries.Spec Chain)
      (Value × RawCtxChainOwner.State (RawCtxPendingOwnerQueries.Kernel Chain) Metadata)) :
    OracleComp (Spec Chain) (Result × OuterState Chain Metadata serverCount beaconCount) :=
  simulateQ primitiveForward run >>= afterOwner exposure sender decode owner history bad outside

inductive Tail {Chain Metadata Result : Type} {serverCount beaconCount : Nat}
    (exposure : Exposure Chain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) :
    (query : (Spec Chain).Domain) →
      ((Spec Chain).Range query → OracleComp (Spec Chain)
        (Result × OuterState Chain Metadata serverCount beaconCount)) → Prop where
  | original (request : OwnerSourceSpec.Domain)
      (history : RawCtxProtocolReveals.History serverCount beaconCount) (bad : Bool)
      (outside : OwnerSourceSpec.Range request → OracleComp SourceSpec Result)
      (query : (RawCtxPendingOwnerQueries.Spec Chain).Domain)
      (next : (RawCtxPendingOwnerQueries.Spec Chain).Range query → OracleComp
        (RawCtxPendingOwnerQueries.Spec Chain)
        (OwnerSourceSpec.Range request × RawCtxChainOwner.State (RawCtxPendingOwnerQueries.Kernel Chain) Metadata))
      (tail : RawCtxPendingOwnerTails.Tail sender decode query next) :
      Tail exposure sender decode owner (.inl query)
        (fun reply => liftOwner exposure sender decode owner history bad outside (next reply))

/-- Every original owner request finishes its actual owner computation before ticking history and resuming the same external live client. -/
theorem program_original {Chain Metadata Result : Type} {serverCount beaconCount : Nat}
    (exposure : Exposure Chain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (request : OwnerSourceSpec.Domain)
    (outside : OwnerSourceSpec.Range request → OracleComp SourceSpec Result)
    (state : OuterState Chain Metadata serverCount beaconCount) :
    program exposure sender decode owner (SourceSpec.query (.inl request) >>= outside) state =
      liftOwner exposure sender decode owner state.1.2 state.2 outside
        ((RawCtxPendingOwnerQueries.compiler sender decode request).run state.1.1) := by
  simp only [program, simulateQ_bind, simulateQ_spec_query]
  rw [StateT.run_bind]
  simp only [compiler, StateT.run, bind_assoc, pure_bind, liftOwner]
  rfl

/-- An actual live read updates the original observation history and exposure bit before the unchanged external client receives its optional reply. -/
theorem program_read {Chain Metadata Result : Type} {serverCount beaconCount : Nat}
    (exposure : Exposure Chain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (read : RawCtxSelectedLiveRead.Read)
    (outside : RawCtxSelectedLiveRead.ReadSpec.Range read → OracleComp SourceSpec Result)
    (state : OuterState Chain Metadata serverCount beaconCount) :
    program exposure sender decode owner (SourceSpec.query (.inr read) >>= outside) state =
      (((Spec Chain).query (.inr (read, some state.1.1.kernel)) :
        OracleComp (Spec Chain) (RawCtxSelectedLiveRead.ReadSpec.Range read)) >>= fun reply =>
        program exposure sender decode owner (outside reply)
          ((state.1.1, RawCtxProtocolReveals.note (RawCtxSelectedLiveRead.observation owner read reply) state.1.2),
            state.2 || exposure read (some state.1.1.kernel))) := by
  simp only [program, simulateQ_bind, simulateQ_spec_query]
  rw [StateT.run_bind]
  simp only [compiler, StateT.run, bind_assoc, pure_bind]

/-- Every selected occurrence of the actual full live source program has an original owner tail followed by the same history update and external live client. -/
theorem program_tail {Chain Metadata Result : Type} {serverCount beaconCount : Nat}
    (exposure : Exposure Chain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (client : OracleComp SourceSpec Result) (state : OuterState Chain Metadata serverCount beaconCount)
    (query : (Spec Chain).Domain)
    (next : (Spec Chain).Range query → OracleComp (Spec Chain)
      (Result × OuterState Chain Metadata serverCount beaconCount))
    (occurs : Occurs query next (program exposure sender decode owner client state))
    (chosen : selected query = true) : Tail exposure sender decode owner query next := by
  induction client using OracleComp.inductionOn generalizing state query next with
  | pure value => exact (pure_impossible query next (value, state) occurs).elim
  | query_bind request outside ih =>
    cases request with
    | inl request =>
      rw [program_original] at occurs
      change Occurs query next (simulateQ inlForward
        ((RawCtxPendingOwnerQueries.compiler sender decode request).run state.1.1) >>=
        afterOwner exposure sender decode owner state.1.2 state.2 outside) at occurs
      rcases bind_cases query next _ _ occurs with ⟨inner, inside, continuation⟩ | ⟨result, after⟩
      · rcases inl_cases query inner _ inside with ⟨originalQuery, originalNext, originalOccurs, same⟩
        have sameQuery := congrArg Sigma.fst same
        change query = .inl originalQuery at sameQuery
        have selectedOriginal : RawCtxPendingMixedPrefix.ownerSelected originalQuery = true := by
          simpa only [sameQuery, selected] using chosen
        have originalTail := RawCtxPendingOwnerTails.program_tail sender decode
          (OwnerSourceSpec.query request : OracleComp OwnerSourceSpec (OwnerSourceSpec.Range request))
          state.1.1 originalQuery originalNext
          (by simpa only [RawCtxPendingOwnerTails.program, simulateQ_spec_query] using originalOccurs)
          selectedOriginal
        rw [continuation]
        exact (congrArg (fun pair : Σ q, (Spec Chain).Range q → OracleComp (Spec Chain)
          (OwnerSourceSpec.Range request × RawCtxPendingOwnerTails.Owner Chain Metadata) =>
            Tail exposure sender decode owner pair.1 (fun reply => pair.2 reply >>=
              afterOwner exposure sender decode owner state.1.2 state.2 outside)) same).mpr
          (Tail.original request state.1.2 state.2 outside originalQuery originalNext originalTail)
      · exact ih result.1 ((result.2, RawCtxProtocolReveals.tick state.1.2), state.2) query next after chosen
    | inr read =>
      rw [program_read] at occurs
      rcases query_cases query (.inr (read, some state.1.1.kernel)) next _ occurs with same | ⟨reply, after⟩
      · have sameQuery := congrArg Sigma.fst same
        change query = .inr (read, some state.1.1.kernel) at sameQuery
        rw [sameQuery] at chosen
        cases chosen
      · exact ih reply
          ((state.1.1, RawCtxProtocolReveals.note (RawCtxSelectedLiveRead.observation owner read reply) state.1.2),
            state.2 || exposure read (some state.1.1.kernel)) query next after chosen

/-- The generic private selector specializes to the original mixed live scanner's exact send/receive callback classes. -/
theorem selected_slot : selected (Chain := RawCtxSelectedChain.Slot) = RawCtxPendingMixedPrefix.liveSelected := by
  funext query
  cases query <;> rfl

/-- A supported stop of the actual full live source program supplies its concrete original owner and external-client tail without any separately assumed continuation property. -/
theorem reached_tail {Chain Metadata Result Base : Type} {serverCount beaconCount : Nat}
    (exposure : Exposure Chain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (impl : QueryImpl (Spec Chain) (StateT Base ProbComp))
    (client : OracleComp SourceSpec Result) (state : OuterState Chain Metadata serverCount beaconCount)
    (index : Nat) (initial reached : Base) (query : (Spec Chain).Domain)
    (next : (Spec Chain).Range query → OracleComp (Spec Chain)
      (Result × OuterState Chain Metadata serverCount beaconCount))
    (supported : (RawCtxPendingMixedPrefix.Stopped.pending query next, reached) ∈ support
      (RawCtxPendingMixedPrefix.scan selected impl (program exposure sender decode owner client state) index initial)) :
    Tail exposure sender decode owner query next :=
  program_tail exposure sender decode owner client state query next
    (scan_occurs selected impl _ index initial reached query next supported)
    (RawCtxPendingMixedPrefix.pending_selected selected impl _ index initial reached query next supported)

end BeaconcryptCore.Computational.RawCtxPendingLiveTails

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingLiveTails.program_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingLiveTails.program_original

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingLiveTails.program_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingLiveTails.program_read

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingLiveTails.program_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingLiveTails.program_tail

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingLiveTails.selected_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingLiveTails.selected_slot

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingLiveTails.reached_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingLiveTails.reached_tail
