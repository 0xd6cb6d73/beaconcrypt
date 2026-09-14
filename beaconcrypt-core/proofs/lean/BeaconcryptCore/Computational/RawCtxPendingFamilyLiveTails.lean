import BeaconcryptCore.Computational.RawCtxPendingFamilyLiveQueries
import BeaconcryptCore.Computational.RawCtxQueryOccurrenceComposition

/-!
The actual original live client retains both complete role families and its timestamped read history through a selected private pending KDF. Source syntax derives the original family tail and complete external live continuation. The private read payload retains the original owner selection; the original optional reply is noted before the outside client resumes. No arbitrary native continuation or target-free-state premise is supplied.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingFamilyLiveTails
open RawCtxPendingFamilyLiveQueries RawCtxGenericFamilyRead RawCtxQueryOccurrence RawCtxQueryOccurrenceComposition

abbrev SourceSpec := RawCtxProtocolReveals.SourceSpec
abbrev FamilySourceSpec := RawCtxProtocolRoles.SourceSpec

def selected {Chain : Type} {serverCount beaconCount : Nat} : (Spec Chain serverCount beaconCount).Domain → Bool
  | .inl query => RawCtxPendingMixedPrefix.ownerSelected query
  | .inr _ => false

noncomputable def program {Chain Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result)
    (state : State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    OracleComp (Spec Chain serverCount beaconCount)
      (Result × State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :=
  (simulateQ (compiler sender route decode) client).run state

noncomputable def afterFamily {Chain Metadata PeerMetadata Identity DhPair KemPair Value Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (history : RawCtxProtocolReveals.History serverCount beaconCount)
    (outside : Value → OracleComp (SourceSpec serverCount beaconCount) Result)
    (result : Value × RawCtxPendingFamilyTails.State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    OracleComp (Spec Chain serverCount beaconCount)
      (Result × State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :=
  program sender route decode (outside result.1) (result.2, RawCtxProtocolReveals.tick history)

noncomputable def liftFamily {Chain Metadata PeerMetadata Identity DhPair KemPair Value Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (history : RawCtxProtocolReveals.History serverCount beaconCount)
    (outside : Value → OracleComp (SourceSpec serverCount beaconCount) Result)
    (work : OracleComp (RawCtxPendingOwnerQueries.Spec Chain)
      (Value × RawCtxPendingFamilyTails.State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)) :
    OracleComp (Spec Chain serverCount beaconCount)
      (Result × State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :=
  simulateQ primitiveForward work >>= afterFamily sender route decode history outside

inductive Tail {Chain Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    (query : (Spec Chain serverCount beaconCount).Domain) →
      ((Spec Chain serverCount beaconCount).Range query → OracleComp (Spec Chain serverCount beaconCount)
        (Result × State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)) → Prop where
  | original (request : (FamilySourceSpec serverCount beaconCount).Domain)
      (history : RawCtxProtocolReveals.History serverCount beaconCount)
      (outside : (FamilySourceSpec serverCount beaconCount).Range request → OracleComp (SourceSpec serverCount beaconCount) Result)
      (query : (RawCtxPendingOwnerQueries.Spec Chain).Domain)
      (inner : (RawCtxPendingOwnerQueries.Spec Chain).Range query → OracleComp (RawCtxPendingOwnerQueries.Spec Chain)
        ((FamilySourceSpec serverCount beaconCount).Range request ×
          RawCtxPendingFamilyTails.State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount))
      (origin : RawCtxPendingFamilyTails.Tail sender route decode query inner) :
      Tail sender route decode (.inl query)
        (fun reply => liftFamily sender route decode history outside (inner reply))

/-- Every original role operation finishes its exact family program before ticking the original history and resuming the outside live client. -/
theorem program_original {Chain Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : (FamilySourceSpec serverCount beaconCount).Domain)
    (outside : (FamilySourceSpec serverCount beaconCount).Range request → OracleComp (SourceSpec serverCount beaconCount) Result)
    (state : State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    program sender route decode
      (((SourceSpec serverCount beaconCount).query (.inl request) : OracleComp (SourceSpec serverCount beaconCount) _) >>= outside) state =
      liftFamily sender route decode state.2 outside
        ((RawCtxGenericFamilyFrontend.impl RawCtxPendingOwnerQueries.calls RawCtxPendingOwnerQueries.publicForward
          sender route decode request).run state.1) := by
  simp only [program, simulateQ_bind, simulateQ_spec_query]
  rw [StateT.run_bind]
  simp only [compiler, StateT.run, bind_assoc, pure_bind, liftFamily]
  rfl

/-- The actual live read uses the requested current optional kernel and records its exact optional reply before continuing. -/
theorem program_read {Chain Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : (RawCtxProtocolReveals.RevealSpec serverCount beaconCount).Domain)
    (outside : (RawCtxProtocolReveals.RevealSpec serverCount beaconCount).Range request → OracleComp (SourceSpec serverCount beaconCount) Result)
    (state : State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    program sender route decode
      (((SourceSpec serverCount beaconCount).query (.inr request) : OracleComp (SourceSpec serverCount beaconCount) _) >>= outside) state =
      (((Spec Chain serverCount beaconCount).query
        (.inr (request, RawCtxGenericRoleFamily.selectedKernel (requestOwner request) state.1)) :
          OracleComp (Spec Chain serverCount beaconCount) _) >>= fun reply =>
        program sender route decode (outside reply) (state.1, RawCtxProtocolReveals.note ⟨request, reply⟩ state.2)) := by
  simp only [program, simulateQ_bind, simulateQ_spec_query]
  rw [StateT.run_bind]
  simp only [compiler, StateT.run, bind_assoc, pure_bind]

/-- Every selected query in the actual full LIVE source schedule derives its original family tail, unchanged history and complete outside LIVE client. -/
theorem program_tail {Chain Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result)
    (state : State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (query : (Spec Chain serverCount beaconCount).Domain)
    (next : (Spec Chain serverCount beaconCount).Range query → OracleComp (Spec Chain serverCount beaconCount)
      (Result × State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount))
    (occurs : Occurs query next (program sender route decode client state))
    (chosen : selected query = true) : Tail sender route decode query next := by
  induction client using OracleComp.inductionOn generalizing state query next with
  | pure value => exact (pure_impossible query next (value, state) occurs).elim
  | query_bind request outside ih =>
    cases request with
    | inl request =>
      rw [program_original sender route decode request outside state] at occurs
      change Occurs query next (simulateQ inlForward
        ((RawCtxGenericFamilyFrontend.impl RawCtxPendingOwnerQueries.calls RawCtxPendingOwnerQueries.publicForward
          sender route decode request).run state.1) >>= afterFamily sender route decode state.2 outside) at occurs
      rcases bind_cases query next _ _ occurs with ⟨inner, inside, continuation⟩ | ⟨result, after⟩
      · rcases inl_cases query inner _ inside with ⟨originalQuery, originalNext, originalOccurs, same⟩
        have sameQuery := congrArg Sigma.fst same
        change query = .inl originalQuery at sameQuery
        have selectedOriginal : RawCtxPendingMixedPrefix.ownerSelected originalQuery = true := by
          simpa only [sameQuery, selected] using chosen
        have originalTail := RawCtxPendingFamilyTails.program_tail sender route decode
          ((FamilySourceSpec serverCount beaconCount).query request :
            OracleComp (FamilySourceSpec serverCount beaconCount) ((FamilySourceSpec serverCount beaconCount).Range request))
          state.1 originalQuery originalNext
          (by simpa only [RawCtxPendingFamilyTails.program, simulateQ_spec_query] using originalOccurs)
          selectedOriginal
        rw [continuation]
        exact (congrArg (fun pair : Σ q, (Spec Chain serverCount beaconCount).Range q →
          OracleComp (Spec Chain serverCount beaconCount)
            ((FamilySourceSpec serverCount beaconCount).Range request ×
              RawCtxPendingFamilyTails.State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) =>
                Tail sender route decode pair.1 (fun reply => pair.2 reply >>= afterFamily sender route decode state.2 outside)) same).mpr
          (Tail.original request state.2 outside originalQuery originalNext originalTail)
      · exact ih result.1 (result.2, RawCtxProtocolReveals.tick state.2) query next after chosen
    | inr request =>
      rw [program_read sender route decode request outside state] at occurs
      rcases query_cases query (.inr (request, RawCtxGenericRoleFamily.selectedKernel (requestOwner request) state.1)) next _ occurs
        with same | ⟨reply, after⟩
      · have sameQuery := congrArg Sigma.fst same
        change query = .inr (request, RawCtxGenericRoleFamily.selectedKernel (requestOwner request) state.1) at sameQuery
        rw [sameQuery] at chosen
        cases chosen
      · exact ih reply (state.1, RawCtxProtocolReveals.note ⟨request, reply⟩ state.2) query next after chosen

/-- A supported cut of the actual complete LIVE program derives its concrete original family and outside-client tail, retaining the same reached primitive state. -/
theorem reached_tail {Chain Metadata PeerMetadata Identity DhPair KemPair Result PrimitiveState : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result)
    (state : State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (impl : QueryImpl (Spec Chain serverCount beaconCount) (StateT PrimitiveState ProbComp)) (index : Nat)
    (initial reached : PrimitiveState) (query : (Spec Chain serverCount beaconCount).Domain)
    (next : (Spec Chain serverCount beaconCount).Range query → OracleComp (Spec Chain serverCount beaconCount)
      (Result × State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount))
    (supported : (RawCtxPendingMixedPrefix.Stopped.pending query next, reached) ∈ support
      (RawCtxPendingMixedPrefix.scan selected impl (program sender route decode client state) index initial)) :
    Tail sender route decode query next :=
  program_tail sender route decode client state query next
    (scan_occurs selected impl _ index initial reached query next supported)
    (RawCtxPendingMixedPrefix.pending_selected selected impl _ index initial reached query next supported)

end BeaconcryptCore.Computational.RawCtxPendingFamilyLiveTails

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingFamilyLiveTails.program_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingFamilyLiveTails.program_original

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingFamilyLiveTails.program_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingFamilyLiveTails.program_read

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingFamilyLiveTails.program_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingFamilyLiveTails.program_tail

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingFamilyLiveTails.reached_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingFamilyLiveTails.reached_tail
