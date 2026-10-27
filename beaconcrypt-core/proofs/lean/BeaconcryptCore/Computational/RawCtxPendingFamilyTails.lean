import BeaconcryptCore.Computational.RawCtxGenericFamilyFrontend
import BeaconcryptCore.Computational.RawCtxPendingServerTails

/-!
A pending private KDF in the actual replicated role frontend keeps the complete original role family and its original outside family client. Server witnesses retain their original assigned-peer program; Beacon witnesses retain the exact established controls and associated data. The inner source tail is derived rather than supplied as an arbitrary native function. These operational source provenance statements do not assert freshness, independent keys or secrecy.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingFamilyTails
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily RawCtxPendingOwnerQueries
open RawCtxQueryOccurrence

abbrev State (Chain Metadata PeerMetadata Identity DhPair KemPair : Type) (serverCount beaconCount : Nat) :=
  Roles (Kernel Chain) Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount
abbrev SourceSpec := RawCtxProtocolRoles.SourceSpec

noncomputable def program {Chain Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result)
    (state : State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    OracleComp (Spec Chain) (Result × State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :=
  (simulateQ (RawCtxGenericFamilyFrontend.impl calls publicForward sender route decode) client).run state

noncomputable def afterServer {Chain Metadata PeerMetadata Identity DhPair KemPair Value Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (before : State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) (index : Fin serverCount)
    (outside : Value → OracleComp (SourceSpec serverCount beaconCount) Result)
    (result : Value × RawCtxPendingServerTails.State Chain Metadata PeerMetadata) :
    OracleComp (Spec Chain) (Result × State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :=
  program sender route decode (outside result.1) (Function.update before.1 index result.2, before.2)

noncomputable def liftServer {Chain Metadata PeerMetadata Identity DhPair KemPair Value Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (before : State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) (index : Fin serverCount)
    (outside : Value → OracleComp (SourceSpec serverCount beaconCount) Result)
    (work : OracleComp (Spec Chain) (Value × RawCtxPendingServerTails.State Chain Metadata PeerMetadata)) :
    OracleComp (Spec Chain) (Result × State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :=
  work >>= afterServer sender route decode before index outside

noncomputable def afterBeacon {Chain Metadata PeerMetadata Identity DhPair KemPair Value Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (before : State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) (index : Fin beaconCount)
    (control : pqxdh.BeaconEstablished) (associatedData : Array Std.U8 281#usize)
    (outside : Value → OracleComp (SourceSpec serverCount beaconCount) Result)
    (result : Value × RawCtxPendingOwnerTails.Owner Chain Unit) :
    OracleComp (Spec Chain) (Result × State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :=
  program sender route decode (outside result.1)
    (before.1, Function.update before.2 index (RawCtxGenericBeacon.reinstall (before.2 index) control associatedData result.2))

noncomputable def liftBeacon {Chain Metadata PeerMetadata Identity DhPair KemPair Value Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (before : State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) (index : Fin beaconCount)
    (control : pqxdh.BeaconEstablished) (associatedData : Array Std.U8 281#usize)
    (outside : Value → OracleComp (SourceSpec serverCount beaconCount) Result)
    (work : OracleComp (Spec Chain) (Value × RawCtxPendingOwnerTails.Owner Chain Unit)) :
    OracleComp (Spec Chain) (Result × State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :=
  work >>= afterBeacon sender route decode before index control associatedData outside

inductive Tail {Chain Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    (query : (Spec Chain).Domain) → ((Spec Chain).Range query → OracleComp (Spec Chain)
      (Result × State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)) → Prop where
  | server (request : RawCtxServerMixed.SourceSpec.Domain)
      (before : State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) (index : Fin serverCount)
      (outside : RawCtxServerMixed.SourceSpec.Range request → OracleComp (SourceSpec serverCount beaconCount) Result)
      (query : (Spec Chain).Domain)
      (inner : (Spec Chain).Range query → OracleComp (Spec Chain)
        (RawCtxServerMixed.SourceSpec.Range request × RawCtxPendingServerTails.State Chain Metadata PeerMetadata))
      (origin : RawCtxPendingServerTails.Tail sender route decode query inner) :
      Tail sender route decode query (fun reply => liftServer sender route decode before index outside (inner reply))
  | beacon (request : RawCtxMixedOwner.SourceSpec.Domain)
      (before : State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) (index : Fin beaconCount)
      (control : pqxdh.BeaconEstablished) (associatedData : Array Std.U8 281#usize)
      (outside : RawCtxMixedOwner.SourceSpec.Range request → OracleComp (SourceSpec serverCount beaconCount) Result)
      (query : (Spec Chain).Domain)
      (inner : (Spec Chain).Range query → OracleComp (Spec Chain)
        (RawCtxMixedOwner.SourceSpec.Range request × RawCtxPendingOwnerTails.Owner Chain Unit))
      (origin : RawCtxPendingOwnerTails.Tail (before.2 index).beacon.identityKeyId decode query inner) :
      Tail sender route decode query (fun reply => liftBeacon sender route decode before index control associatedData outside (inner reply))

private theorem server_occurs {Chain Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : RawCtxServerMixed.SourceSpec.Domain)
    (before : State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) (index : Fin serverCount)
    (outside : RawCtxServerMixed.SourceSpec.Range request → OracleComp (SourceSpec serverCount beaconCount) Result)
    (outsideGood : ∀ result query next, Occurs query next (afterServer sender route decode before index outside result) →
      RawCtxPendingMixedPrefix.ownerSelected query = true → Tail sender route decode query next)
    (query : (Spec Chain).Domain)
    (next : (Spec Chain).Range query → OracleComp (Spec Chain)
      (Result × State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount))
    (occurs : Occurs query next (liftServer sender route decode before index outside
      (RawCtxPendingServerTails.program sender route decode (RawCtxServerMixed.SourceSpec.query request) (before.1 index))))
    (selected : RawCtxPendingMixedPrefix.ownerSelected query = true) : Tail sender route decode query next := by
  rcases RawCtxQueryOccurrenceComposition.bind_cases query next _ _ occurs with inside | continued
  · rcases inside with ⟨inner, innerOccurs, same⟩
    subst next
    exact Tail.server request before index outside query inner
      (RawCtxPendingServerTails.program_tail sender route decode _ (before.1 index) query inner innerOccurs selected)
  · rcases continued with ⟨result, nextOccurs⟩
    exact outsideGood result query next nextOccurs selected

private theorem beacon_occurs {Chain Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : RawCtxMixedOwner.SourceSpec.Domain)
    (before : State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) (index : Fin beaconCount)
    (control : pqxdh.BeaconEstablished) (associatedData : Array Std.U8 281#usize) (kernel : Kernel Chain)
    (outside : RawCtxMixedOwner.SourceSpec.Range request → OracleComp (SourceSpec serverCount beaconCount) Result)
    (outsideGood : ∀ result query next, Occurs query next (afterBeacon sender route decode before index control associatedData outside result) →
      RawCtxPendingMixedPrefix.ownerSelected query = true → Tail sender route decode query next)
    (query : (Spec Chain).Domain)
    (next : (Spec Chain).Range query → OracleComp (Spec Chain)
      (Result × State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount))
    (occurs : Occurs query next (liftBeacon sender route decode before index control associatedData outside
      (RawCtxPendingOwnerTails.program (before.2 index).beacon.identityKeyId decode
        (RawCtxSelectedPublicTrace.SourceSpec.query (.inl request))
        (RawCtxGenericBeacon.selected (before.2 index) control associatedData kernel))))
    (selected : RawCtxPendingMixedPrefix.ownerSelected query = true) : Tail sender route decode query next := by
  rcases RawCtxQueryOccurrenceComposition.bind_cases query next _ _ occurs with inside | continued
  · rcases inside with ⟨inner, innerOccurs, same⟩
    subst next
    exact Tail.beacon request before index control associatedData outside query inner
      (RawCtxPendingOwnerTails.program_tail (before.2 index).beacon.identityKeyId decode _ _ query inner innerOccurs selected)
  · rcases continued with ⟨result, nextOccurs⟩
    exact outsideGood result query next nextOccurs selected

/-- Each complete role/public operation precedes the original adaptive family continuation. -/
theorem program_query {Chain Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : (SourceSpec serverCount beaconCount).Domain)
    (outside : (SourceSpec serverCount beaconCount).Range request → OracleComp (SourceSpec serverCount beaconCount) Result)
    (state : State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    program sender route decode (((SourceSpec serverCount beaconCount).query request : OracleComp (SourceSpec serverCount beaconCount) _) >>= outside) state =
      (do let result ← (RawCtxGenericFamilyFrontend.impl calls publicForward sender route decode request).run state
          program sender route decode (outside result.1) result.2) := rfl

/-- A Server operation retains the exact selected Server program before replacing only its original family index. -/
theorem server_selected {Chain Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : RawCtxServerMixed.SourceSpec.Domain) (index : Fin serverCount)
    (outside : RawCtxServerMixed.SourceSpec.Range request → OracleComp (SourceSpec serverCount beaconCount) Result)
    (state : State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    program sender route decode (((SourceSpec serverCount beaconCount).query (.inl ⟨index, request⟩) : OracleComp (SourceSpec serverCount beaconCount) _) >>= outside) state =
      liftServer sender route decode state index outside
        (RawCtxPendingServerTails.program sender route decode (RawCtxServerMixed.SourceSpec.query request) (state.1 index)) := by
  rw [program_query sender route decode (.inl ⟨index, request⟩) outside state]
  simp [StateT.run, RawCtxGenericFamilyFrontend.impl, liftServer, RawCtxPendingServerTails.program]
  rfl

/-- An active Beacon operation retains its actual established controls and owner program before whole-family publication. -/
theorem beacon_selected {Chain Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : RawCtxMixedOwner.SourceSpec.Domain) (index : Fin beaconCount)
    (control : pqxdh.BeaconEstablished) (associatedData : Array Std.U8 281#usize) (kernel : Kernel Chain)
    (outside : RawCtxMixedOwner.SourceSpec.Range request → OracleComp (SourceSpec serverCount beaconCount) Result)
    (state : State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (active : (state.2 index).beacon.phase = .established control associatedData kernel) :
    program sender route decode (((SourceSpec serverCount beaconCount).query (.inr (.inl ⟨index, request⟩)) : OracleComp (SourceSpec serverCount beaconCount) _) >>= outside) state =
      liftBeacon sender route decode state index control associatedData outside
        (RawCtxPendingOwnerTails.program (state.2 index).beacon.identityKeyId decode
          (RawCtxSelectedPublicTrace.SourceSpec.query (.inl request))
          (RawCtxGenericBeacon.selected (state.2 index) control associatedData kernel)) := by
  rw [program_query sender route decode (.inr (.inl ⟨index, request⟩)) outside state]
  simp [StateT.run, RawCtxGenericFamilyFrontend.impl, RawCtxGenericBeacon.impl, active,
    liftBeacon, RawCtxPendingOwnerTails.program, RawCtxPendingOwnerQueries.compiler]
  rfl

/-- Every selected private query in the actual mixed role-family schedule has a concrete original Server or Beacon tail and full outside family client. -/
theorem program_tail {Chain Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result)
    (state : State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (query : (Spec Chain).Domain)
    (next : (Spec Chain).Range query → OracleComp (Spec Chain)
      (Result × State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount))
    (occurs : Occurs query next (program sender route decode client state))
    (selected : RawCtxPendingMixedPrefix.ownerSelected query = true) : Tail sender route decode query next := by
  induction client using OracleComp.inductionOn generalizing state query next with
  | pure value => exact (pure_impossible query next (value, state) occurs).elim
  | query_bind request outside ih =>
    rcases request with ⟨index, request⟩ | (⟨index, request⟩ | publicQuery)
    · rw [server_selected sender route decode request index outside state] at occurs
      exact server_occurs sender route decode request state index outside
        (fun result innerQuery innerNext innerOccurs innerSelected =>
          ih result.1 (Function.update state.1 index result.2, state.2) innerQuery innerNext innerOccurs innerSelected)
        query next occurs selected
    · cases active : (state.2 index).beacon.phase
      case established control associatedData kernel =>
        rw [beacon_selected sender route decode request index control associatedData kernel outside state active] at occurs
        exact beacon_occurs sender route decode request state index control associatedData kernel outside
          (fun result innerQuery innerNext innerOccurs innerSelected =>
            ih result.1 (state.1, Function.update state.2 index (RawCtxGenericBeacon.reinstall (state.2 index) control associatedData result.2))
              innerQuery innerNext innerOccurs innerSelected)
          query next occurs selected
      all_goals
        rw [program_query sender route decode (.inr (.inl ⟨index, request⟩)) outside state] at occurs
        simp only [StateT.run, RawCtxGenericFamilyFrontend.impl, RawCtxGenericBeacon.impl, active,
          pure_bind] at occurs
        exact ih (RawCtxGenericBeacon.rejected request (state.2 index)).1
          (state.1, Function.update state.2 index (RawCtxGenericBeacon.rejected request (state.2 index)).2)
          query next occurs selected
    · rw [program_query sender route decode (.inr (.inr publicQuery)) outside state] at occurs
      simp only [StateT.run, RawCtxGenericFamilyFrontend.impl, publicForward, bind_assoc, pure_bind] at occurs
      rcases query_cases query (.inr (.inr publicQuery)) next _ occurs with current | following
      · have same : query = .inr (.inr publicQuery) := congrArg Sigma.fst current
        subst query
        simp only [RawCtxPendingMixedPrefix.ownerSelected, Bool.false_eq_true] at selected
      · rcases following with ⟨reply, continued⟩
        exact ih reply state query next continued selected

/-- The same actual supported family prefix yields its concrete pending role tail while retaining the complete reached primitive state. -/
theorem reached_tail {Chain Metadata PeerMetadata Identity DhPair KemPair Result PrimitiveState : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result)
    (roles : State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (impl : QueryImpl (Spec Chain) (StateT PrimitiveState ProbComp)) (index : Nat)
    (initial reached : PrimitiveState) (query : (Spec Chain).Domain)
    (next : (Spec Chain).Range query → OracleComp (Spec Chain)
      (Result × State Chain Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount))
    (supported : (RawCtxPendingMixedPrefix.Stopped.pending query next, reached) ∈
      support (RawCtxPendingMixedPrefix.scan RawCtxPendingMixedPrefix.ownerSelected impl
        (program sender route decode client roles) index initial)) : Tail sender route decode query next := by
  exact program_tail sender route decode client roles query next
    (RawCtxQueryOccurrence.scan_occurs _ impl _ index initial reached query next supported)
    (RawCtxPendingMixedPrefix.pending_selected _ impl _ index initial reached query next supported)

end BeaconcryptCore.Computational.RawCtxPendingFamilyTails

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingFamilyTails.program_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingFamilyTails.program_query

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingFamilyTails.server_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingFamilyTails.server_selected

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingFamilyTails.beacon_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingFamilyTails.beacon_selected

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingFamilyTails.program_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingFamilyTails.program_tail

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingFamilyTails.reached_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingFamilyTails.reached_tail
