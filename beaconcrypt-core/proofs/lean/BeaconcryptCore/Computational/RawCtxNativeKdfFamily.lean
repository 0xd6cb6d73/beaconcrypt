import BeaconcryptCore.Computational.RawCtxKdfRequestTable
import BeaconcryptCore.Computational.RawCtxRevealBudgets

/-!
The actual fixed-HKDF backend factors through one complete-stream table. The complete finite Server/Beacon role and reveal program retains original optional replies, all source history and the entire shared CTX/auxiliary state. Failed and repeated source operations are included. The fixed-source uniform ledger is unchanged.

All chain payloads and memoization state remain private source/analysis context. This equality does not hide a selected chain from an observer, replace public HKDF by a random function, assume fresh inputs or independently sampled owners, or add snapshot/restore coverage. Its supplied fixed functional/native primitive contracts and local deterministic work remain explicit.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxNativeKdfFamily
open PqxdhJointKdf PqxdhJointKdfGame RawCtxKdfRequestTable

abbrev FamilySpec := RawCtxServerServices.BackendSpec + JointKdfRO

/-- Actual private and public evaluations share complete streams at their unchanged addresses. -/
def compiler : QueryImpl RawCtxServerServices.BackendSpec (OracleComp FamilySpec)
  | .inl coin => FamilySpec.query (.inl (.inl coin))
  | .inr (.inl (.inl request)) =>
      fullResponse <$> FamilySpec.query (.inr (address request))
  | .inr (.inl (.inr request)) =>
      FamilySpec.query (.inl (.inr (.inl (.inr request))))
  | .inr (.inr view) => view.project <$> FamilySpec.query (.inr view.address)

/-- Source interpretation discharges the whole original backend equation. -/
theorem compiler_real {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) :
    directImpl source (RawCtxProtocolBackend.backend (Auxiliary := Auxiliary) source writer) ∘ₛ compiler =
      RawCtxProtocolBackend.backend source writer := by
  funext query
  rcases query with coin | ((request | request) | view) <;>
    first | rfl | simp [QueryImpl.compose, compiler, directImpl, OracleSpec.query]

/-- The exact native backend is the one-table computation before any output or state projection. -/
theorem backend_complete {Auxiliary Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (client : OracleComp RawCtxServerServices.BackendSpec Result)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) (table : Table)
    (consistent : Consistent source table) :
    (simulateQ (RawCtxProtocolBackend.backend source writer) client).run state =
      (fun result => (result.1, result.2.1)) <$>
        (simulateQ (tableImpl source (RawCtxProtocolBackend.backend source writer))
          (simulateQ compiler client)).run (state, table) := by
  simpa only [← QueryImpl.simulateQ_compose, compiler_real] using
    table_complete source (RawCtxProtocolBackend.backend source writer)
      (simulateQ compiler client) state table consistent

/-- Compile the actual replicated role/reveal program, preserving its entire returned private state. -/
noncomputable def program {Metadata PeerMetadata Identity DhPair KemPair Result : Type}
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    OracleComp FamilySpec (Result × RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :=
  simulateQ compiler ((simulateQ (RawCtxProtocolReveals.protocolImpl serverCount beaconCount senderId route decode) client).run state)

/-- Both native directions, skipped/retried receives, public evaluations and original reveal replies use the same table. -/
theorem source_complete {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (table : Table)
    (consistent : Consistent source table) :
    (fun result => ((result.1, result.2.1), result.2.2)) <$>
      (simulateQ (RawCtxProtocolReveals.sourceImpl source writer serverCount beaconCount senderId route decode) client).run
        (state, primitive) =
      (fun result => (result.1, result.2.1)) <$>
        (simulateQ (tableImpl source (RawCtxProtocolBackend.backend source writer))
          (program serverCount beaconCount senderId route decode client state)).run (primitive, table) := by
  rw [← RawCtxProtocolReveals.schedule_interpretation, backend_complete source writer _ primitive table consistent]
  rfl

/-- Memoization preserves the source's complete underlying uniform ledger, including every failed receive. -/
theorem source_uniform {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (table : Table)
    (consistent : Consistent source table) :
    ((simulateQ (tableImpl source (RawCtxProtocolBackend.backend source writer))
      (program serverCount beaconCount senderId route decode client state)).run
        (primitive, table)).IsTotalQueryBound
      (budget.1 .coin + 64 * (budget.1 .send + budget.1 .raw + budget.1 .hash)) := by
  have equal := source_complete source writer serverCount beaconCount senderId route decode client state primitive table consistent
  have bounds := congrArg (fun computation => computation.IsTotalQueryBound
    (budget.1 .coin + 64 * (budget.1 .send + budget.1 .raw + budget.1 .hash))) equal
  simp only [IsTotalQueryBound, isQueryBound_map_iff] at bounds
  exact bounds.mp (RawCtxRevealBudgets.schedule_uniform source writer serverCount beaconCount senderId
    route decode client budget bounded (state, primitive))

end BeaconcryptCore.Computational.RawCtxNativeKdfFamily

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeKdfFamily.compiler_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeKdfFamily.compiler_real

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeKdfFamily.backend_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeKdfFamily.backend_complete

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeKdfFamily.source_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeKdfFamily.source_complete

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeKdfFamily.source_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeKdfFamily.source_uniform
