import BeaconcryptCore.Computational.RawCtxNativeKdfFamily

/-!
The complete actual finite native Server/Beacon role and reveal program is compiled with one shared table for private record KDF requests only. Every public HKDF view goes to the unchanged fixed real backend, even if its input equals a private table address. All native replies, paired-role correlations, role state, history and shared primitive effects are retained.

The real fixed-source table equality requires its explicit functional consistency condition. Hybrid tables need separate selected-input alias and freshness arguments; public views must not silently be answered from those tables. The source uniform ledger is transported through literal computation equality, not equality of evaluated distributions. This module does not choose a target, assert input secrecy or prove a hybrid step. Local deterministic computation is retained. Snapshot, persistence and restoration interfaces are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectiveKdfFamily
open PqxdhJointKdf PqxdhJointKdfGame RawCtxKdfRequestTable

abbrev FamilySpec := RawCtxNativeKdfFamily.FamilySpec

/-- Only private record derivations use the analysis table; all public operations retain the actual backend. -/
def compiler : QueryImpl RawCtxServerServices.BackendSpec (OracleComp FamilySpec)
  | .inr (.inl (.inl request)) => fullResponse <$> FamilySpec.query (.inr (address request))
  | request => FamilySpec.query (.inl request)

/-- At the real fixed source, private-only compilation preserves every backend reply and state effect. -/
theorem compiler_real {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) :
    directImpl source (RawCtxProtocolBackend.backend (Auxiliary := Auxiliary) source writer) ∘ₛ compiler =
      RawCtxProtocolBackend.backend source writer := by
  funext query
  rcases query with coin | ((request | request) | view) <;>
    first | rfl | simp [QueryImpl.compose, compiler, directImpl, OracleSpec.query]

/-- Public HKDF projections bypass the private table at their complete original request. -/
theorem public_compiler (view : JointKdfViewSpec.Domain) :
    compiler (.inr (.inr view)) = FamilySpec.query (.inl (.inr (.inr view))) := by
  rfl

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

/-- Both native directions and all peers share one private table while every public evaluation and reveal retains its real source behavior. -/
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

end BeaconcryptCore.Computational.RawCtxSelectiveKdfFamily

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveKdfFamily.compiler_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveKdfFamily.compiler_real

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveKdfFamily.public_compiler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveKdfFamily.public_compiler

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveKdfFamily.backend_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveKdfFamily.backend_complete

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveKdfFamily.source_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveKdfFamily.source_complete

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveKdfFamily.source_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveKdfFamily.source_uniform
