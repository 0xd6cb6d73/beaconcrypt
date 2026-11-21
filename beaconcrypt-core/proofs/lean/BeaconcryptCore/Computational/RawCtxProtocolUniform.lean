import BeaconcryptCore.Computational.RawCtxProtocolBudgets

/-!
The actual deterministic HKDF callback and the common CTX cache give the full record/public schedule at most U+64(S+R+H) uniform-oracle calls across both role families. Four statements derive the bound from actual Beacon operations, tuple-preserving source interpretation, every cross-role/public step and the complete adaptive schedule. Every attempted operation is counted, including inactive rejection and failed primitive opening; cache hits may use fewer samples.

The unit is a uniform-oracle call; a 64-byte commitment-cache miss makes 64 byte-valued calls, while the caller can request another finite range. Zero additional uniform calls for fixed HKDF, functional AEAD or writing is not zero primitive/local computation. Native KDF and public HKDF counts remain explicit in RawCtxProtocolBudgets. Initial role-generation work is outside this fixed-state interface, not declared free. No record-key independence, reveal/freshness, persistence or global protocol-security conclusion follows.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxProtocolUniform
open RawCtxRoleFamily RawCtxProtocolRoles RawCtxProtocolBudgets
open RawCtxServerServiceBounds PqxdhJointKdfGame

/-- Every actual Beacon record operation pays for its possible commitment-cache miss; deterministic HKDF work remains counted separately. -/
theorem beacon_uniform {Identity DhPair KemPair Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : RawCtxBeaconLifecycle.State Identity DhPair KemPair)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((simulateQ (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
      ((RawCtxBeaconLifecycle.beaconImpl decode query).run state)).run primitive).IsTotalQueryBound 64 := by
  have hashBound : ((RawCtxBeaconLifecycle.beaconImpl decode query).run state).IsQueryBoundP
      (fun request => RawCtxMixedOwner.callKind request = .hash) 1 := by
    cases query <;> exact RawCtxBeaconLifecycle.step_bound decode _ state .hash
  simpa only [Nat.zero_mul, Nat.zero_add, Nat.mul_one] using
    RawCtxMixedShared.shared_uniform source.crypto writer (RawCtxSourceHkdf.kdfImpl source) 0
      (RawCtxSourceHkdf.kdf_uniform source) ((RawCtxBeaconLifecycle.beaconImpl decode query).run state)
      _ 1 (RawCtxBeaconLifecycle.step_bound decode query state .kdf) hashBound primitive

/-- Tuple reassociation of the actual source role execution preserves the complete uniform-call bound. -/
theorem beacon_source_uniform {Identity DhPair KemPair Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : RawCtxBeaconLifecycle.State Identity DhPair KemPair)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((RawCtxBeaconLifecycle.sourceImpl
      (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
      decode query).run (state, primitive)).IsTotalQueryBound 64 := by
  rw [← RawCtxBeaconLifecycle.beacon_interpretation]
  simpa only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run, StateT.mk,
    IsTotalQueryBound, isQueryBound_map_iff] using beacon_uniform source writer decode query state primitive

/-- Every cross-role or public request pays its actual complete uniform-oracle cost in the shared source execution. -/
theorem source_step {Metadata PeerMetadata Identity DhPair KemPair Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec serverCount beaconCount).Domain)
    (state : RawCtxProtocolRoles.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
      RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((RawCtxProtocolRoles.sourceImpl source writer serverCount beaconCount senderId route decode query).run state).IsTotalQueryBound
      (uniformWeight 0 (RawCtxProtocolBudgets.sourceKind query)) := by
  rcases query with ⟨index, send | raw⟩ | (⟨index, send | raw⟩ | (coin | (bytes | hkdf)))
  all_goals simp only [RawCtxProtocolRoles.sourceImpl, sourceFamily, StateT.run, bind_pure_comp,
    IsTotalQueryBound, isQueryBound_map_iff, RawCtxProtocolBudgets.sourceKind, uniformWeight,
    Nat.zero_mul, Nat.zero_add]
  case inl.inl =>
    simpa only [RawCtxServerServices.sourceImpl, RawCtxServerServiceBounds.sourceKind, uniformWeight,
      Nat.zero_mul, Nat.zero_add, IsTotalQueryBound, StateT.run,
      RawCtxServerServices.SourceSpec, RawCtxServerMixed.SourceSpec, RawCtxServerSend.ApplicationSpec,
      RawCtxWholeOwner.RawSpec, OracleSpec.Range, OracleSpec.add_def, Sum.elim, OracleSpec.ofFn] using
      RawCtxServerServiceBounds.source_uniform_step source writer (RawCtxSourceHkdf.kdfImpl source) 0
        (RawCtxSourceHkdf.kdf_uniform source) senderId route decode (.inl (.inl send)) (state.1.1 index, state.2)
  case inl.inr =>
    simpa only [RawCtxServerServices.sourceImpl, RawCtxServerServiceBounds.sourceKind, uniformWeight,
      Nat.zero_mul, Nat.zero_add, IsTotalQueryBound, StateT.run,
      RawCtxServerServices.SourceSpec, RawCtxServerMixed.SourceSpec, RawCtxServerSend.ApplicationSpec,
      RawCtxWholeOwner.RawSpec, OracleSpec.Range, OracleSpec.add_def, Sum.elim, OracleSpec.ofFn] using
      RawCtxServerServiceBounds.source_uniform_step source writer (RawCtxSourceHkdf.kdfImpl source) 0
        (RawCtxSourceHkdf.kdf_uniform source) senderId route decode (.inl (.inr raw)) (state.1.1 index, state.2)
  case inr.inl.inl => exact beacon_source_uniform source writer decode (.inl send) (state.1.2 index) state.2
  case inr.inl.inr => exact beacon_source_uniform source writer decode (.inr raw) (state.1.2 index) state.2
  case inr.inr.inl =>
    simp [RawCtxProtocolBackend.backend, QueryImpl.compose, RawCtxServerServices.publicLift,
      RawCtxServerServices.backendImpl, OracleSpec.query]
    exact (isQueryBound_query_iff (spec := unifSpec) coin 1 _ _).2 (by decide)
  case inr.inr.inr.inl =>
    change IsTotalQueryBound (((RawCtxServerServices.backendImpl source writer (RawCtxSourceHkdf.kdfImpl source) ∘ₛ
      RawCtxServerServices.publicLift) (.inr (.inl bytes))).run state.2) 64
    rw [RawCtxServerServices.public_hash, bind_pure_comp]
    simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
      CtxComputationalSecurity.ctxRandomOracle_total_query_bound ((), bytes) state.2.2
  case inr.inr.inr.inr =>
    simp [RawCtxProtocolBackend.backend, QueryImpl.compose, RawCtxServerServices.publicLift,
      RawCtxServerServices.backendImpl, OracleSpec.query]

/-- The shared global source ledger counts caller coins and every private/public commitment miss across both roles. -/
theorem schedule_uniform {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolRoles.SourceSpec serverCount beaconCount) Result) (budget : Budget)
    (bounded : RawCtxProtocolBudgets.Bounded client budget)
    (state : RawCtxProtocolRoles.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
      RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((simulateQ (RawCtxProtocolRoles.sourceImpl source writer serverCount beaconCount senderId route decode)
      client).run state).IsTotalQueryBound
        (budget .coin + 64 * (budget .send + budget .raw + budget .hash)) := by
  have bound := RawCtxProtocolBudgets.weighted_bound
    (RawCtxProtocolRoles.sourceImpl source writer serverCount beaconCount senderId route decode)
    (fun _ => True) (uniformWeight 0) client budget bounded
    (fun query state => (source_step source writer serverCount beaconCount senderId route decode query state).isQueryBoundP)
    state
  simpa only [uniform_bill, Nat.zero_mul, Nat.add_zero, IsTotalQueryBound, IsQueryBoundP,
    not_true_eq_false, false_or, ite_true] using bound

end BeaconcryptCore.Computational.RawCtxProtocolUniform

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolUniform.beacon_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolUniform.beacon_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolUniform.beacon_source_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolUniform.beacon_source_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolUniform.source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolUniform.source_step

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolUniform.schedule_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolUniform.schedule_uniform
