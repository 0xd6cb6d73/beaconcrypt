import BeaconcryptCore.Computational.RawCtxNativeKdfFamily

/-!
Every original private KDF request and public HKDF view makes one complete-stream request. Actual source send/raw bounds give S + 51*R + K for both finite role families under arbitrary adaptive compromise reads, including failed attempts, retries and repeated views. The complete all-reply source budget supplies this bound without a direction/owner/reveal factor.

These are syntactic source/query counts. They do not imply input freshness, independent outputs, zero deterministic HMAC/byte/table work or native runtime bounds. Original reveals retain their actual source replies and have zero extra cryptographic requests only.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxNativeKdfFamilyBounds
open RawCtxNativeKdfFamily

def needsStream : RawCtxServerServices.BackendSpec.Domain → Bool
  | .inr (.inl (.inl _)) => true
  | .inr (.inr _) => true
  | _ => false

/-- Every original private derivation/public view makes exactly one complete-stream request. -/
theorem compiler_step (query : RawCtxServerServices.BackendSpec.Domain) :
    (compiler query).IsQueryBoundP (fun query => query.isRight = true)
      (if needsStream query then 1 else 0) := by
  rcases query with coin | ((request | request) | view) <;>
    simp [compiler, needsStream, isQueryBoundP_map_iff]
  all_goals exact (isQueryBoundP_query_iff (spec := FamilySpec) (p := fun query => query.isRight = true) _ _).2 (by simp)

/-- Every possible adaptive continuation retains its complete-stream call cap. -/
theorem compiler_bound {Result : Type}
    (client : OracleComp RawCtxServerServices.BackendSpec Result) (budget : Nat)
    (bounded : client.IsQueryBoundP (fun query => needsStream query = true) budget) :
    (simulateQ compiler client).IsQueryBoundP (fun query => query.isRight = true) budget := by
  exact RawCtxSourceOpen.simulate_bound compiler _ _ client budget bounded compiler_step

/-- Native source lifting adds no public-view request and preserves the actual KDF predicate. -/
theorem nativeLift_bound {Result : Type} (client : OracleComp RawCtxMixedOwner.NativeSpec Result)
    (budget : Nat)
    (bounded : client.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .kdf) budget) :
    (simulateQ RawCtxServerServices.nativeLift client).IsQueryBoundP (fun query => needsStream query = true) budget := by
  refine RawCtxSourceOpen.simulate_bound RawCtxServerServices.nativeLift _ _ client budget bounded ?_
  refine fun query => (isQueryBoundP_query_iff (spec := RawCtxServerServices.BackendSpec)
    (p := fun query => needsStream query = true) _ _).2 ?_
  rcases query with request | (sealing | (opening | (hash | writer))) <;> simp [needsStream, RawCtxMixedOwner.callKind]

def streamWeight : RawCtxServerServiceBounds.Kind → Nat
  | .send | .hkdf => 1
  | .raw => 51
  | .coin | .hash => 0

open RawCtxProtocolRoles

/-- Per-role source work counts private KDF attempts together with original public views. -/
theorem protocol_step {Metadata PeerMetadata Identity DhPair KemPair : Type}
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (SourceSpec serverCount beaconCount).Domain)
    (state : State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    ((protocolImpl serverCount beaconCount senderId route decode query).run state).IsQueryBoundP
      (fun query => needsStream query = true)
      (streamWeight (RawCtxProtocolBudgets.sourceKind query)) := by
  rcases query with ⟨index, send | raw⟩ | (⟨index, send | raw⟩ | (coin | (bytes | hkdf))) <;>
    simp only [protocolImpl, RawCtxRoleFamily.familyImpl, StateT.run, bind_pure_comp, simulateQ_map,
      isQueryBoundP_map_iff, RawCtxProtocolBudgets.sourceKind, streamWeight]
  case inl.inl => exact nativeLift_bound _ _ (RawCtxServerMixed.send_bound senderId send.1 send.2 (state.1 index) .kdf)
  case inl.inr => exact nativeLift_bound _ _ (RawCtxServerMixed.raw_bound route decode raw (state.1 index) .kdf)
  case inr.inl.inl => exact nativeLift_bound _ _ (RawCtxBeaconLifecycle.step_bound decode (.inl send) (state.2 index) .kdf)
  case inr.inl.inr => exact nativeLift_bound _ _ (RawCtxBeaconLifecycle.step_bound decode (.inr raw) (state.2 index) .kdf)
  all_goals exact (isQueryBoundP_query_iff (spec := RawCtxServerServices.BackendSpec)
    (p := fun query => needsStream query = true) _ _).2 (by simp [needsStream])

/-- Original reveal attempts retain their replies and add no stream request. -/
theorem reveal_step {Metadata PeerMetadata Identity DhPair KemPair : Type}
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec serverCount beaconCount).Domain)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    ((RawCtxProtocolReveals.protocolImpl serverCount beaconCount senderId route decode query).run state).IsQueryBoundP
      (fun query => needsStream query = true) (RawCtxRevealBudgets.weight streamWeight 0 query) := by
  cases query with
  | inl request =>
      simpa only [RawCtxProtocolReveals.protocolImpl, StateT.run, bind_pure_comp,
        isQueryBoundP_map_iff, RawCtxRevealBudgets.weight] using
        protocol_step serverCount beaconCount senderId route decode request state.1
  | inr request => trivial

/-- The complete original source cap has no owner, direction or reveal multiplier. -/
theorem source_bound {Metadata PeerMetadata Identity DhPair KemPair Result : Type}
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    (program serverCount beaconCount senderId route decode client state).IsQueryBoundP
      (fun query => query.isRight = true) (budget.1 .send + 51 * budget.1 .raw + budget.1 .hkdf) := by
  have bound := RawCtxRevealBudgets.weighted_bound
    (RawCtxProtocolReveals.protocolImpl serverCount beaconCount senderId route decode)
    (fun query => needsStream query = true) streamWeight 0 client budget bounded
    (fun query state => reveal_step serverCount beaconCount senderId route decode query state) state
  have enumeration : (Finset.univ : Finset RawCtxServerServiceBounds.Kind) = {.send, .raw, .coin, .hash, .hkdf} := by decide
  simpa [program, RawCtxRevealBudgets.bill, RawCtxServerServiceBounds.bill,
    enumeration, streamWeight, Nat.add_assoc] using compiler_bound _ _ bound

end BeaconcryptCore.Computational.RawCtxNativeKdfFamilyBounds

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeKdfFamilyBounds.compiler_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeKdfFamilyBounds.compiler_step

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeKdfFamilyBounds.compiler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeKdfFamilyBounds.compiler_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeKdfFamilyBounds.nativeLift_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeKdfFamilyBounds.nativeLift_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeKdfFamilyBounds.protocol_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeKdfFamilyBounds.protocol_step

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeKdfFamilyBounds.reveal_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeKdfFamilyBounds.reveal_step

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeKdfFamilyBounds.source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeKdfFamilyBounds.source_bound
