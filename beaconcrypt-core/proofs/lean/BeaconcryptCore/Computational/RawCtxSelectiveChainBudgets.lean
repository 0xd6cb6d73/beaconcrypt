import BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix
import BeaconcryptCore.Computational.RawCtxNativeKdfFamilyBounds

/-!
The actual selective finite Server/Beacon family and its exact stopped prefix have uniform-call cap U + 76*(S+51*R) + 64*(S+R+H). The all-reply source budgets count original sends S, raw attempts R, caller coins U, public commitments H, public HKDF views K and reveals E. Private KDF calls are bounded by S+51*R; public HKDF views remain fixed real evaluations and never cause private-table sampling. Every attempted record and possible callback continuation is included, without a cache consistency, selected-miss, target honesty or freshness premise.

The proof derives the backend's three costs directly from its original syntax, derives the caller-coin cap from the complete source schedule, and consumes the existing native KDF/hash source caps. The exact prefix bound follows from literal scan-and-finish equality. It does not transfer costs across equality of distributions or assert a bound for an arbitrary hidden-input observer. Initial generation, reduction challengers and deterministic primitive, parser, lookup, copying, hash and table work remain separate explicit work. No cryptographic assumption or secrecy conclusion is added.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets
open PqxdhJointKdfGame RawCtxSelectiveChainGame RawCtxServerServiceBounds

/-- The real native backend's only additional uniform work is its possible full64 commitment-cache sample. -/
theorem native_uniform {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (query : RawCtxMixedOwner.NativeSpec.Domain)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) query).run state).IsTotalQueryBound
      (64 * (if RawCtxMixedOwner.callKind query = .hash then 1 else 0)) := by
  have kdfBound : (liftM (RawCtxMixedOwner.NativeSpec.query query) : OracleComp RawCtxMixedOwner.NativeSpec _).IsQueryBoundP
      (fun request => RawCtxMixedOwner.callKind request = .kdf) 1 := by
    exact (isQueryBoundP_query_iff _ _ _).mpr (fun _ => by decide)
  have hashBound : (liftM (RawCtxMixedOwner.NativeSpec.query query) : OracleComp RawCtxMixedOwner.NativeSpec _).IsQueryBoundP
      (fun request => RawCtxMixedOwner.callKind request = .hash)
      (if RawCtxMixedOwner.callKind query = .hash then 1 else 0) := by
    apply (isQueryBoundP_query_iff _ _ _).mpr
    intro selected
    simp [selected]
  simpa only [simulateQ_spec_query, Nat.zero_mul, Nat.zero_add] using
    RawCtxMixedShared.shared_uniform source.crypto writer (RawCtxSourceHkdf.kdfImpl source) 0
      (RawCtxSourceHkdf.kdf_uniform source) (liftM (RawCtxMixedOwner.NativeSpec.query query)) 1 _ kdfBound hashBound state

set_option backward.isDefEq.respectTransparency false in
/-- The compiled backend charges private full76 draws separately from caller coins and shared commitment hashes. -/
theorem compiled_uniform {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (query : RawCtxServerServices.BackendSpec.Domain)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary × Store) :
    (((handler source stage (RawCtxProtocolBackend.backend source writer) ∘ₛ
      RawCtxSelectiveKdfFamily.compiler) query).run state).IsTotalQueryBound
      ((if query.isLeft then 1 else 0) +
        76 * (if nativePredicate .kdf query then 1 else 0) +
        64 * (if nativePredicate .hash query then 1 else 0)) := by
  rcases query with coin | ((request | request) | view)
  all_goals simp only [QueryImpl.compose, RawCtxSelectiveKdfFamily.compiler,
    simulateQ_spec_query, simulateQ_map, handler, StateT.run,
    bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
  case inr.inl.inl =>
    simp only [nativePredicate, RawCtxMixedOwner.callKind, Sum.isLeft, Bool.false_eq_true,
      if_false, if_true, Nat.mul_one, Nat.zero_add]
    change IsTotalQueryBound ((fun result => (RawCtxKdfRequestTable.fullResponse result.1, result.2)) <$>
      ((fun result => (result.1, (state.1, result.2))) <$>
        privateStep source stage (RawCtxKdfRequestTable.address request) state.2)) 76
    simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
      private_uniform source stage (RawCtxKdfRequestTable.address request) state.2
  case inr.inl.inr =>
    have bound := native_uniform source writer (.inr request) state.1
    rcases request with sealing | (opening | (hash | publish)) <;>
      simpa [RawCtxProtocolBackend.backend, RawCtxServerServices.backendImpl, nativePredicate,
        RawCtxMixedOwner.callKind, IsTotalQueryBound] using bound
  case inl =>
    simp [RawCtxProtocolBackend.backend, RawCtxServerServices.backendImpl, nativePredicate,
      bind_pure_comp, isQueryBound_map_iff]
  case inr.inr =>
    simp [RawCtxProtocolBackend.backend, RawCtxServerServices.backendImpl, nativePredicate]


/-- Every possible backend continuation retains the three separate actual query reservations. -/
theorem backend_uniform {Auxiliary Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (client : OracleComp RawCtxServerServices.BackendSpec Result) (qCoin qKdf qHash : Nat)
    (coins : client.IsQueryBoundP (fun query => query.isLeft = true) qCoin)
    (kdfs : client.IsQueryBoundP (nativePredicate .kdf) qKdf)
    (hashes : client.IsQueryBoundP (nativePredicate .hash) qHash)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary × Store) :
    ((simulateQ (handler source stage (RawCtxProtocolBackend.backend source writer))
      (simulateQ RawCtxSelectiveKdfFamily.compiler client)).run state).IsTotalQueryBound
        (qCoin + 76 * qKdf + 64 * qHash) := by
  rw [← QueryImpl.simulateQ_compose]
  induction client using OracleComp.inductionOn generalizing qCoin qKdf qHash state with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at coins kdfs hashes
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      have tail := fun (reply : RawCtxServerServices.BackendSpec.Range query ×
          (RawCtxSharedPrimitive.SharedState Auxiliary × Store)) =>
        ih reply.1 _ _ _ (coins.2 reply.1) (kdfs.2 reply.1) (hashes.2 reply.1) reply.2
      apply (isTotalQueryBound_bind (compiled_uniform source writer stage query state) tail).mono
      split_ifs <;> simp_all only [not_true_eq_false, false_or] <;> omega

/-- Native operation lifting cannot manufacture a caller coin request. -/
theorem native_coins {Result : Type} (client : OracleComp RawCtxMixedOwner.NativeSpec Result) :
    (simulateQ RawCtxServerServices.nativeLift client).IsQueryBoundP
      (fun query => query.isLeft = true) 0 := by
  refine RawCtxSourceOpen.simulate_bound RawCtxServerServices.nativeLift (fun _ => False)
    (fun query => query.isLeft = true) client 0 (isQueryBoundP_false client 0) ?_
  intro query
  exact (isQueryBoundP_query_iff (spec := RawCtxServerServices.BackendSpec)
    (p := fun query => query.isLeft = true) _ _).mpr (by simp)

/-- Both role frontends and all public services forward only original caller coins. -/
theorem protocol_coins {Metadata PeerMetadata Identity DhPair KemPair : Type}
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec serverCount beaconCount).Domain)
    (state : RawCtxProtocolRoles.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    ((RawCtxProtocolRoles.protocolImpl serverCount beaconCount senderId route decode query).run state).IsQueryBoundP
      (fun query => query.isLeft = true)
      (if RawCtxProtocolBudgets.sourceKind query = .coin then 1 else 0) := by
  rcases query with ⟨index, send | raw⟩ | (⟨index, send | raw⟩ | (coin | (bytes | hkdf))) <;>
    simp only [RawCtxProtocolRoles.protocolImpl, RawCtxRoleFamily.familyImpl, StateT.run,
      bind_pure_comp, simulateQ_map, isQueryBoundP_map_iff, RawCtxProtocolBudgets.sourceKind]
  all_goals first | exact native_coins _ | skip
  all_goals exact (isQueryBoundP_query_iff (spec := RawCtxServerServices.BackendSpec)
    (p := fun query => query.isLeft = true) _ _).mpr (by simp)

/-- Every live read retains its original reply and adds no caller coin. -/
theorem reveal_coins {Metadata PeerMetadata Identity DhPair KemPair : Type}
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec serverCount beaconCount).Domain)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    ((RawCtxProtocolReveals.protocolImpl serverCount beaconCount senderId route decode query).run state).IsQueryBoundP
      (fun query => query.isLeft = true)
      (RawCtxRevealBudgets.weight (fun kind => if kind = .coin then 1 else 0) 0 query) := by
  cases query with
  | inl request =>
      simpa only [RawCtxProtocolReveals.protocolImpl, StateT.run, bind_pure_comp,
        isQueryBoundP_map_iff, RawCtxRevealBudgets.weight] using
        protocol_coins serverCount beaconCount senderId route decode request state.1
  | inr request => trivial

/-- The original source budget supplies the caller-coin reservation for the entire native family. -/
theorem source_coins {Metadata PeerMetadata Identity DhPair KemPair Result : Type}
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    ((simulateQ (RawCtxProtocolReveals.protocolImpl serverCount beaconCount senderId route decode)
      client).run state).IsQueryBoundP (fun query => query.isLeft = true) (budget.1 .coin) := by
  have bound := RawCtxRevealBudgets.weighted_bound
    (RawCtxProtocolReveals.protocolImpl serverCount beaconCount senderId route decode)
    (fun query => query.isLeft = true) (fun kind => if kind = .coin then 1 else 0) 0
    client budget bounded (fun query state => reveal_coins serverCount beaconCount senderId route decode query state) state
  simpa [RawCtxRevealBudgets.bill, RawCtxServerServiceBounds.bill] using bound

/-- The actual selective family charges all source work without a target, miss or honesty premise. -/
theorem family_uniform {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (store : Store) :
    (family source writer stage serverCount beaconCount senderId route decode client state primitive store).IsTotalQueryBound
      (budget.1 .coin + 76 * (budget.1 .send + 51 * budget.1 .raw) +
        64 * (budget.1 .send + budget.1 .raw + budget.1 .hash)) := by
  refine backend_uniform source writer stage _ _ _ _
    (source_coins serverCount beaconCount senderId route decode client budget bounded state) ?_ ?_ (primitive, store)
  · simpa [RawCtxMixedOwner.sendCost, RawCtxMixedOwner.receiveCost] using
      RawCtxRevealBudgets.backend_bound serverCount beaconCount senderId route decode client budget bounded state .kdf
  · simpa [RawCtxMixedOwner.sendCost, RawCtxMixedOwner.receiveCost] using
      RawCtxRevealBudgets.backend_bound serverCount beaconCount senderId route decode client budget bounded state .hash

/-- Stopping before an original private callback cannot spend more uniform calls than the complete same source execution. -/
theorem prefix_uniform {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (cutStage runStage : Nat)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (store : Store) :
    (RawCtxSelectiveChainPrefix.scan source cutStage runStage (RawCtxProtocolBackend.backend source writer)
      (RawCtxSelectiveKdfFamily.program serverCount beaconCount senderId route decode client state)
        (primitive, store)).IsTotalQueryBound
      (budget.1 .coin + 76 * (budget.1 .send + 51 * budget.1 .raw) +
        64 * (budget.1 .send + budget.1 .raw + budget.1 .hash)) := by
  apply IsTotalQueryBound.of_bind_left (ob := RawCtxPendingMixedPrefix.finish
    (handler source runStage (RawCtxProtocolBackend.backend source writer)))
  rw [RawCtxSelectiveChainPrefix.scan_finish]
  exact family_uniform source writer runStage serverCount beaconCount senderId route decode
    client budget bounded state primitive store

end BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets.native_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets.native_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets.compiled_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets.compiled_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets.backend_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets.backend_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets.native_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets.native_coins

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets.protocol_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets.protocol_coins

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets.reveal_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets.reveal_coins

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets.source_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets.source_coins

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets.family_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets.family_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets.prefix_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets.prefix_uniform
