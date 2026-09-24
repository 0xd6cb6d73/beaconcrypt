import BeaconcryptCore.Computational.RawCtxSharedBackendBounds

/-!
The full enriched source callbacks retain exact class-specific caps: private derivation has76 uniform calls and no hash; open/seal has one hash and no caller/private draw; public services retain their own class; reveal has neither. These bounds precede source callback aggregation and count all optional failure paths.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RawCtxSharedPendingBounds
open PqxdhJointKdfGame RawCtxSelectiveSharedRom RawCtxSharedBackendBounds AdaptiveCtxSharedHash
variable {A : Type} {S B : Nat}

def publicCost (hash : Bool) : RawCtxServerServices.PublicSpec.Domain → Nat
  | .inl _ => if hash then 0 else 1
  | .inr (.inl _) => if hash then 1 else 0
  | .inr (.inr _) => 0

def liveCost (hash : Bool) : (RawCtxPendingSelectiveFamily.Spec S B).Domain → Nat
  | .inl (.inl (.inl _)) | .inl (.inr (.inl (.inl _))) => if hash then 0 else 76
  | .inl (.inl (.inr _)) | .inl (.inr (.inl (.inr _))) => if hash then 1 else 0
  | .inl (.inr (.inr query)) => publicCost hash query
  | .inr _ => 0

/-- One actual source KDF request uses its original76-draw private lookup, with no commitment query. -/
theorem kdf (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (hash : Bool) (request : SymmetricRatchetKdfRequest) (state : Local A) :
    (((compiledBackend source writer stage ∘ₛ RawCtxServerServices.nativeLift) (.inl request)).run state).IsQueryBoundP
      (HashClass hash) (if hash then 0 else 76) := by
  have bound := RawCtxSharedBackendBounds.compiled source writer stage hash (.inr (.inl (.inl request))) state
  simpa only [compiledBackend, QueryImpl.compose, RawCtxServerServices.nativeLift, simulateQ_spec_query,
    cost, RawCtxServerServiceBounds.nativePredicate, RawCtxMixedOwner.callKind, Sum.isLeft, Bool.false_eq_true,
    reduceCtorEq, if_false, if_true, Nat.mul_one, Nat.zero_add] using bound

/-- Public caller coins, raw BLAKE requests and real HKDF projections retain their exact classes. -/
theorem public_calls (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (hash : Bool) (query : RawCtxServerServices.PublicSpec.Domain) (state : Local A) :
    (((compiledBackend source writer stage ∘ₛ RawCtxServerServices.publicLift) query).run state).IsQueryBoundP
      (HashClass hash) (publicCost hash query) := by
  rcases query with coin | (bytes | view)
  all_goals simp only [QueryImpl.compose, RawCtxServerServices.publicLift, simulateQ_spec_query]
  case inl => exact (RawCtxSharedBackendBounds.compiled source writer stage hash (.inl coin) state).mono (by cases hash <;> simp [cost, publicCost, RawCtxServerServiceBounds.nativePredicate])
  case inr.inl =>
    have bound := RawCtxSharedBackendBounds.compiled source writer stage hash (.inr (.inl (.inr (.inr (.inr (.inl bytes)))))) state
    simpa only [compiledBackend, cost, publicCost, RawCtxServerServiceBounds.nativePredicate,
      RawCtxMixedOwner.callKind, Sum.isLeft, Bool.false_eq_true, reduceCtorEq, if_false, if_true,
      Nat.mul_zero, Nat.zero_add, ite_self] using bound
  case inr.inr =>
    have bound := RawCtxSharedBackendBounds.compiled source writer stage hash (.inr (.inr view)) state
    simpa only [compiledBackend, cost, publicCost, RawCtxServerServiceBounds.nativePredicate,
    RawCtxMixedOwner.callKind, Sum.isLeft, Bool.false_eq_true, reduceCtorEq, if_false, if_true,
    Nat.mul_zero, Nat.zero_add, ite_self] using bound

/-- Every actual pending callback keeps the exact hash/uniform reservation through all source branches. -/
theorem live (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (hash : Bool) (query : (RawCtxPendingSelectiveFamily.Spec S B).Domain) (state : Local A) :
    ((RawCtxSelectiveSharedRom.pending source writer stage query).run state).IsQueryBoundP
      (HashClass hash) (liveCost hash query) := by
  rw [pending_source]
  rcases query with ((request | opening) | ((request | sealing) | publicQuery)) | read
  · simp only [RawCtxPendingFamilyNative.handler, RawCtxPendingFamilyLiveQueries.handler,
      RawCtxPendingNativeCallbacks.receive_kdf, StateT.run_map, isQueryBoundP_map_iff, liveCost]
    exact kdf source writer stage hash _ state
  · simp only [RawCtxPendingFamilyNative.handler, RawCtxPendingFamilyLiveQueries.handler,
      RawCtxPendingNativeCalls.pending, QueryImpl.apply_compose, RawCtxPendingOwnerQueries.erase,
      simulateQ_spec_query, RawCtxPendingNativeCalls.original, liveCost]
    exact receive source writer stage hash _ state
  · simp only [RawCtxPendingFamilyNative.handler, RawCtxPendingFamilyLiveQueries.handler,
      RawCtxPendingNativeCallbacks.send_kdf, StateT.run_map, isQueryBoundP_map_iff, liveCost]
    exact kdf source writer stage hash _ state
  · simp only [RawCtxPendingFamilyNative.handler, RawCtxPendingFamilyLiveQueries.handler,
      RawCtxPendingNativeCalls.pending, QueryImpl.apply_compose, RawCtxPendingOwnerQueries.erase,
      simulateQ_spec_query, RawCtxPendingNativeCalls.original, liveCost]
    exact send source writer stage hash _ state
  · simp only [RawCtxPendingFamilyNative.handler, RawCtxPendingFamilyLiveQueries.handler,
      RawCtxPendingNativeCalls.pending, QueryImpl.apply_compose, RawCtxPendingOwnerQueries.erase,
      simulateQ_spec_query, RawCtxPendingNativeCalls.original, liveCost]
    exact public_calls source writer stage hash _ state
  · trivial

end BeaconcryptCore.Computational.RawCtxSharedPendingBounds


/-- info: 'BeaconcryptCore.Computational.RawCtxSharedPendingBounds.kdf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedPendingBounds.kdf

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedPendingBounds.public_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedPendingBounds.public_calls

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedPendingBounds.live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedPendingBounds.live
