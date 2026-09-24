import BeaconcryptCore.Computational.RawCtxSelectiveSharedRom
import BeaconcryptCore.Computational.PqxdhInitialNativeBudgets

/-!
The concrete pre-cut backend forwards every hash attempt and charges private full76 sampling separately from caller coins. Hash-cache hits are still hash queries. Public HKDF evaluation stays real and incurs no private-table draw.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSharedBackendBounds
open PqxdhJointKdfGame RawCtxSelectiveChainGame RawCtxServerServiceBounds AdaptiveCtxSharedHash
open RawCtxSelectiveSharedRom
variable {A Result : Type}

def cost (hash : Bool) (query : RawCtxServerServices.BackendSpec.Domain) : Nat :=
  if hash then if nativePredicate .hash query then 1 else 0
  else (if query.isLeft then 1 else 0) + 76 * (if nativePredicate .kdf query then 1 else 0)

set_option backward.isDefEq.respectTransparency false in
/-- Every backend callback counts its actual hash attempt or caller/private randomness, including the zero-draw cached branches. -/
theorem compiled (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (hash : Bool) (query : RawCtxServerServices.BackendSpec.Domain) (state : Local A) :
    (((RawCtxSelectiveSharedRom.handler source writer stage ∘ₛ RawCtxSelectiveKdfFamily.compiler) query).run state).IsQueryBoundP
      (HashClass hash) (cost hash query) := by
  rcases query with coin | ((request | request) | view)
  all_goals simp only [QueryImpl.compose, RawCtxSelectiveKdfFamily.compiler,
    simulateQ_spec_query, simulateQ_map, RawCtxSelectiveSharedRom.handler, StateT.run_map,
    bind_pure_comp, isQueryBoundP_map_iff]
  all_goals simp only [StateT.run, isQueryBoundP_map_iff]
  case inr.inl.inl =>
    cases hash
    · simpa [cost, nativePredicate, RawCtxMixedOwner.callKind] using
        (private_bills source stage (RawCtxKdfRequestTable.address request) state.2).2
    · simpa [cost, nativePredicate, RawCtxMixedOwner.callKind] using
        (private_bills source stage (RawCtxKdfRequestTable.address request) state.2).1
  case inl => cases hash <;> simp [RawCtxSourceSharedRom.backend, cost, nativePredicate, HashClass, isQueryBoundP_query_iff]
  case inr.inl.inr =>
    rcases request with sealing | (opening | (hashing | publish))
    all_goals cases hash <;> simp [RawCtxSourceSharedRom.backend, RawCtxSourceSharedRom.native, cost,
      nativePredicate, RawCtxMixedOwner.callKind, HashClass, isQueryBoundP_query_iff]
  case inr.inr => trivial

def bill (hash : Bool) (qCoin qKdf qHash : Nat) := if hash then qHash else qCoin + 76 * qKdf

/-- The complete adaptive backend charges every hash lookup, every original caller coin and every private full-output draw separately. -/
theorem backend (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (hash : Bool) (client : OracleComp RawCtxServerServices.BackendSpec Result) (qCoin qKdf qHash : Nat)
    (coinBound : client.IsQueryBoundP (fun query => query.isLeft = true) qCoin)
    (kdfBound : client.IsQueryBoundP (nativePredicate .kdf) qKdf)
    (hashBound : client.IsQueryBoundP (nativePredicate .hash) qHash) (state : Local A) :
    ((simulateQ (RawCtxSelectiveSharedRom.handler source writer stage ∘ₛ RawCtxSelectiveKdfFamily.compiler) client).run state).IsQueryBoundP
      (HashClass hash) (bill hash qCoin qKdf qHash) := by
  induction client using OracleComp.inductionOn generalizing qCoin qKdf qHash state with
  | pure value => trivial
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at coinBound kdfBound hashBound
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have tail := fun (reply : RawCtxServerServices.BackendSpec.Range query × Local A) =>
      ih reply.1 _ _ _ (coinBound.2 reply.1) (kdfBound.2 reply.1) (hashBound.2 reply.1) reply.2
    apply (isQueryBoundP_bind (compiled source writer stage hash query state) (fun reply _ => tail reply)).mono
    cases hash <;> simp only [cost, bill, Bool.false_eq_true, if_false, if_true]
    all_goals split_ifs <;> simp_all only [not_true_eq_false, false_or] <;> omega

noncomputable def compiledBackend (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat) :
    QueryImpl RawCtxServerServices.BackendSpec (StateT (Local A) (OracleComp HashSpec)) :=
  RawCtxSelectiveSharedRom.handler source writer stage ∘ₛ RawCtxSelectiveKdfFamily.compiler

/-- Native source operations add no caller coin; their actual KDF and hash categories supply the two exact prefix bills. -/
theorem native (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (hash : Bool) (client : OracleComp RawCtxMixedOwner.NativeSpec Result) (qKdf qHash : Nat)
    (kdfs : client.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .kdf) qKdf)
    (hashes : client.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .hash) qHash)
    (state : Local A) :
    ((simulateQ (compiledBackend source writer stage ∘ₛ RawCtxServerServices.nativeLift) client).run state).IsQueryBoundP
      (HashClass hash) (bill hash 0 qKdf qHash) := by
  simpa only [compiledBackend, QueryImpl.simulateQ_compose] using
    backend source writer stage hash (simulateQ RawCtxServerServices.nativeLift client) 0 qKdf qHash
      (RawCtxSelectiveChainBudgets.native_coins client)
      (RawCtxServerServiceBounds.nativeLift_bound .kdf client qKdf kdfs)
      (RawCtxServerServiceBounds.nativeLift_bound .hash client qHash hashes) state

/-- The literal opening hashes at most once and performs no private derivation or caller sampling, even on rejection. -/
theorem opening (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (hash : Bool) (input : RawCtxWholeOwner.OpenInput) (state : Local A) :
    ((simulateQ (compiledBackend source writer stage ∘ₛ RawCtxServerServices.nativeLift)
      (RawCtxMixedOwner.receiveAdapter (.inr input))).run state).IsQueryBoundP (HashClass hash) (if hash then 1 else 0) := by
  have kdfs : (RawCtxMixedOwner.receiveAdapter (.inr input)).IsQueryBoundP
      (fun query => RawCtxMixedOwner.callKind query = .kdf) 0 := by
    apply IsQueryBoundP.of_imp (p' := fun query => query.isLeft = true) _
      (RawCtxPendingNonKdfStore.open_zero input)
    intro query selected
    rcases query with request | (sealing | (opening | (hashing | publish))) <;>
      simp_all only [RawCtxMixedOwner.callKind, reduceCtorEq, Sum.isLeft]
  simpa only [bill, Nat.mul_zero, Nat.zero_add] using
    native source writer stage hash _ 0 1 kdfs (PqxdhInitialNativeBudgets.open_hash input) state
/-- The literal seal hashes at most once and performs no private derivation or caller sampling, including AEAD and writer failure. -/
theorem sealing (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (hash : Bool) (input : RawCtxSourceSend.SealInput) (state : Local A) :
    ((simulateQ (compiledBackend source writer stage ∘ₛ RawCtxServerServices.nativeLift)
      (RawCtxMixedOwner.sendAdapter (.inr input))).run state).IsQueryBoundP (HashClass hash) (if hash then 1 else 0) := by
  have kdfs : (RawCtxMixedOwner.sendAdapter (.inr input)).IsQueryBoundP
      (fun query => RawCtxMixedOwner.callKind query = .kdf) 0 := by
    apply IsQueryBoundP.of_imp (p' := fun query => query.isLeft = true) _
      (RawCtxPendingNonKdfStore.seal_zero input)
    intro query selected
    rcases query with request | (sealing | (opening | (hashing | publish))) <;>
      simp_all only [RawCtxMixedOwner.callKind, reduceCtorEq, Sum.isLeft]
  simpa only [bill, Nat.mul_zero, Nat.zero_add] using
    native source writer stage hash _ 0 1 kdfs (PqxdhInitialNativeBudgets.seal_hash input) state

set_option backward.isDefEq.respectTransparency false in
/-- Missing material and every actual optional opening result are retained within one hash and zero sampling calls. -/
theorem receive (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (hash : Bool)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (state : Local A) :
    ((RawCtxPendingNativeCalls.receive
      (compiledBackend source writer stage ∘ₛ RawCtxServerServices.nativeLift)
      (.inr pending)).run state).IsQueryBoundP (HashClass hash) (if hash then 1 else 0) := by
  simp only [RawCtxPendingNativeCalls.receive, QueryImpl.apply_compose, RawCtxInterpretedReceive.nativeAdapter,
    _root_.simulateQ_spec_query, QueryImpl.simulateQ_compose, RawCtxWholeOwner.adapter]
  split
  · simp only [simulateQ_pure, StateT.run_pure]
    trivial
  · simp only [bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map, isQueryBoundP_map_iff]
    simpa only [QueryImpl.simulateQ_compose] using opening source writer stage hash _ state

set_option backward.isDefEq.respectTransparency false in
/-- The actual enriched seal retains all primitive replies while paying at most one hash and no sampling. -/
theorem send (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (hash : Bool) (pending : RawCtxInterpretedSend.Seal RatchetMaterial RawCtxSourceSend.SealContext) (state : Local A) :
    ((RawCtxPendingNativeCalls.send (compiledBackend source writer stage ∘ₛ RawCtxServerServices.nativeLift)
      (.inr pending)).run state).IsQueryBoundP (HashClass hash) (if hash then 1 else 0) := by
  simp only [RawCtxPendingNativeCalls.send, QueryImpl.apply_compose, RawCtxInterpretedSend.nativeAdapter,
    _root_.simulateQ_spec_query, QueryImpl.simulateQ_compose, RawCtxSourceSend.adapter,
    bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map, isQueryBoundP_map_iff]
  simpa only [QueryImpl.simulateQ_compose] using sealing source writer stage hash _ state

/-- The enriched callback compiler is the literal pending native handler over this same compiled backend. -/
theorem pending_source {S B : Nat} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (query : (RawCtxPendingSelectiveFamily.Spec S B).Domain) :
    RawCtxSelectiveSharedRom.pending (A := A) source writer stage query =
      RawCtxPendingFamilyNative.handler (compiledBackend source writer stage) query := by
  change simulateQ (compiledBackend source writer stage) (pendingCode query) = _
  exact pending_natural _ query

end BeaconcryptCore.Computational.RawCtxSharedBackendBounds


/-- info: 'BeaconcryptCore.Computational.RawCtxSharedBackendBounds.compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedBackendBounds.compiled

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedBackendBounds.backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedBackendBounds.backend

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedBackendBounds.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedBackendBounds.native

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedBackendBounds.opening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedBackendBounds.opening

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedBackendBounds.sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedBackendBounds.sealing

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedBackendBounds.receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedBackendBounds.receive

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedBackendBounds.send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedBackendBounds.send

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedBackendBounds.pending_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedBackendBounds.pending_source
