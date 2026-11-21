import BeaconcryptCore.Computational.RawCtxReceiveSendFields

/-!
Actual selective private callbacks preserve the sender's cached directional path and all earlier full cache bindings. The receive case uses the original source sender-field theorem, and the send case uses its actual recorded private response. These are complete support facts for mutable original callback state; no source distribution or query cost is transferred from a fixed interpreter.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSourcePathCalls
open RawCtxSourceSendPath RawCtxCursorLineage PqxdhJointKdfGame PqxdhSecretInputKdf
variable {A Result : Type}

/-- Every complete native program preserves all earlier private cache bindings; non-KDF effects retain their actual full state. -/
theorem native_extends (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (client : OracleComp RawCtxMixedOwner.NativeSpec Result)
    (state : RawCtxPendingSelectiveFamily.State A) (result : Result × RawCtxPendingSelectiveFamily.State A)
    (supported : result ∈ support ((simulateQ (native source writer stage) client).run state)) :
    Extends state.2.1 result.2.2.1 := by
  simp only [native, RawCtxPendingSelectiveFamily.backend, QueryImpl.simulateQ_compose] at supported
  exact (RawCtxSelectiveReplay.complete source stage (RawCtxProtocolBackend.backend source writer)
    _ state result supported).1

noncomputable def receiveImpl (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat) :=
  (native (A := A) source writer stage ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter

/-- Every actual receive retains the sender's already executed directional cache path while preserving all prior private bindings. -/
theorem receive_path (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (root : RootOutput) (entry : ConcreteRatchetKernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : RawCtxPendingSelectiveFamily.State A) (valid : Path root entry state.2.1)
    (result : (ConcreteRatchetKernel × core.option.Option RawCtxWholeOwner.Decrypted) × RawCtxPendingSelectiveFamily.State A)
    (supported : result ∈ support ((simulateQ (receiveImpl source writer stage)
      (RawCtxOwnerOracle.receive entry target context)).run state)) :
    Extends state.2.1 result.2.2.1 ∧ Path root result.1.1 result.2.2.1 := by
  have extension := native_extends source writer stage
    (simulateQ RawCtxMixedOwner.receiveAdapter (simulateQ RawCtxWholeOwner.adapter
      (RawCtxOwnerOracle.receive entry target context))) state result
    (by simpa only [receiveImpl, QueryImpl.simulateQ_compose] using supported)
  have fields := RawCtxReceiveSendFields.receive_fields (receiveImpl source writer stage)
    state entry target context result supported
  refine ⟨extension, ?_⟩
  have retained := path_extends root entry state.2.1 result.2.2.1 valid extension
  simpa only [RawCtxSourceSendPath.Path, fields.1, fields.2] using retained

/-- The actual refined-kernel receive callback extends every prior binding and preserves each established directional path. -/
theorem receive_call (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (entry : RawCtxPendingOwnerQueries.Kernel RatchetChain) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : RawCtxPendingSelectiveFamily.State A)
    (result : (RawCtxPendingOwnerQueries.Kernel RatchetChain × core.option.Option RawCtxWholeOwner.Decrypted) × RawCtxPendingSelectiveFamily.State A)
    (supported : result ∈ support (((RawCtxGenericNativeCalls.calls (native source writer stage)).receive entry target context).run state)) :
    Extends state.2.1 result.2.2.1 ∧ ∀ root, Path root ⟨entry⟩ state.2.1 → Path root ⟨result.1.1⟩ result.2.2.1 := by
  have original : ((ConcreteRatchetKernel.mk result.1.1, result.1.2), result.2) ∈ support
      ((simulateQ (receiveImpl source writer stage) (RawCtxOwnerOracle.receive ⟨entry⟩ target context)).run state) := by
    rw [receiveImpl, RawCtxGenericNativeCalls.receive_realized, StateT.run_map, support_map]
    exact ⟨result, supported, rfl⟩
  have extension := native_extends source writer stage
    (simulateQ RawCtxMixedOwner.receiveAdapter (simulateQ RawCtxWholeOwner.adapter
      (RawCtxOwnerOracle.receive ⟨entry⟩ target context))) state
    ((ConcreteRatchetKernel.mk result.1.1, result.1.2), result.2)
    (by simpa only [receiveImpl, QueryImpl.simulateQ_compose] using original)
  exact ⟨extension, fun root valid => (receive_path source writer stage root ⟨entry⟩ target context state valid _ original).2⟩

/-- The actual refined-kernel send callback extends every prior binding and advances each established path, even when its seal returns no ciphertext. -/
theorem send_call (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (entry : RawCtxPendingOwnerQueries.Kernel RatchetChain) (context : RawCtxSourceSend.SealContext)
    (state : RawCtxPendingSelectiveFamily.State A)
    (result : (RawCtxPendingOwnerQueries.Kernel RatchetChain × Option RawCtxSourceSend.Encrypted) × RawCtxPendingSelectiveFamily.State A)
    (supported : result ∈ support (((RawCtxGenericNativeCalls.calls (native source writer stage)).send entry context).run state)) :
    Extends state.2.1 result.2.2.1 ∧ ∀ root, Path root ⟨entry⟩ state.2.1 → Path root ⟨result.1.1⟩ result.2.2.1 := by
  have original : ((ConcreteRatchetKernel.mk result.1.1, result.1.2), result.2) ∈ support
      ((simulateQ (sendImpl source writer stage) (RawCtxSourceSend.send ⟨entry⟩ context)).run state) := by
    rw [sendImpl, RawCtxGenericNativeCalls.send_realized, StateT.run_map, support_map]
    exact ⟨result, supported, rfl⟩
  have extension := native_extends source writer stage
    (simulateQ RawCtxMixedOwner.sendAdapter (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send ⟨entry⟩ context)))
    state ((ConcreteRatchetKernel.mk result.1.1, result.1.2), result.2)
    (by simpa only [sendImpl, QueryImpl.simulateQ_compose] using original)
  exact ⟨extension, fun root valid => (send_path source writer stage root ⟨entry⟩ context state valid _ original).2⟩

/-- Successful source replies identify the actual installed sender sequence in the same refined callback result. -/
theorem published_call (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (entry : RawCtxPendingOwnerQueries.Kernel RatchetChain) (context : RawCtxSourceSend.SealContext)
    (state : RawCtxPendingSelectiveFamily.State A)
    (result : (RawCtxPendingOwnerQueries.Kernel RatchetChain × Option RawCtxSourceSend.Encrypted) × RawCtxPendingSelectiveFamily.State A)
    (supported : result ∈ support (((RawCtxGenericNativeCalls.calls (native source writer stage)).send entry context).run state))
    (reply : RawCtxSourceSend.Encrypted) (returned : result.1.2 = some reply) :
    reply.sequence = result.1.1.control.send_sequence := by
  apply published_sequence source writer stage ⟨entry⟩ context state
    ((ConcreteRatchetKernel.mk result.1.1, result.1.2), result.2) _ reply returned
  rw [sendImpl, RawCtxGenericNativeCalls.send_realized, StateT.run_map, support_map]
  exact ⟨result, supported, rfl⟩

/-- Original public callbacks preserve all earlier private cache bindings while retaining their actual source effects. -/
theorem public_extends (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (query : RawCtxServerServices.PublicSpec.Domain)
    (state : RawCtxPendingSelectiveFamily.State A)
    (result : RawCtxServerServices.PublicSpec.Range query × RawCtxPendingSelectiveFamily.State A)
    (supported : result ∈ support (((RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ
      RawCtxServerServices.publicLift) query).run state)) : Extends state.2.1 result.2.2.1 := by
  simp only [RawCtxPendingSelectiveFamily.backend, QueryImpl.compose, QueryImpl.simulateQ_compose] at supported
  exact (RawCtxSelectiveReplay.complete source stage (RawCtxProtocolBackend.backend source writer)
    _ state result supported).1

end BeaconcryptCore.Computational.RawCtxSourcePathCalls

/-- info: 'BeaconcryptCore.Computational.RawCtxSourcePathCalls.native_extends' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePathCalls.native_extends

/-- info: 'BeaconcryptCore.Computational.RawCtxSourcePathCalls.receive_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePathCalls.receive_path

/-- info: 'BeaconcryptCore.Computational.RawCtxSourcePathCalls.receive_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePathCalls.receive_call

/-- info: 'BeaconcryptCore.Computational.RawCtxSourcePathCalls.send_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePathCalls.send_call

/-- info: 'BeaconcryptCore.Computational.RawCtxSourcePathCalls.published_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePathCalls.published_call

/-- info: 'BeaconcryptCore.Computational.RawCtxSourcePathCalls.public_extends' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePathCalls.public_extends
