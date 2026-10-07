-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler

/-! The complete growing-table local compiler uses the actual native source opening and sealing adapters, retaining their optional API replies and entire primitive state. These are operational equalities, without cryptographic or distribution assumptions. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters
open PqxdhRecordLiftChainTable PqxdhRecordLiftMaterialTable PqxdhRecordLiftChainCompiler
variable {Slot PrimitiveState : Type}

abbrev ReceiveNative (PrimitiveState : Type) :=
  QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState ProbComp)
abbrev SendNative (PrimitiveState : Type) :=
  QueryImpl RawCtxSourceSend.PrimitiveSpec (StateT PrimitiveState ProbComp)

/-- The native full76 response is carried intact before its already checked conversion. -/
noncomputable def receiveKdf (native : ReceiveNative PrimitiveState) : Kdf PrimitiveState := fun request =>
  PqxdhRecordLiftRealTable.fromResponse <$> native (.inl request)

/-- Missing material, actual optional plaintext and source metadata wrapping all remain in the original native adapter. -/
noncomputable def receiveOpen (native : ReceiveNative PrimitiveState) :
    Open RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted PrimitiveState := fun pending =>
  simulateQ native (RawCtxWholeOwner.adapter (.inr (RawCtxInterpretedOpening.toNative pending)))

noncomputable def sendKdf (native : SendNative PrimitiveState) : Kdf PrimitiveState := fun request =>
  PqxdhRecordLiftRealTable.fromResponse <$> native (.inl request)

/-- The adapter returns the actual optional writer bytes with source API metadata; no ciphertext is manufactured here. -/
noncomputable def sendSeal (native : SendNative PrimitiveState) :
    Seal RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted PrimitiveState := fun pending =>
  simulateQ native (RawCtxSourceSend.adapter (.inr (RawCtxInterpretedSend.nativeSeal pending)))

/-- Literal native source callbacks equal the local compiler's receive callbacks on every query. -/
theorem receive_callbacks (native : ReceiveNative PrimitiveState) :
    receiveImpl (receiveKdf native) (receiveOpen native) =
      (native ∘ₛ RawCtxWholeOwner.adapter) ∘ₛ RawCtxInterpretedReceive.nativeAdapter := by
  funext request
  cases request with
  | inl request =>
      change (fun value => RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse value)) <$>
        (PqxdhRecordLiftRealTable.fromResponse <$> native (.inl request)) =
        simulateQ (native ∘ₛ RawCtxWholeOwner.adapter) (RawCtxInterpretedReceive.decodeResponse <$>
          (RawCtxOwnerOracle.ReceiveSpec RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted).query (.inl request))
      rw [simulateQ_map, simulateQ_spec_query]
      change _ = RawCtxInterpretedReceive.decodeResponse <$> simulateQ native (RawCtxWholeOwner.adapter (.inl request))
      simp only [RawCtxWholeOwner.adapter, liftM, simulateQ_spec_query, Functor.map_map,
        PqxdhRecordLiftRealTable.fullResponse_from]
  | inr pending =>
      change receiveOpen native pending = simulateQ (native ∘ₛ RawCtxWholeOwner.adapter)
        ((RawCtxOwnerOracle.ReceiveSpec RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted).query
          (.inr (RawCtxInterpretedOpening.toNative pending)))
      rw [simulateQ_spec_query]
      rfl

/-- Result conversion only wraps the refined source kernel, retaining the actual API reply and complete primitive state. -/
def concreteResult {Reply : Type}
    (result : (RefinedRatchet RatchetChain RatchetChain RatchetMaterial × Reply) × PrimitiveState) :
    (ConcreteRatchetKernel × Reply) × PrimitiveState := ((⟨result.1.1⟩, result.1.2), result.2)

/-- The whole evaluated native receive uses the original source adapter and actual optional API reply. -/
theorem receive_native_state (native : ReceiveNative PrimitiveState)
    (entry : RefinedRatchet RatchetChain RatchetChain RatchetMaterial) (target : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) (state : PrimitiveState) :
    concreteResult <$> (simulateQ (receiveImpl (receiveKdf native) (receiveOpen native))
      (RawCtxInterpretedReceive.receive entry target context)).run state =
      (simulateQ native (simulateQ RawCtxWholeOwner.adapter
        (RawCtxOwnerOracle.receive ⟨entry⟩ target context))).run state := by
  rw [receive_callbacks, RawCtxInterpretedReceive.receive_native, simulateQ_map, simulateQ_map,
    ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose, StateT.run_map]
  rfl

/-- Complete local receive erasure reaches the literal source receive and opening adapter with all primitive effects retained. -/
theorem receive_adapter (seeds : Seeds Slot) (valid : Table Slot → Prop)
    (lookup : Lookup Slot PrimitiveState) (native : ReceiveNative PrimitiveState)
    (preserves : LookupPreserves valid lookup)
    (realized : LookupRealized seeds valid lookup (receiveKdf native))
    (entry : LabeledKernel Slot) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : Execution Slot PrimitiveState) (good : valid state.1) (refs : KernelReferences state.1 entry) :
    (concreteResult ∘ eraseResult seeds) <$>
      ((receive seeds lookup (receiveOpen native) (RawCtxChainReceive.normalBegin entry target context)).run state) =
      (simulateQ native (simulateQ RawCtxWholeOwner.adapter
        (RawCtxOwnerOracle.receive ⟨eraseKernel seeds state.1 entry⟩ target context))).run state.2 := by
  have lifted := congrArg (fun computation => concreteResult <$> computation)
    (admitted_receive_erasure seeds valid lookup (receiveKdf native) (receiveOpen native)
      preserves realized entry target context state good refs.1 refs.2)
  simpa only [Functor.map_map, Function.comp_def] using
    lifted.trans (receive_native_state native (eraseKernel seeds state.1 entry) target context state.2)

/-- Literal real full76 lookup discharges the local table equations before the original source adapter join. -/
theorem real_receive_adapter [DecidableEq Slot] (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : Seeds Slot) (native : ReceiveNative PrimitiveState) (correct : KdfReal source (receiveKdf native))
    (entry : LabeledKernel Slot) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : Execution Slot PrimitiveState) (good : RealValid source seeds state.1)
    (refs : KernelReferences state.1 entry) :
    (concreteResult ∘ eraseResult seeds) <$>
      ((receive seeds (realLookup seeds (receiveKdf native)) (receiveOpen native)
        (RawCtxChainReceive.normalBegin entry target context)).run state) =
      (simulateQ native (simulateQ RawCtxWholeOwner.adapter
        (RawCtxOwnerOracle.receive ⟨eraseKernel seeds state.1 entry⟩ target context))).run state.2 :=
  receive_adapter seeds (RealValid source seeds) _ native
    (realLookup_preserves source seeds _ correct) (realLookup_realized seeds _ _) entry target context state good refs

/-- Literal native source callbacks equal the local compiler's send callbacks on every query. -/
theorem send_callbacks (native : SendNative PrimitiveState) :
    sendImpl (sendKdf native) (sendSeal native) =
      (native ∘ₛ RawCtxSourceSend.adapter) ∘ₛ RawCtxInterpretedSend.nativeAdapter := by
  funext request
  cases request with
  | inl request =>
      change (fun value => RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse value)) <$>
        (PqxdhRecordLiftRealTable.fromResponse <$> native (.inl request)) =
        simulateQ (native ∘ₛ RawCtxSourceSend.adapter) (RawCtxInterpretedReceive.decodeResponse <$>
          (RawCtxSourceSend.SendSpec RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted).query (.inl request))
      rw [simulateQ_map, simulateQ_spec_query]
      change _ = RawCtxInterpretedReceive.decodeResponse <$> simulateQ native (RawCtxSourceSend.adapter (.inl request))
      simp only [RawCtxSourceSend.adapter, liftM, simulateQ_spec_query, Functor.map_map,
        PqxdhRecordLiftRealTable.fullResponse_from]
  | inr pending =>
      change sendSeal native pending = simulateQ (native ∘ₛ RawCtxSourceSend.adapter)
        ((RawCtxSourceSend.SendSpec RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted).query
          (.inr (RawCtxInterpretedSend.nativeSeal pending)))
      rw [simulateQ_spec_query]
      rfl

/-- The complete evaluated send uses the original native adapter, including its actual writer option and API metadata. -/
theorem send_native_state (native : SendNative PrimitiveState)
    (entry : RefinedRatchet RatchetChain RatchetChain RatchetMaterial)
    (context : RawCtxSourceSend.SealContext) (state : PrimitiveState) :
    concreteResult <$> (simulateQ (sendImpl (sendKdf native) (sendSeal native))
      (RawCtxInterpretedSend.send entry context)).run state =
      (simulateQ native (simulateQ RawCtxSourceSend.adapter
        (RawCtxSourceSend.send ⟨entry⟩ context))).run state := by
  rw [send_callbacks, RawCtxInterpretedSend.send_native, simulateQ_map, simulateQ_map,
    ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose, StateT.run_map]
  rfl

/-- Complete local send erasure reaches the literal source adapter and retains primitive effects even when sealing fails. -/
theorem send_adapter (seeds : Seeds Slot) (valid : Table Slot → Prop)
    (lookup : Lookup Slot PrimitiveState) (native : SendNative PrimitiveState)
    (preserves : LookupPreserves valid lookup)
    (realized : LookupRealized seeds valid lookup (sendKdf native))
    (entry : LabeledKernel Slot) (context : RawCtxSourceSend.SealContext)
    (state : Execution Slot PrimitiveState) (good : valid state.1) (refs : KernelReferences state.1 entry) :
    (concreteResult ∘ eraseSendResult seeds) <$>
      ((send seeds lookup (sendSeal native) (RawCtxChainSend.normalBegin entry context)).run state) =
      (simulateQ native (simulateQ RawCtxSourceSend.adapter
        (RawCtxSourceSend.send ⟨eraseKernel seeds state.1 entry⟩ context))).run state.2 := by
  have lifted := congrArg (fun computation => concreteResult <$> computation)
    (admitted_send_erasure seeds valid lookup (sendKdf native) (sendSeal native)
      preserves realized entry context state good refs)
  simpa only [Functor.map_map, Function.comp_def] using
    lifted.trans (send_native_state native (eraseKernel seeds state.1 entry) context state.2)

/-- Literal real lookup supplies the table equations and joins the complete original native send without a chosen successful seal. -/
theorem real_send_adapter [DecidableEq Slot] (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : Seeds Slot) (native : SendNative PrimitiveState) (correct : KdfReal source (sendKdf native))
    (entry : LabeledKernel Slot) (context : RawCtxSourceSend.SealContext)
    (state : Execution Slot PrimitiveState) (good : RealValid source seeds state.1)
    (refs : KernelReferences state.1 entry) :
    (concreteResult ∘ eraseSendResult seeds) <$>
      ((send seeds (realLookup seeds (sendKdf native)) (sendSeal native)
        (RawCtxChainSend.normalBegin entry context)).run state) =
      (simulateQ native (simulateQ RawCtxSourceSend.adapter
        (RawCtxSourceSend.send ⟨eraseKernel seeds state.1 entry⟩ context))).run state.2 :=
  send_adapter seeds (RealValid source seeds) _ native
    (realLookup_preserves source seeds _ correct) (realLookup_realized seeds _ _) entry context state good refs

/-- Full-response conversion is reversible around the actual receive KDF call, preserving its complete state effects. -/
theorem receive_kdf_response (native : ReceiveNative PrimitiveState) (request : SymmetricRatchetKdfRequest) :
    RawCtxKdfRequestTable.fullResponse <$> receiveKdf native request = native (.inl request) := by
  simp only [receiveKdf, Functor.map_map, PqxdhRecordLiftRealTable.fullResponse_from, id_map']

/-- The same actual full76 reply and primitive state are retained on the send path. -/
theorem send_kdf_response (native : SendNative PrimitiveState) (request : SymmetricRatchetKdfRequest) :
    RawCtxKdfRequestTable.fullResponse <$> sendKdf native request = native (.inl request) := by
  simp only [sendKdf, Functor.map_map, PqxdhRecordLiftRealTable.fullResponse_from, id_map']

/-- Missing selected material returns source rejection with unchanged primitive state and no opening invocation. -/
theorem receive_open_missing (native : ReceiveNative PrimitiveState)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (missing : (RawCtxInterpretedOpening.toNative pending).material = ok .None) :
    receiveOpen native pending = pure .None := by
  simp only [receiveOpen, RawCtxWholeOwner.adapter_missing _ missing, simulateQ_pure]

/-- A present source getter forwards one exact opening input and wraps the challenger's actual optional plaintext. -/
theorem receive_open_present (native : ReceiveNative PrimitiveState)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (input : RawCtxWholeOwner.OpenInput)
    (present : RawCtxWholeOwner.arguments (RawCtxInterpretedOpening.toNative pending) = some input) :
    receiveOpen native pending = (do
      let reply ← native (.inr input)
      pure (RawCtxOwnerResult.mapReply (RawCtxWholeOwner.decrypted input) reply)) := by
  simp only [receiveOpen, RawCtxWholeOwner.adapter_present _ input present,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure]

/-- The actual selected sealing input produces the API option from exactly the returned writer bytes. -/
theorem send_seal_reply (native : SendNative PrimitiveState)
    (pending : RawCtxInterpretedSend.Seal RatchetMaterial RawCtxSourceSend.SealContext) :
    sendSeal native pending = (do
      let reply ← native (.inr (RawCtxSourceSend.arguments (RawCtxInterpretedSend.nativeSeal pending)))
      pure (reply.map (RawCtxSourceSend.encrypted
        (RawCtxSourceSend.arguments (RawCtxInterpretedSend.nativeSeal pending))))) := by
  simp only [sendSeal, RawCtxSourceSend.adapter, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]

end BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.receive_callbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.receive_callbacks

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.receive_native_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.receive_native_state

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.receive_adapter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.receive_adapter

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.real_receive_adapter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.real_receive_adapter

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.send_callbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.send_callbacks

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.send_native_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.send_native_state

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.send_adapter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.send_adapter

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.real_send_adapter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.real_send_adapter

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.receive_kdf_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.receive_kdf_response

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.send_kdf_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.send_kdf_response

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.receive_open_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.receive_open_missing

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.receive_open_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.receive_open_present

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.send_seal_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters.send_seal_reply
