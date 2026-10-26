import BeaconcryptCore.Computational.RawCtxSourceSendOrder
import BeaconcryptCore.Computational.RawCtxGenericFamilyNative

/-!
The actual native LIVE record schedule preserves sending-counter order under its complete backend, including retained private KDF replies. This is an operational statement for a schedule without owner installation; public routes do not identify installation occurrences across later registrations.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxNativeCounterOrder
open RawCtxPendingOwnerQueries
variable {State M P I D K Result : Type} {S B : Nat}

/-- Every original native receive preserves the sending counter through the actual optional reply and complete shared state. -/
theorem receive_counter (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT State ProbComp))
    (entry : Kernel RatchetChain) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : State) (result : (Kernel RatchetChain × core.option.Option RawCtxWholeOwner.Decrypted) × State)
    (supported : result ∈ support (((RawCtxGenericNativeCalls.calls native).receive entry target context).run state)) :
    result.1.1.control.send_sequence = entry.control.send_sequence := by
  have original : ((ConcreteRatchetKernel.mk result.1.1, result.1.2), result.2) ∈ support
      ((simulateQ ((native ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
        (RawCtxOwnerOracle.receive ⟨entry⟩ target context)).run state) := by
    rw [RawCtxGenericNativeCalls.receive_realized, StateT.run_map, support_map]
    exact ⟨result, supported, rfl⟩
  exact (RawCtxReceiveSendFields.receive_fields _ state ⟨entry⟩ target context _ original).2

/-- An original native send preserves or advances the counter, including an exhausted counter and a missing ciphertext. -/
theorem send_counter (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT State ProbComp))
    (entry : Kernel RatchetChain) (context : RawCtxSourceSend.SealContext)
    (state : State) (result : (Kernel RatchetChain × Option RawCtxSourceSend.Encrypted) × State)
    (supported : result ∈ support (((RawCtxGenericNativeCalls.calls native).send entry context).run state)) :
    entry.control.send_sequence.val ≤ result.1.1.control.send_sequence.val := by
  have original : ((ConcreteRatchetKernel.mk result.1.1, result.1.2), result.2) ∈ support
      ((simulateQ ((native ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
        (RawCtxSourceSend.send ⟨entry⟩ context)).run state) := by
    rw [RawCtxGenericNativeCalls.send_realized, StateT.run_map, support_map]
    exact ⟨result, supported, rfl⟩
  exact RawCtxSourceSendOrder.send_counter _ ⟨entry⟩ context state _ original

private theorem rules (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT State ProbComp)) (floor : Nat) :
    RawCtxFamilyStateInvariant.Rules (RawCtxGenericNativeCalls.calls native)
      (fun _ _ => True) (fun kernel _ => floor ≤ kernel.control.send_sequence.val) where
  refl := fun _ => trivial
  trans := fun _ _ _ _ _ => trivial
  mono := fun _ _ _ _ valid => valid
  receive := fun entry target context state result supported =>
    ⟨trivial, fun valid => by simpa only [receive_counter native entry target context state result supported] using valid⟩
  send := fun entry context state result supported =>
    ⟨trivial, fun valid => valid.trans (send_counter native entry context state result supported)⟩

/-- The complete original indexed record/read schedule preserves a selected sending-counter lower bound, with callback facts derived from the native source programs. -/
theorem schedule_lower (backend : QueryImpl RawCtxServerServices.BackendSpec (StateT State ProbComp))
    (floor : Nat) (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (entry : RawCtxGenericFamilyLive.State (Kernel RatchetChain) M P I D K S B) (state : State)
    (result : (Result × RawCtxGenericFamilyLive.State (Kernel RatchetChain) M P I D K S B) × State)
    (supported : result ∈ support (((simulateQ (RawCtxGenericFamilyLive.impl
      (RawCtxGenericNativeCalls.calls (backend ∘ₛ RawCtxServerServices.nativeLift))
      (backend ∘ₛ RawCtxServerServices.publicLift) (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk)
      sender route decode) client).run entry).run state))
    (initial : ∀ kernel, RawCtxGenericRoleFamily.selectedKernel selected entry.1 = some kernel →
      floor ≤ kernel.control.send_sequence.val) :
    ∀ kernel, RawCtxGenericRoleFamily.selectedKernel selected result.1.2.1 = some kernel →
      floor ≤ kernel.control.send_sequence.val := by
  exact (RawCtxFamilyStateInvariant.schedule _ _ _
    (rules (backend ∘ₛ RawCtxServerServices.nativeLift) floor)
    _ (fun _ _ _ _ => trivial) _ (fun _ _ _ _ => trivial)
    sender route decode client entry state result supported selected).2 initial

/-- The literal original native LIVE run preserves the counter lower bound in its complete source state, without a caller-supplied callback simulation law. -/
theorem source_lower (backend : QueryImpl RawCtxServerServices.BackendSpec (StateT State ProbComp))
    (floor : Nat) (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (entry : RawCtxProtocolReveals.State M P I D K S B) (state : State)
    (result : (Result × RawCtxProtocolReveals.State M P I D K S B) × State)
    (supported : result ∈ support ((simulateQ backend
      ((simulateQ (RawCtxProtocolReveals.protocolImpl S B sender route decode) client).run entry)).run state))
    (initial : ∀ kernel, RawCtxProtocolReveals.selectedKernel selected entry.1 = some kernel →
      floor ≤ kernel.refined.control.send_sequence.val) :
    ∀ kernel, RawCtxProtocolReveals.selectedKernel selected result.1.2.1 = some kernel →
      floor ≤ kernel.refined.control.send_sequence.val := by
  rw [RawCtxGenericFamilyNative.actual, StateT.run_map, support_map] at supported
  obtain ⟨original, reached, rfl⟩ := supported
  have before : ∀ kernel, RawCtxGenericRoleFamily.selectedKernel selected
      (RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined entry.1) = some kernel →
      floor ≤ kernel.control.send_sequence.val := by
    intro kernel found
    have actual : RawCtxProtocolReveals.selectedKernel selected entry.1 = some (ConcreteRatchetKernel.mk kernel) := by
      rw [← RawCtxGenericRoleFamily.roundtrip ConcreteRatchetKernel.refined ConcreteRatchetKernel.mk (fun _ => rfl) entry.1,
        RawCtxGenericRoleFamily.native_selected, found]
      rfl
    exact initial ⟨kernel⟩ actual
  have preserved := schedule_lower backend floor selected sender route decode client
    (RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined entry.1, entry.2) state original reached before
  intro kernel found
  change RawCtxProtocolReveals.selectedKernel selected
    (RawCtxGenericRoleFamily.nativeRoles ConcreteRatchetKernel.mk original.1.2.1) = some kernel at found
  rw [RawCtxGenericRoleFamily.native_selected] at found
  obtain ⟨old, present, rfl⟩ := Option.map_eq_some_iff.mp found
  exact preserved old present

/-- Two actual kernel observations at the same owner are counter-ordered by the original no-install LIVE execution. -/
theorem source_mono (backend : QueryImpl RawCtxServerServices.BackendSpec (StateT State ProbComp))
    (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (entry : RawCtxProtocolReveals.State M P I D K S B) (state : State)
    (result : (Result × RawCtxProtocolReveals.State M P I D K S B) × State)
    (supported : result ∈ support ((simulateQ backend
      ((simulateQ (RawCtxProtocolReveals.protocolImpl S B sender route decode) client).run entry)).run state))
    (before after : ConcreteRatchetKernel)
    (installed : RawCtxProtocolReveals.selectedKernel selected entry.1 = some before)
    (retained : RawCtxProtocolReveals.selectedKernel selected result.1.2.1 = some after) :
    before.refined.control.send_sequence.val ≤ after.refined.control.send_sequence.val := by
  apply source_lower backend before.refined.control.send_sequence.val selected sender route decode
    client entry state result supported _ after retained
  intro kernel found
  cases Option.some.inj (installed.symm.trans found)
  exact le_refl _

/-- A literal admitted send followed by the original no-install LIVE suffix gives strict chronological counter order, even if its writer returns no frame. -/
theorem after_send_strict (backend : QueryImpl RawCtxServerServices.BackendSpec (StateT State ProbComp))
    (first : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext) (state : State)
    (active : first.refined.control.send_sequence ≠ core.num.U64.MAX)
    (sent : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) × State)
    (sentActual : sent ∈ support ((simulateQ
      (((backend ∘ₛ RawCtxServerServices.nativeLift) ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
      (RawCtxSourceSend.send first context)).run state))
    (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (entry : RawCtxProtocolReveals.State M P I D K S B)
    (installed : RawCtxProtocolReveals.selectedKernel selected entry.1 = some sent.1.1)
    (result : (Result × RawCtxProtocolReveals.State M P I D K S B) × State)
    (supported : result ∈ support ((simulateQ backend
      ((simulateQ (RawCtxProtocolReveals.protocolImpl S B sender route decode) client).run entry)).run sent.2))
    (later : ConcreteRatchetKernel)
    (retained : RawCtxProtocolReveals.selectedKernel selected result.1.2.1 = some later) :
    first.refined.control.send_sequence.val < later.refined.control.send_sequence.val := by
  have monotone := source_mono backend selected sender route decode client entry sent.2 result supported
    sent.1.1 later installed retained
  obtain ⟨_, _, _, _, _, _, _, _, _, _, advanced, _⟩ :=
    RawCtxSourceSend.send_nonexhausted_support _ first context state active sent sentActual
  omega

end BeaconcryptCore.Computational.RawCtxNativeCounterOrder

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeCounterOrder.receive_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeCounterOrder.receive_counter

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeCounterOrder.send_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeCounterOrder.send_counter

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeCounterOrder.schedule_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeCounterOrder.schedule_lower

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeCounterOrder.source_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeCounterOrder.source_lower

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeCounterOrder.source_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeCounterOrder.source_mono

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeCounterOrder.after_send_strict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeCounterOrder.after_send_strict
