-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicOrdinarySpecialization
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Refinement.AdapterPublicOrdinaryEnvelope
open AdapterPublicWrapperRustT (RustT)
open AdapterRecordRequestMonad (liftRust)
open beaconcrypt_public_wrapper
variable {m : Type → Type} [Monad m] [LawfulMonad m] {A B : Type}
omit [LawfulMonad m] in
private theorem lift_ok (value : A) :
    (liftRust (.ok value) : RustT m A) = pure value := rfl
private theorem lift_bind (work : RustM A) (next : A → RustM B) :
    (liftRust (work >>= next) : RustT m B) =
      ((liftRust work : RustT m A) >>= fun value => liftRust (next value)) := by
  apply RustT.ext
  cases work <;> simp only [bind_tc_ok, bind_tc_fail, bind_tc_div,
    RustT.run_bind, RustT.run_liftRust, pure_bind]

universe u v w
omit [Monad m] [LawfulMonad m] in
private theorem call_apply {X : Type u} {F : X → Type v} {G : X → Type w}
    [∀ x, AdapterPublicWrapperLiftFunction.LiftFunction (RustT m) (F x) (G x)]
    (source : (x : X) → F x) (value : X) :
    AdapterPublicWrapperLiftFunction.call (m := RustT m) source value =
      AdapterPublicWrapperLiftFunction.call (m := RustT m) (source value) := by rfl
omit [LawfulMonad m] in
private theorem call_result (source : RustM A) :
    AdapterPublicWrapperLiftFunction.call (m := RustT m) source =
      (liftRust source : RustT m A) := by rfl

theorem take_some (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) :
    beaconcrypt_public_ordinary_request.ratchet.RatchetKernelSlot.take (m := RustT m) ⟨some kernel⟩ =
      pure (kernel, (⟨none⟩ : ratchet.RatchetKernelSlot)) := by
  change (do
    let pair ← (liftRust (.ok (some kernel, none)) : RustT m (Option _ ×Option _))
    let selected ← (liftRust (core.option.Option.expect pair.1 (toStr "a ratchet kernel is absent only while its synchronous effect is running" AdapterPublicOrdinaryString.slot_bound)) : RustT m _)
    pure (selected, (⟨pair.2⟩ : ratchet.RatchetKernelSlot))) = _
  simp only [lift_ok, pure_bind, core.option.Option.expect]

theorem put_empty (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) :
    beaconcrypt_public_ordinary_request.ratchet.RatchetKernelSlot.put (m := RustT m) ⟨none⟩ kernel =
      pure (⟨some kernel⟩ : ratchet.RatchetKernelSlot) := by
  change (do
    let valid ← (liftRust (.ok true) : RustT m Bool)
    let _ ← (liftRust (AdapterPublicOrdinaryPlatform.assertBool valid) : RustT m Unit)
    pure (⟨some kernel⟩ : ratchet.RatchetKernelSlot)) = _
  simp only [lift_ok, pure_bind, AdapterPublicOrdinaryPlatform.assertBool, massert, ite_true]


def manager (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) : ratchet.RatchetManager :=
  ⟨⟨some kernel⟩⟩

theorem deref_some (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) :
    beaconcrypt_public_ordinary_request.ratchet.RatchetKernelSlot.Insts.CoreOpsDerefDerefConcreteRatchetKernel.deref
      (m := RustT m) ⟨some kernel⟩ = pure kernel := by
  change (do
    let value ← (liftRust (.ok (some kernel)) : RustT m (Option _))
    (liftRust (core.option.Option.expect value (toStr "a ratchet kernel is absent only while its synchronous effect is running" AdapterPublicOrdinaryString.slot_bound)) : RustT m _)) = _
  simp only [lift_ok, pure_bind, core.option.Option.expect]

theorem status_some (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) :
    beaconcrypt_public_ordinary_request.ratchet.RatchetManager.status (m := RustT m) (manager kernel) =
      pure (⟨kernel.refined.control.send_sequence, kernel.refined.control.receive_sequence,
        kernel.refined.control.receive_cache.len⟩ : beaconcrypt_public_ordinary.ratchet.RatchetStatus) := by
  unfold beaconcrypt_public_ordinary_request.ratchet.RatchetManager.status manager
  rw [deref_some]
  simp only [pure_bind]
  change (do
    let send ← (liftRust (.ok kernel.refined.control.send_sequence) : RustT m _)
    let receive ← (liftRust (.ok kernel.refined.control.receive_sequence) : RustT m _)
    let cached ← (liftRust (.ok kernel.refined.control.receive_cache.len) : RustT m _)
    pure (⟨send,receive,cached⟩ : beaconcrypt_public_ordinary.ratchet.RatchetStatus)) = _
  simp only [lift_ok, pure_bind]


def prepareSend (bytes : Slice U8) (target sender : U64) (ad : Array U8 281#usize)
    (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) :
    RustM (core.option.Option beaconcrypt_core.record_effects.SealFrameContext) := do
  let empty ← core.slice.Slice.is_empty bytes
  if empty then .ok none else
    let next ← core.num.U64.checked_add kernel.refined.control.send_sequence 1#u64
    let selected ← core.option.Option.Insts.CoreOpsTry_traitTry.branch next
    match selected with
    | .Continue sequence =>
        let length ← core.slice.Slice.len bytes
        let fits ← beaconcrypt_public_ordinary.wire.frame_len length sequence sender
        let admitted ← core.option.Option.Insts.CoreOpsTry_traitTry.branch fits
        match admitted with
        | .Continue _ => do
            let context ← beaconcrypt_core.record_effects.SealFrameContext.new bytes target sender ad .Frame
            .ok (some context)
        | .Break residual =>
            core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual _ residual
    | .Break residual =>
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual _ residual


noncomputable def prepareReceive (bytes : Slice U8) (sender : U64) :
    RustM (core.option.Option beaconcrypt_core.transport.FrameView) := do
  let empty ← core.slice.Slice.is_empty bytes
  if empty then .ok none else
    let frame ← beaconcrypt_public_ordinary.ratchet.decode_crypto_frame bytes
    let selected ← core.option.Option.Insts.CoreOpsTry_traitTry.branch frame
    match selected with
    | .Continue decoded => do
        let accepted ← beaconcrypt_core.transport.admit_frame decoded.seq decoded.key_id decoded.cipher_text sender
        let admitted ← core.option.Option.Insts.CoreOpsTry_traitTry.branch accepted
        match admitted with
        | .Continue view => .ok (some view)
        | .Break residual =>
            core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual _ residual
    | .Break residual =>
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual _ residual

section Dynamic
variable [PublicWrapperPlatform.Material] [PublicWrapperPlatform.Platform] [PublicWrapperPlatform.Allocator]
variable [AdapterPublicOrdinaryRequestMonad.Operations (RustT m)]

omit [PublicWrapperPlatform.Material] in
theorem send_frame (bytes : Slice U8) (target sender : U64) (ad : Array U8 281#usize)
    (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) :
    beaconcrypt_public_ordinary_request.ratchet.encrypt_message_with_ratchet (m := RustT m)
      bytes target sender ad (manager kernel) =
    (do
      let prepared ← (liftRust (prepareSend bytes target sender ad kernel) : RustT m _)
      match prepared with
      | none => pure (none, manager kernel)
      | some context => do
          let sent ← AdapterPublicOrdinaryRequestMonad.Operations.send kernel context
          pure (sent.2, manager sent.1)) := by
  unfold beaconcrypt_public_ordinary_request.ratchet.encrypt_message_with_ratchet
    beaconcrypt_public_ordinary_request.ratchet.encrypt_with_ratchet prepareSend
  simp only [ite_true, status_some, pure_bind,
    beaconcrypt_public_ordinary_request.ratchet.RatchetStatus.impl.send_sequence]
  rw [lift_bind]
  simp only [bind_assoc]
  apply bind_congr
  intro empty
  cases empty <;> simp only [Bool.false_eq_true, ite_false, ite_true, lift_ok, pure_bind]
  rw [lift_bind]
  simp only [bind_assoc]
  apply bind_congr
  intro next
  simp only [call_apply, call_result]
  cases next <;> simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    bind_tc_ok, lift_ok, pure_bind]
  rw [lift_bind]
  simp only [bind_assoc]
  apply bind_congr
  intro length
  rw [lift_bind]
  simp only [bind_assoc]
  apply bind_congr
  intro fits
  cases fits <;> simp only [bind_tc_ok, lift_ok, pure_bind]
  rw [lift_bind]
  simp only [bind_assoc]
  apply bind_congr
  intro context
  simp only [lift_ok, pure_bind]
  dsimp only [manager]
  rw [take_some]
  simp only [pure_bind]
  apply bind_congr
  rintro ⟨changed, reply⟩
  rw [put_empty]
  simp only [pure_bind]

omit [PublicWrapperPlatform.Material] in
theorem receive_payload (ciphertext : Slice U8) (sequence sender : U64) (ad : Array U8 281#usize)
    (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) :
    beaconcrypt_public_ordinary_request.ratchet.decrypt_payload_with_ratchet (m := RustT m)
      ciphertext sequence sender ad (manager kernel) =
    (do
      let effect ← (liftRust (beaconcrypt_core.record_effects.begin_record_receive kernel sequence ciphertext ad sender) : RustT m _)
      let received ← AdapterPublicOrdinaryRequestMonad.Operations.receive effect
      pure (received.2, manager received.1)) := by
  unfold beaconcrypt_public_ordinary_request.ratchet.decrypt_payload_with_ratchet
  dsimp only [manager]
  rw [take_some]
  simp only [pure_bind, call_apply, call_result]
  apply bind_congr
  intro effect
  apply bind_congr
  rintro ⟨changed,reply⟩
  rw [put_empty]
  simp only [pure_bind]

omit [PublicWrapperPlatform.Material] in
theorem receive_frame (bytes : Slice U8) (sender : U64) (ad : Array U8 281#usize)
    (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) :
    beaconcrypt_public_ordinary_request.ratchet.decrypt_message_with_ratchet (m := RustT m)
      bytes sender ad (manager kernel) =
    (do
      let prepared ← (liftRust (prepareReceive bytes sender) : RustT m _)
      match prepared with
      | none => pure (none,manager kernel)
      | some view => do
          let effect ← (liftRust (beaconcrypt_core.record_effects.begin_record_receive kernel view.sequence view.ciphertext ad view.sender) : RustT m _)
          let received ← AdapterPublicOrdinaryRequestMonad.Operations.receive effect
          pure (received.2, manager received.1)) := by
  unfold beaconcrypt_public_ordinary_request.ratchet.decrypt_message_with_ratchet prepareReceive
  rw [lift_bind]
  simp only [bind_assoc]
  apply bind_congr
  intro empty
  cases empty <;> simp only [Bool.false_eq_true,ite_false,ite_true,lift_ok,pure_bind]
  rw [lift_bind]
  simp only [bind_assoc]
  apply bind_congr
  intro frame
  simp only [call_apply,call_result]
  cases frame <;> simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    bind_tc_ok,lift_ok,pure_bind]
  rw [lift_bind]
  simp only [bind_assoc]
  apply bind_congr
  intro accepted
  cases accepted <;> simp only [bind_tc_ok,lift_ok,pure_bind]
  exact receive_payload _ _ _ _ _

end Dynamic

end BeaconcryptCore.Refinement.AdapterPublicOrdinaryEnvelope

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryEnvelope.take_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryEnvelope.take_some

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryEnvelope.put_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryEnvelope.put_empty

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryEnvelope.deref_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryEnvelope.deref_some

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryEnvelope.status_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryEnvelope.status_some

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryEnvelope.send_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryEnvelope.send_frame

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryEnvelope.receive_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryEnvelope.receive_payload

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryEnvelope.receive_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryEnvelope.receive_frame
