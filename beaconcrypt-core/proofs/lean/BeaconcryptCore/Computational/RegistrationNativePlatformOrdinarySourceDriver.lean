-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterRecordStatefulSend
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySend
/-! The actual outer send body is folded through its existing core-phase controller under arbitrary common-state callbacks. The optional Vec view is the actual standard read-only byte view, and every enclosing Rust failure/divergence remains in RustT. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceDriver
open BeaconcryptCore.Refinement
open AdapterRecordSendRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {m : Type → Type} [Monad m] [Operations (RustT m)]
abbrev Result := AdapterRecordStatefulSend.Result
private def fromWrite (pending : record_effects.SealWrite) : RustT m Result := do
  let request ← Lifted.writerRequest pending
  let written ← Operations.writer request
  let (kernel, output) ← Lifted.writerFinish pending written
  let encrypted ← Lifted.outputMap output
  pure (kernel, encrypted)
private def fromCommitment (pending : record_effects.SealCommitment) : RustT m Result := do
  let (transcript, back) ← Lifted.transcriptMut pending
  let (digest, changed) ← Operations.hash transcript
  let next ← Lifted.commitmentResume (back changed) digest
  match next with
  | .Rejected kernel => pure (kernel, .None)
  | .WriteRequested writer => fromWrite writer
private def afterAead (next : record_effects.SealAfterAead) : RustT m Result :=
  match next with
  | .Rejected kernel => pure (kernel, .None)
  | .CommitmentRequested pending => fromCommitment pending
private def fromAead (pending : record_effects.SealAead) : RustT m Result := do
  let request ← Lifted.sealRequest pending
  let detached ← Operations.sealing request
  let borrowed ← Lifted.asRef detached
  match borrowed with
  | .None => do
      let next ← Lifted.sealResume pending .None
      afterAead next
  | .Some pair => do
      let (body, tag) := pair
      let bytes ← Lifted.asSlice body
      let next ← Lifted.sealResume pending (.Some (bytes, tag))
      afterAead next
private def fromKdf (pending : record_effects.RecordSendKdf) : RustT m Result := do
  let request ← Lifted.kdfRequest pending
  let response ← Operations.kdf request
  let ready ← Lifted.kdfResume pending response
  fromAead ready
private def source (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (context : record_effects.SealFrameContext) : RustT m Result := do
  let next ← Lifted.beginSend kernel context
  match next with
  | .Rejected original => pure (original, .None)
  | .KdfRequested pending => fromKdf pending
private theorem body_factor (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (context : record_effects.SealFrameContext) :
    AdapterRecordSendRequestExtraction.execute (m := RustT m) kernel context = source kernel context := by
  rfl
variable [LawfulMonad m]
/-- The actual generated closure preserves ciphertext, target identifier and allocated sequence. -/
def render (result : RegistrationNativePlatformOrdinarySend.Result) : RustT m Result := do
  let encrypted ← Lifted.outputMap result.2
  pure (result.1, encrypted)
private theorem write_fold (pending : record_effects.SealWrite) :
    fromWrite (m := m) pending =
      (RegistrationNativePlatformOrdinarySend.fromWrite (fun request => (Operations.writer (m := RustT m) request).run) pending >>= render (m := m)) := by
  unfold fromWrite RegistrationNativePlatformOrdinarySend.fromWrite render
  simp only [Lifted.writerRequest, Lifted.writerFinish, bind_assoc]

omit [Operations (RustT m)] in
private theorem render_none (kernel : ratchet.concrete.ConcreteRatchetKernel) :
    render (m := m) (kernel, .None) = pure (kernel, .None) := by
  apply RustT.ext
  simp only [render, Lifted.outputMap, RustT.run_bind, RustT.run_liftRust,
    RustT.run_pure, core.option.Option.map, pure_bind]

private theorem commitment_fold (pending : record_effects.SealCommitment) :
    fromCommitment (m := m) pending =
      (RegistrationNativePlatformOrdinarySend.fromCommitment
        (fun transcript => (Operations.hash (m := RustT m) transcript).run)
        (fun request => (Operations.writer (m := RustT m) request).run) pending >>= render (m := m)) := by
  unfold fromCommitment RegistrationNativePlatformOrdinarySend.fromCommitment
  simp only [Lifted.transcriptMut, Lifted.commitmentResume, bind_assoc]
  apply bind_congr
  rintro ⟨transcript, back⟩
  apply bind_congr
  rintro ⟨digest, changed⟩
  apply bind_congr
  intro next
  cases next <;> simp only [pure_bind, render_none, write_fold]

omit [Operations (RustT m)] [LawfulMonad m] in
private theorem asRef_exact (value : core.option.Option (alloc.vec.Vec U8 × Array U8 16#usize)) :
    Lifted.asRef (m := RustT m) value = pure value := by
  cases value <;> rfl

omit [Operations (RustT m)] [LawfulMonad m] in
private theorem asSlice_exact (value : alloc.vec.Vec U8) :
    Lifted.asSlice (m := RustT m) value = (pure (value : Slice U8) : RustT m (Slice U8)) := rfl

private theorem aead_fold (pending : record_effects.SealAead) :
    fromAead (m := m) pending =
      (RegistrationNativePlatformOrdinarySend.fromAead
        (fun request => (Operations.sealing (m := RustT m) request).run)
        (fun transcript => (Operations.hash (m := RustT m) transcript).run)
        (fun request => (Operations.writer (m := RustT m) request).run) pending >>= render (m := m)) := by
  unfold fromAead RegistrationNativePlatformOrdinarySend.fromAead
  simp only [Lifted.sealRequest, bind_assoc]
  apply bind_congr
  intro request
  apply bind_congr
  intro detached
  rw [asRef_exact, pure_bind]
  cases detached with
  | none =>
      simp only [Lifted.sealResume]
      apply bind_congr
      intro next
      cases next <;> simp only [afterAead, pure_bind, render_none, commitment_fold]
  | some pair =>
      rcases pair with ⟨body, tag⟩
      simp only [asSlice_exact, Lifted.sealResume]
      erw [pure_bind]
      apply bind_congr
      intro next
      cases next <;> simp only [afterAead, pure_bind, render_none, commitment_fold]

private theorem kdf_fold (pending : record_effects.RecordSendKdf) :
    fromKdf (m := m) pending =
      (RegistrationNativePlatformOrdinarySend.fromKdf
        (fun request => (Operations.kdf (m := RustT m) request).run)
        (fun request => (Operations.sealing (m := RustT m) request).run)
        (fun transcript => (Operations.hash (m := RustT m) transcript).run)
        (fun request => (Operations.writer (m := RustT m) request).run) pending >>= render (m := m)) := by
  unfold fromKdf RegistrationNativePlatformOrdinarySend.fromKdf
  simp only [Lifted.kdfRequest, Lifted.kdfResume, bind_assoc]
  apply bind_congr
  intro request
  apply bind_congr
  intro response
  apply bind_congr
  intro ready
  exact aead_fold ready

/-- The actual extracted outer driver equals its core-phase controller for arbitrary stateful local callbacks, retaining all enclosing Rust outcomes and the exact output closure. -/
theorem controller (kernel : ratchet.concrete.ConcreteRatchetKernel) (context : record_effects.SealFrameContext) :
    AdapterRecordSendRequestExtraction.execute (m := RustT m) kernel context =
      (RegistrationNativePlatformOrdinarySend.execute
        (fun request => (Operations.kdf (m := RustT m) request).run)
        (fun request => (Operations.sealing (m := RustT m) request).run)
        (fun transcript => (Operations.hash (m := RustT m) transcript).run)
        (fun request => (Operations.writer (m := RustT m) request).run) kernel context >>= render (m := m)) := by
  rw [body_factor]
  unfold source RegistrationNativePlatformOrdinarySend.execute
  simp only [Lifted.beginSend, bind_assoc]
  apply bind_congr
  intro next
  cases next with
  | Rejected original => simp only [pure_bind, render_none]
  | KdfRequested pending => exact kdf_fold pending

omit [Operations (RustT m)] in
/-- Interpreting the actual source request program under any shared-state implementation is the complete core controller with those same four dynamic callbacks. -/
theorem program (implementation : QueryImpl Spec m)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (context : record_effects.SealFrameContext) :
    simulateQ implementation (AdapterRecordStatefulSend.program kernel context) =
      ((do
        let result ← RegistrationNativePlatformOrdinarySend.execute
          (fun request => implementation (.kdf request))
          (fun request => implementation (.sealing request))
          (fun transcript => implementation (.hash transcript))
          (fun request => implementation (.writer request)) kernel context
        render result : RustT m Result).run) := by
  rw [AdapterRecordStatefulSend.interpreted]
  unfold AdapterRecordStatefulSend.execute
  let : Operations (RustT m) := operations implementation
  exact congrArg RustT.run (controller (m := m) kernel context)

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceDriver.controller' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceDriver.controller

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceDriver.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceDriver.program

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceDriver
