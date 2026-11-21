-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicOrdinaryReceiveGate
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerSender
open BeaconcryptCore.Computational
open AdapterPublicWrapperRustT (RustT)
variable {m : Type →Type} [Monad m] [LawfulMonad m]

theorem source (bytes : Slice U8) :
    beaconcrypt_public_ordinary_request.ratchet.encrypted_frame_sender (m:=RustT m) bytes=
      pure ((RegistrationNativeConcreteCodec.wire.parseFrame (TranscriptAuthParts.absSlice bytes)).map
        CborProductionBoundary.NativeFrame.sender) := by
  obtain ⟨parsed,decoded,projected⟩ := AdapterPublicOrdinaryReceiveGate.decode bytes
  unfold beaconcrypt_public_ordinary_request.ratchet.encrypted_frame_sender
    beaconcrypt_public_ordinary_request.ratchet.decode_crypto_frame
  change (do
    let parsed ← (AdapterRecordRequestMonad.liftRust (beaconcrypt_public_ordinary.ratchet.decode_crypto_frame bytes) : RustT m _)
    let selected ← (AdapterRecordRequestMonad.liftRust (core.option.Option.Insts.CoreOpsTry_traitTry.branch parsed) : RustT m _)
    match selected with
    | .Continue frame =>pure (some frame.key_id)
    | .Break residual =>AdapterRecordRequestMonad.liftRust (core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual U64 residual))=_
  rw [decoded]
  apply RustT.ext
  cases parsed <;> simp [RustT.run_bind,RustT.run_liftRust,RustT.run_pure,projected,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]

end BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerSender
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerSender.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerSender.source
