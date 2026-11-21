-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerSender
/-! The public adapter uses the sender read by its actual generated frame decoder on the original raw bytes. This fixes the selected deployment route and derives agreement with the complete record decoder. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRouting

noncomputable def route : RawCtxServerRouting.SenderDecoder := fun bytes =>
  (RegistrationNativeConcreteCodec.wire.parseFrame bytes).map CborProductionBoundary.NativeFrame.sender

theorem source {m : Type →Type} [Monad m] [LawfulMonad m] (bytes : Slice U8) :
    beaconcrypt_public_ordinary_request.ratchet.encrypted_frame_sender
      (m:=BeaconcryptCore.Refinement.AdapterPublicWrapperRustT.RustT m) bytes=
      pure (route (TranscriptAuthParts.absSlice bytes)) :=
  BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerSender.source bytes

theorem agreement : RawCtxServerRouting.DecoderAgreement route
    (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire).frameRead := by
  intro raw frame successful
  change CborProductionBoundary.frameDecoder RegistrationNativeConcreteCodec.wire.parseFrame raw=some frame at successful
  unfold CborProductionBoundary.frameDecoder CborTransport.boundedDecoder at successful
  split at successful
  · dsimp only at successful
    cases parsed:RegistrationNativeConcreteCodec.wire.parseFrame raw with
    | none=>
      rw [parsed] at successful
      cases successful
    | some original=>
      rw [parsed] at successful
      change some (CborProductionBoundary.decoded original)=some frame at successful
      cases Option.some.inj successful
      simp only [route,parsed,Option.map_some,CborProductionBoundary.decoded]
  · cases successful

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRouting
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRouting.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRouting.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRouting.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRouting.agreement
