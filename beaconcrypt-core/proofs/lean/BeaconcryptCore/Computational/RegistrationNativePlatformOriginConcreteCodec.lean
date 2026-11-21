-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperiment
/-! The record-origin argument uses the actual extracted Frame decoder on the canonical internal writer. Its readback is proved from the extracted codec, not required from a caller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginConcreteCodec
open BeaconcryptCore.Refinement
local notation "wire" => RegistrationNativePlatformConcreteSource.wire
local notation "codec" => RegistrationNativeWire.ledgerCodec wire

/-- Every admitted canonical source frame reads back through the actual extracted parser, including its inclusive complete-message bound. -/
theorem canonical : CborRawCanonicalBuild.CanonicalReadBack codec := by
  intro frame admitted
  have representable : frame.payload.length < 2^64 := by
    unfold CborSizing.frameLen CborSizing.byteStringLen CborSizing.maxMessageSize at admitted
    omega
  have fits : (CborTransport.render frame).length ≤ CborSizing.maxMessageSize := by
    rwa [CborTransport.render_length frame representable]
  change CborTransport.boundedDecoder (fun raw => CborProductionBoundary.decoded <$> (RegistrationNativePlatformConcreteSource.wire).parseFrame raw)
    (CborTransport.render frame) = some frame
  unfold CborTransport.boundedDecoder
  rw [ite_eq_left fits]
  change CborProductionBoundary.decoded <$> RegistrationNativeConcreteCodec.wire.parseFrame (CborTransport.render frame) = some frame
  rw [RegistrationNativeConcreteCodec.frame_projection]
  exact FrameCodecReadBack.render_readback frame representable fits

/-- The real codec discharges the only frame readback contract used by the source origin and binding attachments. -/
theorem readback : PqxdhServerAuthNegativeControl.FrameReadBack
    (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) :=
  CborRawCanonicalBuild.frame_readBack codec canonical

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginConcreteCodec

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginConcreteCodec.canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginConcreteCodec.canonical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginConcreteCodec.readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginConcreteCodec.readback
