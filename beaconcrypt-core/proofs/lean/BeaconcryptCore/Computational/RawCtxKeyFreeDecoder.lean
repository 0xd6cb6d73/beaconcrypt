import BeaconcryptCore.Computational.RawCtxCanonicalSchedule
import BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection

/-!
The raw CTX decoder needs the selected nonce and public source context, but never the selected message key. The nonce must be available to the simulator continuation under its actual joint sampler; this interface does not assert that production discloses the nonce on the network. This module removes the native material capability from that decoder and routes an actual reached source opening into the existing shared-cache CTX family. The original raw bytes, prepared sequence, frame sender, AD and optional challenger plaintext are preserved.

This is an operational interface theorem for arbitrary keys, including aliases. It does not identify the evolving-material distribution with an independent family, prove nonce freshness, or turn a selected-chain secrecy statement into full raw-record security. The explicit source occurrence conditions below are the conditions already proved by RawCtxOpeningOccurrence before every actual callback, including failures. Primitive implementations and local parsing work remain contracts; snapshots and persistence are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxKeyFreeDecoder
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxCanonical

/-- Normalization reads only the already selected public frame payload. -/
noncomputable def record (frame : RawCtxReceive.DecodedFrame)
    (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload frame.payload = some slices) : CtxRomRecord :=
  let value := (RawCtxFrameDecoding.fromPayload_record frame.payload slices parsed).choose
  let facts := (RawCtxFrameDecoding.fromPayload_record frame.payload slices parsed).choose_spec
  ⟨value.body, value.tag, facts.2.2.2.2.1, ⟨value.commit, facts.2.2.2.2.2.1⟩⟩

/-- No selected key, proposed plaintext or recovered plaintext occurs in the target. -/
noncomputable def target (nonce : CtxNonce) (sequence : Std.U64)
    (frame : RawCtxReceive.DecodedFrame) (ad : Pqxdh.Bytes)
    (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload frame.payload = some slices)
    (width : ad.length = 153) : CtxUnclaimedAcceptance.Target :=
  ⟨nonce, ⟨⟨ad, sequence.val, frame.sender.val⟩, width, sequence.bv.isLt, frame.sender.bv.isLt⟩,
    record frame slices parsed⟩

/-- The single decoder supplied to a component key uses its selected nonce and source AD/pin. -/
noncomputable def decoder (nonce : CtxNonce) (expected : Std.U64)
    (ad : Pqxdh.Bytes) (read : RawCtxReceive.FrameDecoder) : RawDecoder := fun raw =>
  if raw.isEmpty then none else
  match read raw with
  | none => none
  | some frame =>
      if valid : RawCtxReceive.ValidFrame expected ad frame then
        match parsed : RawCtxFrameDecoding.fromPayload frame.payload with
        | none => none
        | some slices => some (target nonce frame.sequence frame ad slices parsed valid.2.2)
      else none

/-- The actual selected native capability has exactly this key-free target. -/
theorem target_source (input : RawCtxWholeOwner.OpenInput)
    (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices)
    (width : input.context.associatedData.length = 153) :
    RawCtxCanonicalOpening.selectedTarget input slices parsed width =
      target (RawCtxSourceOpen.sourceNonce input) input.sequence input.context.frame
        input.context.associatedData slices parsed width := rfl

/-- Key erasure is exact for every raw byte string, including malformed and rejected inputs. -/
theorem decoder_source (material : RatchetMaterial) (expected : Std.U64)
    (ad : Pqxdh.Bytes) (read : RawCtxReceive.FrameDecoder) :
    RawCtxCanonicalOpening.selectedDecoder material expected ad read =
      decoder ⟨(BeaconcryptCore.Refinement.RepresentationBridge.absMaterial material).2,
        by simp [BeaconcryptCore.Refinement.RepresentationBridge.absMaterial]⟩ expected ad read := rfl

/-- Every reached source occurrence supplies the decoder equation before the optional reply exists. -/
theorem decoder_selected (input : RawCtxWholeOwner.OpenInput)
    (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (nonempty : input.context.raw.isEmpty = false)
    (decoded : read input.context.raw = some input.context.frame)
    (valid : RawCtxReceive.ValidFrame expected input.context.associatedData input.context.frame)
    (sequence : input.sequence = input.context.frame.sequence) :
    decoder (RawCtxSourceOpen.sourceNonce input) expected input.context.associatedData read input.context.raw =
      some (target (RawCtxSourceOpen.sourceNonce input) input.sequence input.context.frame
        input.context.associatedData slices parsed valid.2.2) := by
  exact RawCtxCanonicalOpening.selectedDecoder_source input slices parsed read expected nonempty decoded valid sequence

end BeaconcryptCore.Computational.RawCtxKeyFreeDecoder

/-- info: 'BeaconcryptCore.Computational.RawCtxKeyFreeDecoder.target_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKeyFreeDecoder.target_source

/-- info: 'BeaconcryptCore.Computational.RawCtxKeyFreeDecoder.decoder_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKeyFreeDecoder.decoder_source

/-- info: 'BeaconcryptCore.Computational.RawCtxKeyFreeDecoder.decoder_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKeyFreeDecoder.decoder_selected
