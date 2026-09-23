import BeaconcryptCore.Computational.RawCtxKeyFreeDecoder

/-!
The actual source opening is consumed by the real shared-cache component handler. Each key's selected nonce and immutable decoder context are supplied without passing its unavailable secret key. The nonce remains simulator-side data; neither independence from the key nor network disclosure is asserted. The proof retains the untouched suffix dictionary, all other family entries, full shared cache and actual optional plaintext. It applies to every reached valid source opening, including failed commitment and failed AEAD outcomes, before any plaintext exists.

These are exact handler/continuation laws for arbitrary material, not an assumption that source-generated keys form an independent family. That distribution and the fixed-key sealing nonce gate still require their separate consuming composition. No snapshot or persistence interface occurs.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSharedSourceOpening
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxCanonical AdaptiveCtxSharedModes

/-- Reinstall the complete canonical poststate while preserving the unused replay suffix dictionary. -/
def retain (before : State) (after : CanonicalState) : State :=
  (((AdaptiveCtxSharedHash.separate after).1, before.1.2), (AdaptiveCtxSharedHash.separate after).2)

set_option backward.isDefEq.respectTransparency false in
/-- The real component keeps all canonical state and the identical unused suffix dictionary. -/
theorem real_complete (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : State) :
    (targetImpl true decode c key query).run state =
      (fun result => (result.1, retain state result.2)) <$>
        (AdaptiveCtxCanonical.canonicalImpl decode c key query).run (canonicalProjection state) := by
  have full := congrArg (fun work => (fun result => (result.1, retain state result.2)) <$> work)
    (AdaptiveCtxSharedHash.local_interpretation decode c key query state.1.1 state.2)
  have localEq : (AdaptiveCtxSharedModes.localImpl true decode c key query).run state.1 =
      (fun result => (result.1, (result.2, state.1.2))) <$>
        (AdaptiveCtxSharedHash.localImpl decode c key query).run state.1.1 := by
    simp only [AdaptiveCtxSharedModes.localImpl, StateT.run, if_true, bind_pure_comp]
  rw [target_run, localEq, simulateQ_map, StateT.run_map]
  simpa only [Functor.map_map, retain, AdaptiveCtxSharedHash.reassemble,
    AdaptiveCtxSharedHash.separate_install, canonicalProjection] using full

/-- Reinstall only the selected entry, retaining every other entry and the shared hash cache. -/
noncomputable def retainFamily {count : Nat} (index : Fin (count + 1))
    (before : AdaptiveCtxSharedKeySelection.SourceState count) (after : CanonicalState) :
    AdaptiveCtxSharedKeySelection.SourceState count :=
  (Function.update before.1 index ((AdaptiveCtxSharedHash.separate after).1, (before.1 index).2),
    (AdaptiveCtxSharedHash.separate after).2)

/-- Complete real-family routing exposes the exact canonical selected call, without discarding other keys' state. -/
theorem family_complete {count : Nat} (index : Fin (count + 1))
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin (count + 1) → CtxKey) (query : ReceiveSpec.Domain)
    (state : AdaptiveCtxSharedKeySelection.SourceState count) :
    (AdaptiveCtxSharedKeySelection.sourceImpl (fun _ => true) decode c keys ⟨index, query⟩).run state =
      (fun result => (result.1, retainFamily index state result.2)) <$>
        (AdaptiveCtxCanonical.canonicalImpl (decode index) c (keys index) query).run
          (canonicalProjection (state.1 index, state.2)) := by
  change (do
    let result ← (targetImpl true (decode index) c (keys index) query).run (state.1 index, state.2)
    pure (result.1, Function.update state.1 index result.2.1, result.2.2)) = _
  rw [real_complete]
  simp only [bind_pure_comp, Functor.map_map, retainFamily, retain]

/-- The actual source-selected optional opening is the real component call with a decoder that has no message key. -/
theorem reached_source {count : Nat} (index : Fin (count + 1))
    (nonce : Fin (count + 1) → CtxNonce) (expected : Fin (count + 1) → Std.U64)
    (ad : Fin (count + 1) → Pqxdh.Bytes) (read : RawCtxReceive.FrameDecoder)
    (c : Pqxdh.Crypto) (keys : Fin (count + 1) → CtxKey)
    (input : RawCtxWholeOwner.OpenInput) (state : AdaptiveCtxSharedKeySelection.SourceState count)
    (keySelected : keys index = RawCtxSourceOpen.sourceKey input)
    (nonceSelected : nonce index = RawCtxSourceOpen.sourceNonce input)
    (adSelected : ad index = input.context.associatedData)
    (nonempty : input.context.raw.isEmpty = false)
    (decoded : read input.context.raw = some input.context.frame)
    (valid : RawCtxReceive.ValidFrame (expected index) input.context.associatedData input.context.frame)
    (sequence : input.sequence = input.context.frame.sequence)
    (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices) :
    (AdaptiveCtxSharedKeySelection.sourceImpl (fun _ => true)
      (fun i => RawCtxKeyFreeDecoder.decoder (nonce i) (expected i) (ad i) read) c keys
      ⟨index, .inr input.context.raw⟩).run state =
      (fun result => (result.1, retainFamily index state result.2)) <$>
        RawCtxCanonicalOpening.sourceOpening c input
          (RawCtxCanonicalOpening.selectedTarget input slices parsed valid.2.2)
          (canonicalProjection (state.1 index, state.2)) := by
  rw [family_complete]
  simp only [keySelected, nonceSelected, adSelected, AdaptiveCtxCanonical.canonicalImpl, StateT.run]
  rw [← RawCtxCanonicalOpening.sourceOpening_canonical c input slices parsed valid.2.2 _ _
    (RawCtxKeyFreeDecoder.decoder_selected input slices parsed read (expected index)
      nonempty decoded valid sequence)]
  rfl

end BeaconcryptCore.Computational.RawCtxSharedSourceOpening

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedSourceOpening.real_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedSourceOpening.real_complete

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedSourceOpening.family_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedSourceOpening.family_complete

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedSourceOpening.reached_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedSourceOpening.reached_source
