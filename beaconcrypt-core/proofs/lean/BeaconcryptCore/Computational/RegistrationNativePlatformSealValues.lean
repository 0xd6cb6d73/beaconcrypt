-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSealReceipt

/-! Actual successful source sealing returns the fixed native AEAD ciphertext/tag on the literal source-requested operands. This primitive-value receipt retains arbitrary external sampler and allocation state and does not equate the old and Platform experiments. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSealValues
open PqxdhServerAuthExperiment (Setup Codec)
open BeaconcryptCore.Refinement
open BeaconcryptCore.Refinement.ProtocolComposition
variable {n : Nat} {E Auxiliary Platform ι KemSK Reader Response : Type} {base : OracleSpec ι}

/-- Actual native detached sealing is deterministic and updates its real World primitive counter. -/
theorem native (setup : Setup base KemSK) (codec : Codec Reader Response) (input : RawCtxSourceSeal.AeadInput)
    (before : RegistrationWorldAgreement.State n Auxiliary) :
    ∃ after, (RegistrationWorldRecords.record setup codec (.inr (.inl input))).run before =
      pure (some (setup.source.crypto.aeadSeal input.key input.nonce input.associatedData input.plaintext), after) := by
  exact ⟨_, rfl⟩

private theorem opened (bytes : Pqxdh.Bytes) (result : Slice U8)
    (actual : RegistrationAuthenticationShared.openedBytes (some bytes) = .Some result) :
    TranscriptAuthParts.absSlice result = bytes := by
  simp only [RegistrationAuthenticationShared.openedBytes] at actual
  split at actual
  · cases actual
    simp only [TranscriptAuthParts.absSlice, List.map_map, Function.comp_def, absByte_concreteByte]
    change List.map id bytes = bytes
    exact List.map_id bytes
  · cases actual

private theorem sealed (pair : Pqxdh.Bytes × Pqxdh.Bytes) (ciphertext : Slice U8) (tag : Std.Array U8 16#usize)
    (actual : RegistrationRecordPrimitives.sealedBytes (some pair) = .Some (ciphertext, tag)) :
    (TranscriptAuthParts.absSlice ciphertext, absBytes tag) = pair := by
  simp only [RegistrationRecordPrimitives.sealedBytes] at actual
  split at actual
  · cases converted : RegistrationAuthenticationShared.openedBytes (some pair.1) with
    | none => simp only [converted] at actual; cases actual
    | some bytes =>
      simp only [converted] at actual
      have body := opened pair.1 bytes converted
      cases actual
      exact Prod.ext body (by simp [absBytes, List.map_map, Function.comp_def])
  · cases actual

variable [primitive : AdapterSealPrimitive.Operations]

/-- Actual source native-AEAD success has exactly the fixed source primitive output, independently of arbitrary external uniform interpretation. -/
theorem aead (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (plaintext : Slice U8) (associated : core.option.Option (Slice U8)) (nonce : primitive.Nonce) (key : primitive.Key)
    (ciphertext : Slice U8) (tag : Std.Array U8 16#usize)
    (before after : RegistrationWorldAgreement.State n Auxiliary) (previous next : Platform)
    (supported : ((.ok (.Ok (ciphertext, tag)), after), next) ∈ support
      (((RegistrationNativePlatformSourceSeal.aead coins setup codec view failure plaintext associated nonce key).run before).run previous)) :
    (TranscriptAuthParts.absSlice ciphertext, absBytes tag) =
      setup.source.crypto.aeadSeal (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key).key
        (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key).nonce
        (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key).associatedData
        (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key).plaintext := by
  obtain ⟨final, literal⟩ := native setup codec (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key) before
  rw [RegistrationNativePlatformSourceSeal.aead_run, literal, simulateQ_pure, StateT.run_map, StateT.run_pure, map_pure,
    support_pure, Set.mem_singleton_iff] at supported
  have detached : RegistrationNativePlatformSourceSeal.detached failure (some (setup.source.crypto.aeadSeal
      (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key).key
      (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key).nonce
      (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key).associatedData
      (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key).plaintext)) = .Ok (ciphertext, tag) := by
    exact (RustM.ok.inj (congrArg (fun value => value.1.1) supported)).symm
  unfold RegistrationNativePlatformSourceSeal.detached at detached
  cases chosen : RegistrationRecordPrimitives.sealedBytes _ with
  | none => rw [chosen] at detached; cases detached
  | some result =>
    rw [chosen] at detached
    have same : result = (ciphertext, tag) := by simpa only [core.result.Result.Ok.injEq] using detached
    rw [same] at chosen
    exact sealed _ ciphertext tag chosen

/-- Successful actual allocator/seal execution uses the exact requested key, nonce, AD and prefixed plaintext and returns the fixed source ciphertext/tag. -/
theorem sealing (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (correct : view.Correct) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (request : record_effects.AeadSealRequest) (ciphertext : Slice U8) (tag : Std.Array U8 16#usize)
    (before after : RegistrationWorldAgreement.State n Auxiliary) (previous next : Platform)
    (supported : ((.ok (.Some (ciphertext, tag)), after), next) ∈ support
      (((RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation request).run before).run previous)) :
    (TranscriptAuthParts.absSlice ciphertext, absBytes tag) =
      setup.source.crypto.aeadSeal (absBytes request.key) (absBytes request.nonce) (absBytes request.associated_data)
        (RegistrationRecordPrimitives.plaintextBytes request.plaintext) := by
  obtain ⟨key, nonce, plaintext, middle, _aeadState, _keyRun, _nonceRun, _allocated, inputEq, called, _marked⟩ :=
    RegistrationNativePlatformSealReceipt.sealing coins setup codec view correct failure allocation request ciphertext tag before after previous next supported
  have actual := aead coins setup codec view failure plaintext (.Some (Std.Array.to_slice request.associated_data)) nonce key
    ciphertext tag before _ middle next called
  rw [inputEq] at actual
  exact actual

end BeaconcryptCore.Computational.RegistrationNativePlatformSealValues

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSealValues.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSealValues.native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSealValues.aead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSealValues.aead

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSealValues.sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSealValues.sealing
