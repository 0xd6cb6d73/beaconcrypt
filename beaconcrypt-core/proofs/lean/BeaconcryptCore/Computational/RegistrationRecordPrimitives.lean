-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAuthenticationShared
import BeaconcryptCore.Computational.MldsaSharedSource

/-!
Typed initial-record callbacks consume the actual extracted requests. Initial and ongoing ratchet replies come from the same supplied HKDF source; commitments use the same record/authentication random-oracle cache. Raw registration writing concatenates the protected ciphertext, tag and commitment, while frame writing invokes the existing outer writer. Slice representability failures return None without rolling back primitive effects. Arbitrary optional native replies remain available to the source controller's open interface; this concrete specialization uses the existing functional HKDF, AEAD and total ROM presentation.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationRecordPrimitives

open CtxRomAuth
open BeaconcryptCore.Refinement.ProtocolComposition (concreteByte)

inductive Request where
  | rootKdf (request : pqxdh.RootKeyInput)
  | initialKdf (request : ratchet.SymmetricRatchetKdfRequest)
  | ratchetKdf (request : ratchet.SymmetricRatchetKdfRequest)
  | seal (request : record_effects.AeadSealRequest)
  | hash (request : commitment.CommitmentTranscript)
  | write (request : record_effects.RecordWriteRequest)
  | openAead (request : record.AeadRequest)

abbrev Spec : OracleSpec Request
  | .rootKdf _ => core.option.Option (Std.Array Std.U8 32#usize)
  | .initialKdf _ => core.option.Option pqxdh.concrete.InitialRatchetKdfResponse
  | .ratchetKdf _ => core.option.Option ratchet.RatchetKdfResponse
  | .seal _ => core.option.Option (Slice Std.U8 × Std.Array Std.U8 16#usize)
  | .hash _ => core.option.Option (Std.Array Std.U8 64#usize)
  | .write _ | .openAead _ => core.option.Option (Slice Std.U8)

def plaintextBytes : record_effects.SealPlaintextRequest → Pqxdh.Bytes
  | .Single bytes => TranscriptAuthParts.absSlice bytes
  | .Prefixed prefixBytes bytes => absBytes prefixBytes ++ TranscriptAuthParts.absSlice bytes

def partsBytes (parts : Std.Array (Slice Std.U8) 3#usize) : Pqxdh.Bytes :=
  (parts.val.map TranscriptAuthParts.absSlice).flatten

def sealInput (request : record_effects.AeadSealRequest) : RawCtxSourceSeal.AeadInput :=
  ⟨absBytes request.key, absBytes request.nonce, absBytes request.associated_data, plaintextBytes request.plaintext⟩

def openInput (request : record.AeadRequest) : RawCtxSourceOpen.BaseInput :=
  ⟨absBytes request.key, absBytes request.nonce, absBytes request.associated_data,
    TranscriptAuthParts.absSlice request.ciphertext⟩

def sealedBytes (reply : Option (Pqxdh.Bytes × Pqxdh.Bytes)) :
    core.option.Option (Slice Std.U8 × Std.Array Std.U8 16#usize) :=
  match reply with
  | none => .None
  | some (ciphertext, tag) =>
      if width : tag.length = 16 then
        match RegistrationAuthenticationShared.openedBytes (some ciphertext) with
        | .None => .None
        | .Some bytes => .Some (bytes, ⟨tag.map concreteByte,
            by simpa only [List.length_map, Std.UScalar.ofNatCore_val_eq] using width⟩)
      else .None

private def noMldsa : MldsaTranscriptAuth.Verify := fun _ _ _ _ => false

/-- Every primitive argument is taken from its actual extracted request, including raw versus framed record writing. -/
def callbacks (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) :
    QueryImpl Spec (OracleComp MldsaSharedNative.Spec)
  | .rootKdf request => pure (.Some (RawCtxSourceHkdf.rootResponse source.crypto request))
  | .initialKdf request => pure (.Some (RawCtxSourceHkdf.initialResponse source.crypto request))
  | .ratchetKdf request => do
      let response ← MldsaSharedNative.recordLift (.inl request)
      pure (.Some response)
  | .seal request => do
      let result ← MldsaSharedNative.recordLift (.inr (.inl (sealInput request)))
      pure (sealedBytes result)
  | .hash transcript =>
      RegistrationAuthenticationShared.callbacks source.crypto noMldsa
        (.hash (.Single (Std.Array.to_slice transcript.bytes)))
  | .write (.Raw parts) => pure (RegistrationAuthenticationShared.openedBytes (some (partsBytes parts)))
  | .write (.Frame parts sequence sender) => do
      let result ← MldsaSharedNative.recordLift (.inr (.inr (.inr (.inr ⟨sequence, sender, partsBytes parts⟩))))
      pure (RegistrationAuthenticationShared.openedBytes result)
  | .openAead request => do
      let result ← MldsaSharedNative.recordLift (.inr (.inr (.inl (openInput request))))
      pure (RegistrationAuthenticationShared.openedBytes result)

noncomputable def implementation {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) :
    QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  MldsaSharedSource.implementation source writer ∘ₛ callbacks source

/-- Actual agreement root derivation uses the same selected HKDF source and preserves the complete separate primitive state. -/
theorem root_exact {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (request : pqxdh.RootKeyInput)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (implementation source writer (.rootKdf request)).run state =
      pure (.Some (RawCtxSourceHkdf.rootResponse source.crypto request), state) := by
  rfl

theorem initial_exact {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (request : ratchet.SymmetricRatchetKdfRequest)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (implementation source writer (.initialKdf request)).run state =
      pure (.Some (RawCtxSourceHkdf.initialResponse source.crypto request), state) := by
  rfl

theorem raw_write_exact {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (parts : Std.Array (Slice Std.U8) 3#usize)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (implementation source writer (.write (.Raw parts))).run state =
      pure (RegistrationAuthenticationShared.openedBytes (some (partsBytes parts)), state) := by
  rfl

/-- Initial-record commitment hashing and incoming authentication hashing use the same complete primitive state and cache. -/
theorem hash_exact {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (request : commitment.CommitmentTranscript)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (implementation source writer (.hash request)).run state =
      (fun result => (.Some (RegistrationAuthenticationShared.digestArray result.1), (state.1, result.2))) <$>
        (ctxRandomOracle ((), absBytes request.bytes)).run state.2 := by
  exact RegistrationAuthenticationShared.hash_exact source.crypto noMldsa writer (RawCtxSourceHkdf.kdfImpl source)
    (.Single (Std.Array.to_slice request.bytes)) state

/-- Native initial-record programs preserve the common cache on every path, including failure. -/
theorem program_cache_persists {Auxiliary Output : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (work : OracleComp Spec Output) (state : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : Output × RawCtxSharedPrimitive.SharedState Auxiliary)
    (supported : result ∈ support ((simulateQ (implementation source writer) work).run state)) :
    state.2 ≤ result.2.2 := by
  rw [implementation, QueryImpl.simulateQ_compose] at supported
  exact MldsaSharedSource.program_cache_persists source writer _ state result supported

/-- Authentication/signing history stored in the unrelated auxiliary coordinate survives every actual first-record callback. -/
theorem program_auxiliary_unchanged {Auxiliary Output : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (work : OracleComp Spec Output) (state : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : Output × RawCtxSharedPrimitive.SharedState Auxiliary)
    (supported : result ∈ support ((simulateQ (implementation source writer) work).run state)) :
    result.2.1 = state.1 := by
  rw [implementation, QueryImpl.simulateQ_compose] at supported
  exact MldsaSharedSource.program_auxiliary_unchanged source writer _ state result supported

end BeaconcryptCore.Computational.RegistrationRecordPrimitives

/-- info: 'BeaconcryptCore.Computational.RegistrationRecordPrimitives.initial_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRecordPrimitives.initial_exact
/-- info: 'BeaconcryptCore.Computational.RegistrationRecordPrimitives.raw_write_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRecordPrimitives.raw_write_exact
/-- info: 'BeaconcryptCore.Computational.RegistrationRecordPrimitives.hash_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRecordPrimitives.hash_exact
/-- info: 'BeaconcryptCore.Computational.RegistrationRecordPrimitives.program_cache_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRecordPrimitives.program_cache_persists
/-- info: 'BeaconcryptCore.Computational.RegistrationRecordPrimitives.program_auxiliary_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRecordPrimitives.program_auxiliary_unchanged
/-- info: 'BeaconcryptCore.Computational.RegistrationRecordPrimitives.root_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRecordPrimitives.root_exact
