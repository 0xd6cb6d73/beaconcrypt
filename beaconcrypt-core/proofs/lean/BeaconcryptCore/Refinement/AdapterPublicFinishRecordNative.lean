-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordJournal
import BeaconcryptCore.Refinement.AdapterPublicFinishInterpret
import BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishRecordNative
open BeaconcryptCore.Computational
open RegistrationNativeBeaconFrontend (M)
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def primitives (setup : PqxdhServerAuthExperiment.Setup base KemSK) (erased : commitment.CommitmentTranscript) :
    AdapterPublicFinishRecord.Primitives (M n KemSK source Auxiliary) where
  initial request := pure (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes
  kdf request := pure (RawCtxSourceHkdf.response setup.source.crypto request)
  hash transcript := do
    let digest ← RegistrationNativeBeaconFrontend.hash (.Single (Std.Array.to_slice transcript.bytes))
    pure (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest), erased)
  aead request := pure (AdapterRecordNativeRepresentation.plaintext
    (RawCtxSourceOpen.baseOpen setup.source.crypto (RegistrationRecordPrimitives.openInput request)))

theorem borrowed_plaintext (reply : Option Pqxdh.Bytes) :
    AdapterPublicInitPublication.borrowed (AdapterRecordNativeRepresentation.plaintext reply) =
      RegistrationAuthenticationShared.openedBytes reply := by
  cases reply with
  | none => rfl
  | some bytes =>
      simp only [AdapterRecordNativeRepresentation.plaintext, Option.bind_some, RegistrationAuthenticationShared.openedBytes]
      split <;> rfl

theorem initial (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased : commitment.CommitmentTranscript) (request : ratchet.SymmetricRatchetKdfRequest) :
    RegistrationNativeRecordJournal.unlogged (n := n) (source := source) (Auxiliary := Auxiliary) setup wire (.initialKdf request) =
      (fun bytes => core.option.Option.Some (⟨bytes⟩ : pqxdh.concrete.InitialRatchetKdfResponse)) <$>
        (primitives setup erased).initial request := by
  rfl

theorem kdf (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased : commitment.CommitmentTranscript) (request : ratchet.SymmetricRatchetKdfRequest) :
    RegistrationNativeRecordJournal.unlogged (n := n) (source := source) (Auxiliary := Auxiliary) setup wire (.ratchetKdf request) =
      core.option.Option.Some <$> (primitives setup erased).kdf request := by
  rfl

theorem hash (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased transcript : commitment.CommitmentTranscript) :
    RegistrationNativeRecordJournal.unlogged (n := n) (source := source) (Auxiliary := Auxiliary) setup wire (.hash transcript) =
      Prod.fst <$> (primitives setup erased).hash transcript := by
  change (RegistrationNativeBeaconFrontend.hash (.Single (Std.Array.to_slice transcript.bytes)) >>= fun digest => pure (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest))) =
    Prod.fst <$> (RegistrationNativeBeaconFrontend.hash (.Single (Std.Array.to_slice transcript.bytes)) >>= fun digest => pure (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest), erased))
  rw [map_bind]
  apply bind_congr
  intro digest
  simp only [map_pure]

theorem aead (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased : commitment.CommitmentTranscript) (request : record.AeadRequest) :
    RegistrationNativeRecordJournal.unlogged (n := n) (source := source) (Auxiliary := Auxiliary) setup wire (.openAead request) =
      AdapterPublicInitPublication.borrowed <$> (primitives setup erased).aead request := by
  rw [show (primitives (n := n) (source := source) (Auxiliary := Auxiliary) setup erased).aead request =
    pure (AdapterRecordNativeRepresentation.plaintext (RawCtxSourceOpen.baseOpen setup.source.crypto (RegistrationRecordPrimitives.openInput request))) from rfl, map_pure, borrowed_plaintext]
  rfl

theorem leaves (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased : commitment.CommitmentTranscript) :
    AdapterPublicFinishInterpret.Leaves (primitives (n := n) (source := source) (Auxiliary := Auxiliary) setup erased)
      (RegistrationNativeRecordJournal.unlogged setup wire) :=
  ⟨initial setup wire erased, kdf setup wire erased, hash setup wire erased, aead setup wire erased⟩
end BeaconcryptCore.Refinement.AdapterPublicFinishRecordNative
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishRecordNative.borrowed_plaintext' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishRecordNative.borrowed_plaintext
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishRecordNative.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishRecordNative.initial
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishRecordNative.kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishRecordNative.kdf
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishRecordNative.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishRecordNative.hash
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishRecordNative.aead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishRecordNative.aead
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishRecordNative.leaves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishRecordNative.leaves
