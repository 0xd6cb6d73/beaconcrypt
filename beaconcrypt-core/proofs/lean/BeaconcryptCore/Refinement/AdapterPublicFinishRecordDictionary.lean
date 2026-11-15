-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishRecordNative
import BeaconcryptCore.Refinement.AdapterPublicWrapperChildren
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishRecordDictionary
open BeaconcryptCore.Computational
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativeBeaconFrontend (M)
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def recording (setup : PqxdhServerAuthExperiment.Setup base KemSK) (erased : commitment.CommitmentTranscript) :
    QueryImpl AdapterRecordRequestMonad.Spec (M n KemSK source Auxiliary)
  | .kdf request => RustM.ok <$> (AdapterPublicFinishRecordNative.primitives setup erased).kdf request
  | .hash transcript => RustM.ok <$> (AdapterPublicFinishRecordNative.primitives setup erased).hash transcript
  | .aead request => RustM.ok <$> (match request with
      | none => pure none
      | some request => (AdapterPublicFinishRecordNative.primitives setup erased).aead request)
  | .compare left right => pure (.ok (decide (TranscriptAuthParts.absSlice left = TranscriptAuthParts.absSlice right)))

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] {E : Type}

omit material platform in
theorem source_leaves (setup : PqxdhServerAuthExperiment.Setup base KemSK) (erased : commitment.CommitmentTranscript)
    (authentication : QueryImpl AdapterPublicWrapperChildren.AuthenticationSpec (M n KemSK source Auxiliary))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (M n KemSK source Auxiliary)) :
    letI : ChildOperations (RustT (M n KemSK source Auxiliary)) :=
      AdapterPublicWrapperChildren.children authentication (recording setup erased) writer
    AdapterPublicFinishRecord.Contract (AdapterPublicFinishRecordNative.primitives (n := n) (source := source) (Auxiliary := Auxiliary) setup erased) := by
  let : ChildOperations (RustT (M n KemSK source Auxiliary)) :=
    AdapterPublicWrapperChildren.children authentication (recording setup erased) writer
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

variable [localOps : LocalOperations (RustT (M n KemSK source Auxiliary))]
variable [PublicWrapperPlatform.CryptoOperations]

omit [PublicWrapperPlatform.CryptoOperations] in
theorem first_open (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased : commitment.CommitmentTranscript)
    (authentication : QueryImpl AdapterPublicWrapperChildren.AuthenticationSpec (M n KemSK source Auxiliary))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (M n KemSK source Auxiliary))
    (initial : ∀ request, (localOps.ratchet_initial_ratchet_hkdf request).run =
      pure (.ok (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes))
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (agreed : agreement.BeaconAgreement) :
    letI : ChildOperations (RustT (M n KemSK source Auxiliary)) :=
      AdapterPublicWrapperChildren.children authentication (recording setup erased) writer
    (AdapterPublicFinishBody.beginOpen (m := M n KemSK source Auxiliary) self agreed).run =
      (fun answer => AdapterPublicFinishRecord.wrap self (AdapterPublicFinishRecord.result self.identity_key_kid answer)) <$>
        simulateQ (RegistrationNativeRecordJournal.unlogged setup wire) (RegistrationBeaconRecordExecutor.begin agreed) := by
  let : ChildOperations (RustT (M n KemSK source Auxiliary)) :=
    AdapterPublicWrapperChildren.children authentication (recording setup erased) writer
  apply AdapterPublicFinishInterpret.source (AdapterPublicFinishRecordNative.primitives setup erased)
    (RegistrationNativeRecordJournal.unlogged setup wire) (source_leaves setup erased authentication writer)
    (AdapterPublicFinishRecordNative.leaves setup wire erased) _ self agreed
  intro request
  simpa only [AdapterPublicFinishRecordNative.primitives, map_pure] using initial request
end BeaconcryptCore.Refinement.AdapterPublicFinishRecordDictionary
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishRecordDictionary.source_leaves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishRecordDictionary.source_leaves
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishRecordDictionary.first_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishRecordDictionary.first_open
