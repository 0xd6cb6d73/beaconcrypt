-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishBackend
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCommonModel
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCryptoPlatform
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLeaves
/-! Literal SDK finish dictionaries retain source objects and the original primitive computations. The request interpreter supplies authentication hashes and first-record primitive effects; no owner, scalar or model result enters the executable dictionary. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDictionaries
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativeBeaconFrontend (Trusted)
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable {n : Nat} {I KemSK E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

noncomputable def authentication (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (trusted : QueryImpl (Trusted n KemSK) m) : QueryImpl RegistrationAuthenticationExecutor.Spec m :=
  fun query => simulateQ trusted (AdapterPublicFinishFreeTree.authentication (source:=source) setup query)

noncomputable def primitives (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (trusted : QueryImpl (Trusted n KemSK) m) (erased : commitment.CommitmentTranscript) :
    AdapterPublicFinishRecord.Primitives m where
  initial request := pure (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes
  kdf request := pure (RawCtxSourceHkdf.response setup.source.crypto request)
  hash transcript := do
    let digest ← trusted (.inl (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes (.Single (Std.Array.to_slice transcript.bytes))))))
    pure (.Some (RegistrationAuthenticationShared.digestArray digest), erased)
  aead request := pure (AdapterRecordNativeRepresentation.plaintext
    (RawCtxSourceOpen.baseOpen setup.source.crypto (RegistrationRecordPrimitives.openInput request)))

noncomputable def recording (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (trusted : QueryImpl (Trusted n KemSK) m) (erased : commitment.CommitmentTranscript) :
    QueryImpl AdapterRecordRequestMonad.Spec m
  | .kdf request => RustM.ok <$> (primitives setup trusted erased).kdf request
  | .hash transcript => RustM.ok <$> (primitives setup trusted erased).hash transcript
  | .aead request => RustM.ok <$> (match request with
      | none => pure none
      | some request => (primitives setup trusted erased).aead request)
  | .compare left right => pure (.ok (decide (TranscriptAuthParts.absSlice left = TranscriptAuthParts.absSlice right)))

noncomputable def record (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (trusted : QueryImpl (Trusted n KemSK) m) : QueryImpl RegistrationRecordPrimitives.Spec m :=
  fun query => simulateQ trusted (RegistrationNativeRecordJournal.core setup wire query)

omit [LawfulMonad m] in
private theorem coins_pure (trusted : QueryImpl (Trusted n KemSK) m) {A : Type} (value : A) :
    simulateQ trusted (RegistrationNativeAgreementJournal.coins (pure value)) = pure value := by
  simp only [RegistrationNativeAgreementJournal.coins, simulateQ_pure]

 theorem record_leaves (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (trusted : QueryImpl (Trusted n KemSK) m) (erased : commitment.CommitmentTranscript) :
    AdapterPublicFinishInterpret.Leaves (primitives setup trusted erased) (record setup wire trusted) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro request
    change simulateQ trusted (RegistrationNativeAgreementJournal.coins (pure (core.option.Option.Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request)))) = _
    simp only [coins_pure, primitives, map_pure]
  · intro request
    change simulateQ trusted (RegistrationNativeAgreementJournal.coins (pure (core.option.Option.Some (RawCtxSourceHkdf.response setup.source.crypto request)))) = _
    simp only [coins_pure, primitives, map_pure]
  · intro transcript
    simp only [record, RegistrationNativeRecordJournal.core, primitives,
      simulateQ_bind, simulateQ_spec_query, simulateQ_pure, map_bind, map_pure]
  · intro request
    change simulateQ trusted (RegistrationNativeAgreementJournal.coins
      (pure (RegistrationAuthenticationShared.openedBytes
        (RawCtxSourceOpen.baseOpen setup.source.crypto (RegistrationRecordPrimitives.openInput request))))) = _
    simp only [coins_pure, primitives, map_pure,
      AdapterPublicFinishRecordNative.borrowed_plaintext]

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]

omit [LawfulMonad m] material platform in
theorem source_leaves (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (trusted : QueryImpl (Trusted n KemSK) m) (erased : commitment.CommitmentTranscript)
    (parseEd : Slice U8 → m (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m) :
    let : ChildOperations (RustT m) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.authentication (authentication (source:=source) setup trusted) parseEd verifyEd)
      (recording setup trusted erased) writer
    AdapterPublicFinishRecord.Contract (primitives setup trusted erased) := by
  let : ChildOperations (RustT m) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.authentication (authentication (source:=source) setup trusted) parseEd verifyEd)
    (recording setup trusted erased) writer
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDictionaries

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDictionaries.record_leaves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDictionaries.record_leaves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDictionaries.source_leaves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDictionaries.source_leaves
