-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishObservedLift
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceLogProgram
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceObservedProgram
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativeBeaconFrontend (Trusted)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
variable {m:Type→Type} [Monad m] [LawfulMonad m] {Log A Q:Type} {spec:OracleSpec Q}

private theorem queries (implementation:QueryImpl spec m) (work:OracleComp spec A) :
    simulateQ (fun query=>StateT.lift (implementation query):QueryImpl spec (StateT (List Log) m)) work=
      StateT.lift (simulateQ implementation work) :=by
  induction work using OracleComp.inductionOn with
  | pure value=>
    simp only [simulateQ_pure]
    funext past
    change (Pure.pure (value,past):m _)=(do let answer←Pure.pure value;Pure.pure (answer,past))
    simp only [pure_bind]
  | query_bind query next ih=>
    simp only [simulateQ_bind,simulateQ_spec_query,ih]
    exact (monadLift_bind (m:=m) (n:=StateT (List Log) m) (implementation query) (fun reply=>simulateQ implementation (next reply))).symm

variable [material:PublicWrapperPlatform.Material] [platform:PublicWrapperPlatform.Platform]
variable [ed:AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.CryptoOperations]
variable [original:CryptoOperations (RustT m)]
variable {n:Nat} {I KemSK E:Type} {base:OracleSpec I} {mlSource:RegistrationNativeMldsa.Source}
variable (setup:PqxdhServerAuthExperiment.Setup base KemSK) (wire:RegistrationNativeWire.Wire)
variable (trusted:QueryImpl (Trusted n KemSK) m) (note:Stage→Log)

noncomputable def completion (self:beaconcrypt_public_wrapper.beacon.Beacon) (agreed:agreement.BeaconAgreement) :
    RustT (StateT (List Log) m) AdapterPublicFinishBody.Result:=
  ⟨RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.suffix setup wire trusted note self (.BeaconComplete agreed)⟩

noncomputable def run (erased:commitment.CommitmentTranscript)
    (parseEd:Slice U8→m (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd:Slice U8→ed.PublicKey→m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer:QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (self:beaconcrypt_public_wrapper.beacon.Beacon) (input:Slice U8) :StateT (List Log) m (RustM AdapterPublicFinishBody.Result):=
  letI :CryptoOperations (RustT (StateT (List Log) m)):=AdapterPublicFinishObservedLift.cryptography
  letI :ChildOperations (RustT (StateT (List Log) m)):=AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.authentication
      (fun query=>StateT.lift (RegistrationNativePlatformSdkFinishDictionaries.authentication (source:=mlSource) setup trusted query))
      (fun bytes=>StateT.lift (parseEd bytes)) (fun bytes key=>StateT.lift (verifyEd bytes key)))
    (fun query=>StateT.lift (RegistrationNativePlatformSdkFinishDictionaries.recording setup trusted erased query))
    (fun query=>StateT.lift (writer query))
  letI :Codecs (RustT (StateT (List Log) m)):=AdapterPublicConcreteCodecs.codecs
  (AdapterPublicFinishObservedRequest.run (m:=RustT (StateT (List Log) m)) (completion setup wire trusted note) self input).run

variable (view:AdapterPublicWrapperState.MaterialView mlSource KemSK)
variable (model:AdapterPublicAgreementCommonModel.Model (m:=m) setup view)

omit platform in
theorem accepted (self:beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime:beaconcrypt_crypto.crypto_kx.KeyPair) (kem:beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (authenticated:registration.AuthenticatedResponse) :
    letI :CryptoOperations (RustT (StateT (List Log) m)):=AdapterPublicFinishObservedLift.cryptography
    (AdapterPublicFinishObservedBody.accepted (completion setup wire trusted note) self prekey oneTime kem authenticated).run=
      RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.accepted setup wire trusted note view model self prekey oneTime kem authenticated :=by
  let :CryptoOperations (RustT (StateT (List Log) m)):=AdapterPublicFinishObservedLift.cryptography
  have grouped:AdapterPublicFinishObservedBody.accepted (completion setup wire trusted note) self prekey oneTime kem authenticated=(do
    let agreed←(do
      let phase←AdapterRecordRequestMonad.liftRust (agreement.begin_beacon_agreement authenticated)
      beaconcrypt_public_request.pqxdh.execute_beacon_agreement phase (AdapterPublicAgreementBeaconMaterial.registrationKeys self prekey oneTime kem))
    AdapterPublicFinishObservedBody.fromAgreement (completion setup wire trusted note) self agreed):=by
    simp only [AdapterPublicFinishObservedBody.accepted,AdapterPublicAgreementBeaconMaterial.registrationKeys,bind_assoc]
  rw [grouped,RustT.run_bind,AdapterPublicFinishObservedLift.agreement setup view model]
  unfold RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.accepted
  apply bind_congr
  intro result
  cases result with
  | fail error | div=>rfl
  | ok effect=>cases effect with
    | Rejected optional=>cases optional <;>rfl
    | _=>rfl

omit platform in
theorem source (erased:commitment.CommitmentTranscript)
    (parseEd:Slice U8→m (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd:Slice U8→ed.PublicKey→m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer:QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (self:beaconcrypt_public_wrapper.beacon.Beacon) (input:Slice U8) :
    run (mlSource:=mlSource) setup wire trusted note erased parseEd verifyEd writer self input=
      RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.program setup wire trusted note view model self input :=by
  let :CryptoOperations (RustT (StateT (List Log) m)):=AdapterPublicFinishObservedLift.cryptography
  let auth:QueryImpl RegistrationAuthenticationExecutor.Spec (StateT (List Log) m):=fun query=>StateT.lift (RegistrationNativePlatformSdkFinishDictionaries.authentication (source:=mlSource) setup trusted query)
  let :ChildOperations (RustT (StateT (List Log) m)):=AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.authentication auth (fun bytes=>StateT.lift (parseEd bytes)) (fun bytes key=>StateT.lift (verifyEd bytes key)))
    (fun query=>StateT.lift (RegistrationNativePlatformSdkFinishDictionaries.recording setup trusted erased query)) (fun query=>StateT.lift (writer query))
  let :Codecs (RustT (StateT (List Log) m)):=AdapterPublicConcreteCodecs.codecs
  change (AdapterPublicFinishObservedRequest.run (m:=RustT (StateT (List Log) m)) (completion setup wire trusted note) self input).run=_
  rw [AdapterPublicFinishObservedBody.authentication (completion setup wire trusted note) auth
    (fun bytes=>StateT.lift (parseEd bytes)) (fun bytes key=>StateT.lift (verifyEd bytes key))
    (fun query=>StateT.lift (RegistrationNativePlatformSdkFinishDictionaries.recording setup trusted erased query)) (fun query=>StateT.lift (writer query))]
  unfold RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.program
  cases phase:self.state with
  | InitSent pending prekey oneTime kem=>
    cases aborted:pending.aborted_state with
    | fail error | div=>simp only [aborted]
    | ok control=>
      simp only [aborted]
      change (do
        let reply←simulateQ auth (RegistrationResponseExecutor.begin pending (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)))
        AdapterPublicFinishObservedBody.after (completion setup wire trusted note) {self with state:=.Aborted control} prekey oneTime kem reply)=_
      rw [queries]
      apply bind_congr
      intro reply
      cases reply with
      | fail error | div=>rfl
      | ok result=>cases result with
        | Err control=>rfl
        | Ok authenticated=>exact accepted setup wire trusted note view model _ prekey oneTime kem authenticated
  | _=>rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceObservedProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceObservedProgram.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceObservedProgram.accepted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceObservedProgram.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceObservedProgram.source
