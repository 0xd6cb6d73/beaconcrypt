-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCreateStep
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinParsing
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReply
/-! Raw constructor dispatch uses original source pin slices. Invalid pins execute the actual extracted pure rejection, while valid pins invoke the actual shared constructor and internally retain its complete material relation. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateDispatch
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformExtractedSdkCreateReceipt (SourceM)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
private theorem pure_apply {S A : Type} {m : Type →Type} [Monad m] (value : A) (state : S) :
    (pure value : StateT S m A) state=pure (value,state) := rfl
variable {n : Nat} {I KemSK R Error Platform : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations (RustT (SourceM n KemSK source Platform))]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (RustT (SourceM n KemSK source Platform))]
variable [children : AdapterPublicWrapperRequestMonad.ChildOperations (RustT (SourceM n KemSK source Platform))]
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (generator : rand_core.TryCryptoRng R Error) (view : AdapterPublicWrapperState.MaterialView source KemSK)
variable (kem : AdapterBeaconConstructorKem.Representation view R)
variable (leaves : AdapterBeaconConstructorNative.Leaves (n:=n) (Auxiliary:=RegistrationServerRoleBackend.State)
  coins setup checks representation created generator view kem)
variable (views : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential source)
variable (parsing : RegistrationNativePlatformPublicAdapterPinParsing.EdContract view)

omit material platform ed generators crypto children in
private theorem closed_pure {A : Type} (value : A) (before : RegistrationNativeExperiment.State n KemSK source) :
    (RegistrationNativePlatformExtractedSdkCreate.close (pure value : SourceM n KemSK source Platform A)).run before=pure (value,before) := by
  simp only [RegistrationNativePlatformExtractedSdkCreate.close,StateT.run,pure_apply,map_pure]
  unfold RegistrationNativeFinishTerminalTree.assemble
  rw [RegistrationWorldAgreementCompiler.join_erase]

noncomputable def command (keyId : U64) (identityKey mlKey : Slice U8)
    (current : RegistrationNativeExperiment.State n KemSK source ×Platform) :
    ProbComp (Option Nat ×(RegistrationNativeExperiment.State n KemSK source ×Platform)) :=
  match PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice identityKey),
    RegistrationNativeWire.parseMldsaPin (TranscriptAuthParts.absSlice mlKey) with
  | some identity,some ml=>Prod.map RegistrationNativeRawAdapter.resultOption id <$>
      (RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
        (((RegistrationNativePlatformExperiment.liftNative coins
          (RegistrationNativeExperiment.beacon setup checks representation created
            (RegistrationNativeBeaconFrontend.create setup source identity ml keyId))).run current.1).run current.2))
  | _,_=>pure (none,current)

noncomputable def refused (keyId : U64) (identityKey mlKey : Slice U8)
    (current : RegistrationNativeExperiment.State n KemSK source ×Platform)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (invalid : PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice identityKey)=none ∨
      RegistrationNativeWire.parseMldsaPin (TranscriptAuthParts.absSlice mlKey)=none) :
    TotalStep (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
      (pure ((none : Option Nat),current)) := {
  step:={
    Packet:=Unit
    sample:=pure ()
    sourceType:=AdapterBeaconConstructorBody.Outcome R
    sourceReply:=fun _=>.ok (.Err (),before.base.objects.rng)
    sourceState:=fun _=>before.base.objects.snapshot.committed
    sourceCall:=RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
      (((RegistrationNativePlatformExtractedSdkCreate.close
        (beaconcrypt_constructor_request.beacon.Beacon.try_new_with_rng (m:=RustT (SourceM n KemSK source Platform)) generator
          keyId identityKey mlKey before.base.objects.rng).run).run before.base.objects.snapshot.committed.1).run before.base.objects.snapshot.committed.2)
    source_exact:=by
      rw [RegistrationNativePlatformPublicAdapterPinParsing.rejected view parsing generator keyId identityKey mlKey before.base.objects.rng invalid]
      change (pure (RustM.ok ((.Err (),before.base.objects.rng) : AdapterBeaconConstructorBody.Outcome R),before.base.objects.snapshot.committed) :
        ProbComp (RustM (AdapterBeaconConstructorBody.Outcome R) ×(RegistrationNativeExperiment.State n KemSK source ×Platform)))=_
      rw [RustT.run_pure,closed_pure,StateT.run_pure,map_pure]
      rfl
    native:=fun _=>(none,current)
    native_exact:=rfl
    store:=fun _ _=>before }
  observe:=fun _=>none
  normal:=fun _ _=>⟨_,rfl⟩
  reply:=fun _ _ _ _=>rfl }

noncomputable def step (keyId : U64) (identityKey mlKey : Slice U8)
    (current : RegistrationNativeExperiment.State n KemSK source ×Platform)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current) :
    TotalStep (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
      (command coins setup checks representation created keyId identityKey mlKey current) := by
  cases identity:PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice identityKey) with
  | none=>
    rw [command,identity]
    exact refused setup created generator view views credential parsing keyId identityKey mlKey current before (.inl identity)
  | some identityBytes=>
    cases ml:RegistrationNativeWire.parseMldsaPin (TranscriptAuthParts.absSlice mlKey) with
    | none=>
      rw [command,identity,ml]
      exact refused setup created generator view views credential parsing keyId identityKey mlKey current before (.inr ml)
    | some mlBytes=>
      rw [command,identity,ml]
      have call:=RegistrationNativePlatformSdkStrongCreateStep.total coins setup checks representation created generator view kem leaves views credential
        keyId (parsing.object identityBytes) mlBytes identityKey mlKey
        (RegistrationNativePlatformPublicAdapterPinParsing.ed_decoded view parsing identityKey identityBytes identity)
        (RegistrationNativePlatformPublicAdapterPinParsing.ml_decoded mlKey mlBytes ml)
        current.1 current.2 before
      have mapped:=RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption call
      simp only [parsing.publicBytes] at mapped
      exact mapped

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateDispatch
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateDispatch.refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateDispatch.refused
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateDispatch.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateDispatch.step
