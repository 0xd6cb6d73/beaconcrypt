-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptStore
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterGetterLifts
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReply
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerStoreObjects
/-! The complete supported acceptance factory's physical marginal uses only the actual source result and observed backend. The actual returned SDK token determines the public handle; the whole continuation store is derived internally. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPhysical
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerReservationNative (project AllocationReply)
open BeaconcryptCore.Computational
private theorem source_eq {N Reply T : Type} {Private : N→Type} {model : ProbComp (Reply×N)}
    (call : RegistrationNativePlatformExtractedSdkPublic.TotalStep Private model)
    (first : {packet //packet∈support call.step.sample}→T)
    (update : RustM call.step.sourceType×N→T)
    (retained : ∀packet,first packet=update (call.step.sourceReply packet.val,call.step.sourceState packet.val)) :
    first <$>PFunctor.FreeM.attachSupp call.step.sample=update <$>call.step.sourceCall :=by
  rw [←call.step.source_exact,Functor.map_map]
  have erased:=congrArg (fun work=>(fun packet=>update (call.step.sourceReply packet,call.step.sourceState packet)) <$>work)
    (RegistrationNativePlatformExtractedSdkAdaptive.attached_erase call.step.sample)
  simp only [Functor.map_map] at erased
  rw [←erased]
  congr 1
  funext packet
  exact retained packet

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n : Nat} {KemSK I Reader Response PlatformState : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable [original : CryptoOperations (RustT ProbComp)]
local notation "NativeM" => RegistrationNativePlatformExperiment.M n KemSK mlSource (StateT PlatformState ProbComp)
attribute [local irreducible] RegistrationAuthenticationExecutor.begin
variable [originalLocal : LocalOperations (RustT (StateT PlatformState ProbComp))]
variable [originalContainers : ContainerOperations (RustT (StateT PlatformState ProbComp))]
local instance nativeLocal : LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp))) :=
  RegistrationNativePlatformPublicAdapterLeaves.localOperations originalLocal
local instance nativeContainers : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp))) :=
  RegistrationNativePlatformPublicAdapterLeaves.containerOperations originalContainers


local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource


theorem query {E R Error : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (checks : PqxdhServerAuthExperiment.Checks) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify) (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec NativeM)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM)
    (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (joint : PqxdhJointIdentity.Primitives)
    (model : AdapterPublicAgreementPrimitiveModel.Model (m := ProbComp) generator setup checks view)
    (entropy : AdapterPublicAgreementServerNative.Entropy model)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : Native×PlatformState)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential current)
    (input : Slice U8)
    (edGetter : ∀ key, (@CryptoOperations.edPublicBytes material ed (RustT NativeM)
      (AdapterPublicAgreementNativePlatformInterpreter.operations coins original) key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (originalLocal.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
    (membershipOperation : ∀ identifier, AdapterPublicServerReplayPrefix.contains
      (m := StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp))
      before.objects.server.consumed_registrations identifier = pure (views.replay before.objects.server.consumed_registrations identifier))
    (allocated : (StateT PlatformState ProbComp) AllocationReply)
    (allocationOperation : (AdapterPublicServerAcceptBody.setReserve
      (m := StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)) before.objects.server.consumed_registrations).run =
        RustM.ok <$> StateT.lift allocated)
    (footprint : ∀ previous reply next, (reply, next) ∈ support (allocated.run previous) →
      AdapterPublicWrapperStorage.ReplayReserve views before.objects.server.consumed_registrations reply)
    (insertion : ∀ history, AdapterPublicServerAgreementRetention.Standard (n := n) (KemSK := KemSK)
      (mlSource := mlSource) (m := (StateT PlatformState ProbComp)) views {before.objects.server with consumed_registrations := history}) :
    let getterNative:=RegistrationNativePlatformPublicAdapterGetterLifts.mldsa (n:=n) view mlGetter
    let call:=RegistrationNativePlatformSdkServerSteps.accept coins setup codec checks route verify edLaws recording writer generator view views joint model entropy created credential current before input edGetter getterNative membershipOperation allocated allocationOperation footprint insertion
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      (RegistrationNativePlatformSdkOrdinaryBeaconSelected.basePhysical view views joint created credential)
      (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption call)=
      RegistrationNativePlatformPublicAdapterAcceptStore.run originalContainers coins setup checks verify model.representation created
        generator view views input (RegistrationNativePlatformPublicAdapterStore.erase before.objects) :=by
  let getterNative:=RegistrationNativePlatformPublicAdapterGetterLifts.mldsa (n:=n) view mlGetter
  let call:=RegistrationNativePlatformSdkServerSteps.accept coins setup codec checks route verify edLaws recording writer generator view views joint model entropy created credential current before input edGetter getterNative membershipOperation allocated allocationOperation footprint insertion
  have attached : RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      (RegistrationNativePlatformSdkOrdinaryBeaconSelected.basePhysical view views joint created credential)
      (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption call)=
      RegistrationNativePlatformPublicAdapterAcceptStore.observed view views
        (RegistrationNativePlatformPublicAdapterStore.erase before.objects) <$>call.step.sourceCall :=by
    unfold RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
    apply source_eq call
    intro packet
    have kept:=RegistrationNativePlatformSdkServerStoreObjects.accept_objects coins setup codec checks route verify edLaws recording writer generator view views joint model entropy created credential current before input edGetter getterNative membershipOperation allocated allocationOperation footprint insertion packet
    have marked:=RegistrationNativePlatformExtractedSdkPublic.returned_exact call packet
    change (RustM.ok (RegistrationNativePlatformPublicAdapterAcceptStore.handle before.objects.nextSession
        (RegistrationNativePlatformExtractedSdkPublic.returned call packet).2,
        RegistrationNativePlatformPublicAdapterStore.erase
          (RegistrationNativePlatformExtractedSdkPublic.store call packet).objects),
      (RegistrationNativePlatformPublicAdapterStore.erase
        (RegistrationNativePlatformExtractedSdkPublic.store call packet).objects).backend)=_
    rw [kept,RegistrationNativePlatformPublicAdapterStore.accept_update,
      RegistrationNativePlatformPublicAdapterAccept.snapshot_source]
    unfold RegistrationNativePlatformPublicAdapterAcceptStore.observed
    rw [marked]
    rfl
  exact attached.trans (RegistrationNativePlatformPublicAdapterAcceptStore.source originalContainers coins setup checks verify model.representation created originalLocal
    generator codec route edLaws recording writer view views credential current
    (RegistrationNativePlatformPublicAdapterStore.erase before.objects) before.server before.backend input edGetter mlGetter)

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPhysical
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPhysical.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPhysical.query
