-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildSupportedPublic
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkBuildReification
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkBuildSessions
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierServer
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildNormal
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
/-! The concrete reached SDK builder obtains its public response directly from the same normal source return. Its continuation retains the actual supported raw receipt and complete source/platform poststate. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerBuildStep
open BeaconcryptCore.Refinement
open BeaconcryptCore.Computational
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperState AdapterPublicWrapperStorage
open AdapterPublicServerBuildBody (Server Reply)
variable {n : Nat} {KemSK Platform E I Reader Response : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
local notation "Cut" => RegistrationNativePlatformCutJournal.State Native
local notation "Base" => StateT Platform ProbComp
local notation "NativeM" => StateT Native Base
local notation "SourceM" => StateT Cut Base
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [primitive : AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
  (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]

variable [localOps : LocalOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
  (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]
variable [crypto : CryptoOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
  (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]
open AdapterPublicServerBuildPrefix (completion finish admitted project application AllocationReply reserveNative)

omit localOps in
noncomputable def complete {R : Type}
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView)
(converted : RegistrationNativePlatformOrdinarySourceNative.Conversion keyView) (failure : primitive.Error)
(allocate : alloc.vec.Vec U8→Usize→Base (core.result.Result Unit E))
(reserveFrame : Nat→Base (core.result.Result Unit E))
(erased : commitment.CommitmentTranscript)
(sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
(reservePackets : Usize→Base (core.result.Result Unit E))
(fallback : registration.MldsaSigningRequest → NativeM RegistrationSigningShared.SignReply)

    (previousLocal : LocalOperations (RustT SourceM))
    (previousChildren : ChildOperations (RustT SourceM))
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (joint : PqxdhJointIdentity.Primitives) (current : Native×Platform)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential current)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (data : core.option.Option (Slice U8))
    (parsed : AdapterPublicServerToken.ParsedToken token)
    (edGetter : ∀ key, (crypto.edPublicBytes key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (previousLocal.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
    (allocated : Base AllocationReply)
    (reserveOperation : (containers.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
      beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
      hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator before.objects.server.known_ids 1#usize).run =
        RustM.ok <$> StateT.lift allocated)
    (footprint : ∀ external reply next, (reply, next) ∈ support (allocated.run external) → PeerReserve views before.objects.server.known_ids reply)
    (containsOperation : ∀ (current : Cut),
      AdapterPublicWrapperState.Server view views created credential before.objects.server current.1.server →
      ∀ identifier,
      ((containers.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
        beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
        hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
        core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
          (core.borrow.Borrow.Blanket U64)) before.objects.server.known_ids identifier).run).run current =
      pure (.ok (views.peer before.objects.server.known_ids identifier).isSome,
        ({current.1 with server := AdapterPublicServerPresenceNative.charged current.1.server identifier}, current.2)))
    (standard : ∀ known publication inserting publicKey,
      peer.begin_peer_insert before.objects.server.control publication = .ok (.Ok inserting) →
      beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes inserting.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey) →
      AdapterPublicServerInstallFunctional.Standard (m := SourceM) views {before.objects.server with known_ids := known} inserting publicKey)
 :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential)
      (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExperiment.server
          (RegistrationNativePlatformCompletionSdk.complete (RegistrationNativePlatformSourceBuild.pin coins)
            (admitted <$>StateT.lift allocated) (RegistrationNativePlatformCompletionSdk.nativePresent coins)
            (RegistrationNativePlatformExtractedSdkServer.Build.sourceFinish coins setup codec keyView failure
              (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate)
              (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased sign
              (RegistrationNativePlatformConcreteSource.writer reservePackets)) token.registration (application data))) current) := by
  let sourceBefore : Cut:=(current.1,none)
  let Private : Native×Platform→Type:=RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential
  apply RegistrationNativePlatformExtractedSdkBuildSupportedPublic.step coins setup codec keyView converted failure
    allocate reserveFrame erased sign reservePackets fallback previousLocal previousChildren view views created credential
    before.objects.server sourceBefore before.server token data parsed edGetter mlGetter allocated reserveOperation footprint containsOperation standard current.2 Private
  intro publication reply self rawAfter platformAfter supported returned
  let witness:=RegistrationNativePlatformExtractedSdkAdaptiveServerSupported.Build.step coins setup codec keyView failure
    (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate) (RegistrationNativePlatformConcreteSource.helper reserveFrame)
    erased sign (RegistrationNativePlatformConcreteSource.writer reservePackets) fallback previousLocal previousChildren
    view views created credential before.objects.server sourceBefore before.server token data parsed edGetter mlGetter
    allocated reserveOperation footprint containsOperation standard current.2 (fun _=>PUnit)
    (fun _ _ _ _ _ _ _=>PUnit.unit)
  have reached:=RegistrationNativePlatformSdkBeaconFrame.step_support witness (((publication,.ok (reply,self)),rawAfter),platformAfter) supported
  change (let result:=project before.objects.server.control ((publication,.ok (reply,self)),rawAfter);
    (result.1,(result.2,platformAfter)))∈support _ at reached
  let after:=(project before.objects.server.control ((publication,.ok (reply,self)),rawAfter)).2
  have actual : (((project before.objects.server.control ((publication,.ok (reply,self)),rawAfter)).1,after),platformAfter)∈support
      (((RegistrationNativePlatformExperiment.server
          (RegistrationNativePlatformCompletionSdk.complete (RegistrationNativePlatformSourceBuild.pin coins)
            (admitted <$>StateT.lift allocated) (RegistrationNativePlatformCompletionSdk.nativePresent coins)
            (RegistrationNativePlatformExtractedSdkServer.Build.sourceFinish coins setup codec keyView failure
              (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate)
              (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased sign
              (RegistrationNativePlatformConcreteSource.writer reservePackets)) token.registration (application data))).run current.1).run current.2) := by
    rw [RegistrationNativePlatformPackedState.pack,support_map] at reached
    obtain ⟨⟨⟨actualReply,actualAfter⟩,next⟩,called,equal⟩:=reached
    simp only [Prod.mk.injEq] at equal
    obtain ⟨replyEq,afterEq,platformEq⟩:=equal
    cases replyEq
    cases afterEq
    cases platformEq
    exact called
  have reserveMap : (admitted <$>StateT.lift allocated : StateT (RegistrationServerFrontendCompiler.State n) Base Bool)=StateT.lift (admitted <$>allocated) := by
    apply StateT.ext
    intro server
    simp only [StateT.run_map,StateT.run_lift,map_bind,bind_map_left,map_pure]

  have sessionsActual:=actual
  rw [reserveMap] at sessionsActual
  have sessions:=RegistrationNativePlatformSdkBuildSessions.native_complete coins (admitted <$>allocated)
    (RegistrationNativePlatformExtractedSdkServer.Build.sourceFinish coins setup codec keyView failure
      (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate)
      (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased sign
      (RegistrationNativePlatformConcreteSource.writer reservePackets)) token.registration (application data) current.1 current.2 _ sessionsActual
  have frame:=RegistrationNativePlatformSdkBeaconFrame.complete coins setup codec keyView failure
    (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate) (RegistrationNativePlatformConcreteSource.helper reserveFrame)
    erased sign (RegistrationNativePlatformConcreteSource.writer reservePackets) allocated admitted token.registration (application data) current.1 current.2 _ actual
  have backend:=RegistrationNativePlatformSdkBuildReification.projected view views created credential before.objects.server.control publication (reply,self) rawAfter returned platformAfter
  exact RegistrationNativePlatformExtractedSdkCarrierServer.buildPut view views joint created credential current before self after platformAfter
    returned sessions frame (RegistrationNativePlatformSdkServerReification.snapshot view views self none (rawAfter.1,platformAfter)) backend
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerBuildStep

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerBuildStep.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerBuildStep.complete
