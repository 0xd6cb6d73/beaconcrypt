-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRaw
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildModel
attribute [local irreducible] RegistrationNativePlatformPublicAdapterRawModel.raw RegistrationNativePlatformPublicAdapterRawModel.typed
  RegistrationNativePlatformExtractedExperiment.record RegistrationNativePlatformExtractedAuthentication.accept
  RegistrationNativePlatformExtractedBundle.bundle RegistrationNativePlatformExtractedFinish.finish
open BeaconcryptCore.Refinement
open AdapterPublicServerBuildPrefix (admitted AllocationReply)
variable {n :Nat} {I KemSK E P :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [PublicWrapperPlatform.Material] [PublicWrapperPlatform.Platform]
variable [primitive :AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations] [AdapterInitEdPrimitive.Operations]
local notation "Base"=>StateT P ProbComp
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins

omit [PublicWrapperPlatform.Material] in
theorem typed (setup :PqxdhServerAuthExperiment.Setup base KemSK) (checks :PqxdhServerAuthExperiment.Checks)
    (representation :RegistrationServerRoleBackend.ConvertedIdentity setup) (created :PqxdhLiveServerConstruction.Created Unit)
    (credential :RegistrationNativeMldsa.Credential source) (view :RegistrationNativePlatformSourceSeal.KeyView)
    (failure :primitive.Error) (allocate :alloc.vec.Vec U8 →Usize →Base (core.result.Result Unit E))
    (reserveRegistration :Base Bool) (allocated :Base AllocationReply)
    (reserveFrame :Nat →Base (core.result.Result Unit E)) (erased :commitment.CommitmentTranscript)
    (reservePackets :Usize →Base (core.result.Result Unit E)) (handle :Nat) (payload :Option Pqxdh.Bytes)
 :
    RegistrationNativePlatformPublicAdapterRawModel.typed (n:=n) (Platform:=P) (source:=source) setup checks representation created credential view failure
        (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate) reserveRegistration (admitted <$>allocated)
        reserveFrame erased (RegistrationNativePlatformConcreteSource.helper reserveFrame)
        (RegistrationNativePlatformConcreteSource.writer reservePackets) (.inr (.build handle (RegistrationNativeRawAdapter.application payload)))=
    (RegistrationNativePlatformPublicAdapterBuildRaw.bytes <$>
      RegistrationNativePlatformExperiment.server (n:=n) (source:=source)
        (RegistrationNativePlatformCompletionSdk.build (n:=n) (RegistrationNativePlatformSourceBuild.pin (n:=n) coins)
          (admitted <$>StateT.lift allocated) (RegistrationNativePlatformCompletionSdk.nativePresent (n:=n) coins)
          (RegistrationNativePlatformExtractedSdkServer.Build.sourceFinish (n:=n) coins setup
            (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire))
            view failure (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate)
            (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased (RegistrationNativeMldsa.owned source credential)
            (RegistrationNativePlatformConcreteSource.writer reservePackets)) handle (RegistrationNativeRawAdapter.application payload)) :
        StateT (RegistrationNativeExperiment.State n KemSK source) Base (RustM (Option (U64×Pqxdh.Bytes)))) :=by
  have reserveMap : (admitted <$>StateT.lift allocated :StateT (RegistrationServerFrontendCompiler.State n) Base Bool)=
      StateT.lift (admitted <$>allocated) :=by
    apply StateT.ext
    intro before
    simp only [StateT.run_map,StateT.run_lift,map_bind,bind_map_left,map_pure]
  rw [reserveMap]
  let codec:=RegistrationNativeWire.ledgerCodec
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire)
  have sourceSame :RegistrationNativePlatformExtractedSourceSeal.build (n:=n) coins setup codec view failure
      (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate) erased (admitted <$>allocated)
      (RegistrationNativeMldsa.owned source credential) (RegistrationNativePlatformConcreteSource.helper reserveFrame)
      (RegistrationNativePlatformConcreteSource.writer reservePackets) handle (RegistrationNativeRawAdapter.application payload)=
      RegistrationNativePlatformCompletionSdk.build (RegistrationNativePlatformSourceBuild.pin coins)
        (StateT.lift (admitted <$>allocated)) (RegistrationNativePlatformCompletionSdk.nativePresent coins)
        (RegistrationNativePlatformExtractedSdkServer.Build.sourceFinish coins setup codec view failure
          (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate)
          (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased (RegistrationNativeMldsa.owned source credential)
          (RegistrationNativePlatformConcreteSource.writer reservePackets)) handle (RegistrationNativeRawAdapter.application payload) :=rfl
  unfold RegistrationNativePlatformPublicAdapterRawModel.typed
  dsimp only [RegistrationNativePlatformExtractedExperiment.handler,RegistrationNativePlatformExtractedRegistration.handler]
  change RegistrationNativePlatformPublicAdapterBuildRaw.bytes <$>
      RegistrationNativePlatformExperiment.server (n:=n) (source:=source)
        (RegistrationNativePlatformExtractedSourceSeal.build coins setup codec view failure
          (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate) erased (admitted <$>allocated)
          (RegistrationNativeMldsa.owned source credential) (RegistrationNativePlatformConcreteSource.helper reserveFrame)
          (RegistrationNativePlatformConcreteSource.writer reservePackets) handle (RegistrationNativeRawAdapter.application payload))=_
  rw [sourceSame]

omit [PublicWrapperPlatform.Material] in
theorem raw (setup :PqxdhServerAuthExperiment.Setup base KemSK) (checks :PqxdhServerAuthExperiment.Checks)
    (representation :RegistrationServerRoleBackend.ConvertedIdentity setup) (created :PqxdhLiveServerConstruction.Created Unit)
    (credential :RegistrationNativeMldsa.Credential source) (view :RegistrationNativePlatformSourceSeal.KeyView)
    (failure :primitive.Error) (allocate :alloc.vec.Vec U8 →Usize →Base (core.result.Result Unit E))
    (reserveRegistration :Base Bool) (allocated :Base AllocationReply)
    (reserveFrame :Nat →Base (core.result.Result Unit E)) (erased :commitment.CommitmentTranscript)
    (reservePackets :Usize →Base (core.result.Result Unit E)) (handle :Nat) (payload :Option Pqxdh.Bytes)
 :
    RegistrationNativePlatformPublicAdapterRawModel.raw (n:=n) (Platform:=P) (source:=source) setup checks representation created credential view failure
        (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate) reserveRegistration (admitted <$>allocated)
        reserveFrame erased (RegistrationNativePlatformConcreteSource.helper reserveFrame)
        (RegistrationNativePlatformConcreteSource.writer reservePackets) (.inr (.build handle payload))=
    (RegistrationNativePlatformPublicAdapterBuildRaw.response <$>
      RegistrationNativePlatformExperiment.server (n:=n) (source:=source)
        (RegistrationNativePlatformCompletionSdk.build (n:=n) (RegistrationNativePlatformSourceBuild.pin (n:=n) coins)
          (admitted <$>StateT.lift allocated) (RegistrationNativePlatformCompletionSdk.nativePresent (n:=n) coins)
          (RegistrationNativePlatformExtractedSdkServer.Build.sourceFinish (n:=n) coins setup
            (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire))
            view failure (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate)
            (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased (RegistrationNativeMldsa.owned source credential)
            (RegistrationNativePlatformConcreteSource.writer reservePackets)) handle (RegistrationNativeRawAdapter.application payload)) :
        StateT (RegistrationNativeExperiment.State n KemSK source) Base (Option PqxdhServerRegistrationPublication.Response)) :=by
  rw [RegistrationNativePlatformPublicAdapterRawModel.build,typed setup checks representation created credential view failure allocate reserveRegistration allocated reserveFrame erased reservePackets handle payload,Functor.map_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildModel

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildModel.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildModel.raw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildModel.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildModel.typed
