-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredCreateTyped
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredCreate
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLift
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditModel
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildModel
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInterface
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedCreate
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n :Nat} {I KemSK P E R Error S A :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitives :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [PublicWrapperPlatform.CryptoOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto :CryptoOperations (RustT ProbComp)]
variable [originalLocal :LocalOperations (RustT (StateT P ProbComp))]
variable [originalContainers :ContainerOperations (RustT (StateT P ProbComp))]
variable {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
variable (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
open RegistrationNativePlatformPublicAdapterDispatcherCore (Private model physical children raw_cast)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
open RegistrationNativePlatformSdkOrdinaryBeaconSelected (raw)
local notation "wire"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire
local notation "codec"=>RegistrationNativeWire.ledgerCodec wire
local notation "allocation"=>RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin
local notation "helper"=>RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer configuration.reservePackets
variable (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)local notation "auditPrivate"=>RegistrationNativePlatformPublicAdapterAuditModel.Private configuration created credential
local notation "auditModel"=>RegistrationNativePlatformPublicAdapterAuditModel.model configuration created credential
local notation "auditPhysical"=>RegistrationNativePlatformPublicAdapterAuditModel.physical configuration created credential

open RegistrationNativePlatformPublicAdapterCreatePhysical (Valid)

omit material platform ed primitives [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  [FrameDispatchFallback.Operations] originalGenerators originalCrypto in
private theorem invalid (identityKey mlKey :Slice U8) (bad :¬Valid identityKey mlKey) :
    PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice identityKey)=none ∨
      RegistrationNativeWire.parseMldsaPin (TranscriptAuthParts.absSlice mlKey)=none :=by
  cases ed:PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice identityKey) with
  | none=>exact Or.inl rfl
  | some edBytes=>
    cases ml:RegistrationNativeWire.parseMldsaPin (TranscriptAuthParts.absSlice mlKey) with
    | none=>exact Or.inr rfl
    | some mlBytes=>exact False.elim (bad ⟨edBytes,mlBytes,ed,ml⟩)

omit primitives [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  [FrameDispatchFallback.Operations] originalGenerators originalCrypto originalLocal originalContainers in
private theorem raw_map_cast {N A B :Type} {Private :N→Type} {left right :ProbComp (A×N)}
    (same :left=right) (call :TotalStep Private left) (observe :A→B)
    (project :∀current,Private current→RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P) :
    raw project (RegistrationNativePlatformPublicAdapterReply.map observe
      (RegistrationNativePlatformPublicAdapterBuildRaw.modelCast same call))=
      raw project (RegistrationNativePlatformPublicAdapterReply.map observe call) :=rfl

omit primitives [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  [FrameDispatchFallback.Operations] originalGenerators originalCrypto originalLocal originalContainers in
private theorem raw_normalized {N :Type} {Private :N→Type} {target :ProbComp (Option Nat×N)}
    (project :∀current,Private current→RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P)
    (call :TotalStep Private target) :
    raw (fun current stored=>RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize (project current stored)) call=
      RegistrationNativePlatformPublicAdapterCreateNormalized.result <$>raw project call :=by
  unfold raw
  calc
    _=(fun packet=>RegistrationNativePlatformPublicAdapterCreateNormalized.result
      (RustM.ok (call.observe (RegistrationNativePlatformExtractedSdkPublic.returned call packet),
        project (call.step.native packet.val).2 (RegistrationNativePlatformExtractedSdkPublic.store call packet)),
        (project (call.step.native packet.val).2 (RegistrationNativePlatformExtractedSdkPublic.store call packet)).backend)) <$>
      PFunctor.FreeM.attachSupp call.step.sample :=rfl
    _=_:=(Functor.map_map _ _ _).symm

noncomputable def active (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before)
    (keyId :U64) (identityKey mlKey :Slice U8) (edBytes :Std.Array U8 32#usize) (mlBytes :Std.Array U8 1952#usize)
    (edParsed :PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice identityKey)=some edBytes)
    (mlParsed :RegistrationNativeWire.parseMldsaPin (TranscriptAuthParts.absSlice mlKey)=some mlBytes) :
    TotalStep auditPrivate ((auditModel (.inr (.create identityKey mlKey keyId))).run before) :=by
  have shape:RegistrationNativePlatformPublicAdapterTypedAuditRaw.form RegistrationNativeConcreteCodec.wire
      (.inr (.create (TranscriptAuthParts.absSlice identityKey) (TranscriptAuthParts.absSlice mlKey) keyId))=
      .query (.inr (.create edBytes mlBytes keyId)) RegistrationNativeRawAdapter.resultOption :=by
    simp only [RegistrationNativePlatformPublicAdapterTypedAuditRaw.form,edParsed,mlParsed]
  refine RegistrationNativePlatformPublicAdapterAuditLift.selected configuration created credential
    (.inr (.create (TranscriptAuthParts.absSlice identityKey) (TranscriptAuthParts.absSlice mlKey) keyId))
    (.inr (.create edBytes mlBytes keyId)) RegistrationNativeRawAdapter.resultOption shape before.1 before.2 ?_
  refine RegistrationNativePlatformPublicAdapterBuildRaw.modelCast ?_
    (RegistrationNativePlatformPublicAdapterConfiguredCreateTyped.step configuration created credential before.1 stored keyId
      (configuration.pins.object edBytes) mlBytes identityKey mlKey
      (RegistrationNativePlatformPublicAdapterPinParsing.ed_decoded configuration.view configuration.pins identityKey edBytes edParsed)
      (RegistrationNativePlatformPublicAdapterPinParsing.ml_decoded mlKey mlBytes mlParsed))
  rw [configuration.pins.publicBytes]

omit [PublicWrapperPlatform.CryptoOperations] in
theorem active_query (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before)
    (keyId :U64) (identityKey mlKey :Slice U8) (edBytes :Std.Array U8 32#usize) (mlBytes :Std.Array U8 1952#usize)
    (edParsed :PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice identityKey)=some edBytes)
    (mlParsed :RegistrationNativeWire.parseMldsaPin (TranscriptAuthParts.absSlice mlKey)=some mlBytes) :
    raw auditPhysical (active configuration created credential before stored keyId identityKey mlKey edBytes mlBytes edParsed mlParsed)=
      RegistrationNativePlatformPublicAdapterCreateNormalized.source coins setup checks configuration.agreement.representation created configuration.view children
        configuration.generator keyId identityKey mlKey (auditPhysical before stored) :=by
  unfold active
  rw [RegistrationNativePlatformPublicAdapterAuditLift.selected_physical]
  rw [raw_map_cast]
  unfold RegistrationNativePlatformPublicAdapterConfiguredCreateTyped.step
  rw [raw_map_cast,RegistrationNativePlatformPublicAdapterConfiguredCreateTyped.mapped]
  have sourceLaw:=RegistrationNativePlatformPublicAdapterCreatePhysical.active_physical coins setup checks configuration.agreement.representation created configuration.view children children
    configuration.generator configuration.kem configuration.mlGeneration configuration.edGeneration configuration.prekeyGeneration configuration.kemGeneration
    configuration.views credential keyId (configuration.pins.object edBytes) mlBytes identityKey mlKey
      (RegistrationNativePlatformPublicAdapterPinParsing.ed_decoded configuration.view configuration.pins identityKey edBytes edParsed)
      (RegistrationNativePlatformPublicAdapterPinParsing.ml_decoded mlKey mlBytes mlParsed) before.1 stored
  have projected:=congrArg (fun work=>RegistrationNativePlatformPublicAdapterCreateNormalized.result <$>work) sourceLaw
  refine Eq.trans ?_ (projected.trans ?_)
  · exact raw_normalized
      (RegistrationNativePlatformSdkOrdinaryBeaconSelected.strongPhysical setup configuration.view configuration.views created credential) _
  · exact RegistrationNativePlatformPublicAdapterCreateNormalized.stable coins setup checks configuration.agreement.representation created configuration.view children
      configuration.generator configuration.kem configuration.mlGeneration configuration.edGeneration configuration.prekeyGeneration configuration.kemGeneration
      keyId identityKey mlKey (RegistrationNativePlatformPublicAdapterStore.erase stored.base.objects)

noncomputable def step (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before)
    (identityKey mlKey :Slice U8) (keyId :U64) :TotalStep auditPrivate ((auditModel (.inr (.create identityKey mlKey keyId))).run before) :=by
  classical
  exact if valid:Valid identityKey mlKey then
    active configuration created credential before stored keyId identityKey mlKey (Classical.choose valid) (Classical.choose (Classical.choose_spec valid))
      (Classical.choose_spec (Classical.choose_spec valid)).1 (Classical.choose_spec (Classical.choose_spec valid)).2
  else
    RegistrationNativePlatformPublicAdapterAuditLift.silenced configuration created credential
      (.inr (.create (TranscriptAuthParts.absSlice identityKey) (TranscriptAuthParts.absSlice mlKey) keyId)) none
      (RegistrationNativePlatformPublicAdapterTypedAuditRaw.create_malformed RegistrationNativeConcreteCodec.wire
        (TranscriptAuthParts.absSlice identityKey) (TranscriptAuthParts.absSlice mlKey) keyId (invalid identityKey mlKey valid))
      before.1 before.2 (RegistrationNativePlatformPublicAdapterConfiguredCreate.step configuration created credential before.1 stored identityKey mlKey keyId)

omit [PublicWrapperPlatform.CryptoOperations] in
theorem query (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before)
    (identityKey mlKey :Slice U8) (keyId :U64) :
    raw auditPhysical (step configuration created credential before stored identityKey mlKey keyId)=
      RegistrationNativePlatformPublicAdapterCreateNormalized.source coins setup checks configuration.agreement.representation created configuration.view children
        configuration.generator keyId identityKey mlKey (auditPhysical before stored) :=by
  classical
  by_cases valid:Valid identityKey mlKey
  · simp only [step,dite_eq_left valid]
    exact active_query configuration created credential before stored keyId identityKey mlKey _ _ _ _
  · simp only [step,dite_eq_right valid]
    exact (RegistrationNativePlatformPublicAdapterAuditLift.silenced_physical configuration created credential _ _ _ before.1 before.2 _).trans
      (RegistrationNativePlatformPublicAdapterConfiguredCreate.query configuration created credential before.1 stored identityKey mlKey keyId)

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedCreate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedCreate.active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedCreate.active

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedCreate.active_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedCreate.active_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedCreate.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedCreate.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedCreate.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedCreate.query
