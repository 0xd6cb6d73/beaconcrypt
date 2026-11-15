-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcherCore
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredAccept
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLift
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedAccept
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n :Nat} {I KemSK P E R Error :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitives :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto :CryptoOperations (RustT ProbComp)]
variable [originalLocal :LocalOperations (RustT (StateT P ProbComp))]
variable [originalContainers :ContainerOperations (RustT (StateT P ProbComp))]
variable {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
variable (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
local notation "codec"=>RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire)
local notation "route"=>RegistrationNativePlatformPublicAdapterRouting.route
variable (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential source)
variable (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source)
variable (stored :RegistrationNativePlatformPublicAdapterAuditModel.Private configuration created credential before)
variable (input :Slice U8)

omit [PublicWrapperPlatform.CryptoOperations] in
theorem validTarget (packet :registration.InitPacket)
    (decoded :RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input)=some packet) :
    RegistrationNativePlatformPackedState.pack
      (RegistrationNativePlatformExtractedSdkServer.Accept.native coins setup codec checks
        (AdapterPublicServerSourceLens.admitted <$>configuration.replayAllocate stored.base.objects.server.consumed_registrations)
        route source.verify configuration.agreement.representation created input) before.1=
      ((RegistrationNativePlatformPublicAdapterAuditModel.typed configuration created credential (.inr (.accept packet))).run before.1) :=by
  have admission :AdapterPublicServerSourceLens.admitted <$>configuration.replayAllocate stored.base.objects.server.consumed_registrations=
    configuration.reserveRegistration:=configuration.replayAdmission _
  rw [admission]
  unfold RegistrationNativePlatformExtractedSdkServer.Accept.native
  rw [decoded]
  unfold RegistrationNativePlatformPublicAdapterAuditModel.typed RegistrationNativePlatformPublicAdapterRawModel.typed
  rfl

omit [PublicWrapperPlatform.CryptoOperations] in
noncomputable def valid (packet :registration.InitPacket)
    (decoded :RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input)=some packet) :=
  RegistrationNativePlatformPublicAdapterAuditLift.selected configuration created credential
    (.inr (.accept (TranscriptAuthParts.absSlice input))) (.inr (.accept packet)) RegistrationNativeRawAdapter.resultOption
    (by simp only [RegistrationNativePlatformPublicAdapterTypedAuditRaw.form,RegistrationNativeConcreteReaders.init,decoded])
    before.1 before.2
    (RegistrationNativePlatformPublicAdapterBuildRaw.modelCast (validTarget configuration created credential before stored input packet decoded)
      (RegistrationNativePlatformPublicAdapterConfiguredAccept.typedStep configuration created credential before.1 stored input))

omit [PublicWrapperPlatform.CryptoOperations] in
noncomputable def invalid (decoded :RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input)=none) :=
  RegistrationNativePlatformPublicAdapterAuditLift.silenced configuration created credential
    (.inr (.accept (TranscriptAuthParts.absSlice input))) none
    (by simp only [RegistrationNativePlatformPublicAdapterTypedAuditRaw.form,RegistrationNativeConcreteReaders.init,decoded])
    before.1 before.2
    (RegistrationNativePlatformPublicAdapterConfiguredAccept.step configuration created credential before.1 stored input)

omit [PublicWrapperPlatform.CryptoOperations] in
noncomputable def step :RegistrationNativePlatformExtractedSdkPublic.TotalStep
    (RegistrationNativePlatformPublicAdapterAuditModel.Private configuration created credential)
    (((RegistrationNativePlatformPublicAdapterAuditModel.model configuration created credential (.inr (.accept input))).run before)) :=
  match decoded:RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none=>invalid configuration created credential before stored input decoded
  | some packet=>valid configuration created credential before stored input packet decoded

attribute [local irreducible] RegistrationNativePlatformPublicAdapterAuditModel.typed

omit [PublicWrapperPlatform.CryptoOperations] in
theorem valid_query (packet :registration.InitPacket)
    (decoded :RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input)=some packet) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      (RegistrationNativePlatformPublicAdapterAuditModel.physical configuration created credential)
      (valid configuration created credential before stored input packet decoded)=
      RegistrationNativePlatformPublicAdapterConfiguredAccept.sourceOperation configuration created
        (RegistrationNativePlatformPublicAdapterAuditModel.physical configuration created credential before stored) input :=by
  unfold valid
  rw [RegistrationNativePlatformPublicAdapterAuditLift.selected_physical]
  change RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
    (RegistrationNativePlatformPublicAdapterDispatcherCore.physical configuration created credential)
    (RegistrationNativePlatformPublicAdapterConfiguredAccept.step configuration created credential before.1 stored input)=_
  exact RegistrationNativePlatformPublicAdapterConfiguredAccept.query configuration created credential before.1 stored input

omit [PublicWrapperPlatform.CryptoOperations] in
theorem invalid_query (decoded :RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input)=none) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      (RegistrationNativePlatformPublicAdapterAuditModel.physical configuration created credential)
      (invalid configuration created credential before stored input decoded)=
      RegistrationNativePlatformPublicAdapterConfiguredAccept.sourceOperation configuration created
        (RegistrationNativePlatformPublicAdapterAuditModel.physical configuration created credential before stored) input :=by
  unfold invalid
  rw [RegistrationNativePlatformPublicAdapterAuditLift.silenced_physical]
  exact RegistrationNativePlatformPublicAdapterConfiguredAccept.query configuration created credential before.1 stored input

omit [PublicWrapperPlatform.CryptoOperations] in
theorem query :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      (RegistrationNativePlatformPublicAdapterAuditModel.physical configuration created credential)
      (step configuration created credential before stored input)=
      RegistrationNativePlatformPublicAdapterConfiguredAccept.sourceOperation configuration created
        (RegistrationNativePlatformPublicAdapterAuditModel.physical configuration created credential before stored) input :=by
  unfold step
  split
  · exact invalid_query configuration created credential before stored input _
  · exact valid_query configuration created credential before stored input _ _

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedAccept
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedAccept.validTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedAccept.validTarget
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedAccept.valid_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedAccept.valid_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedAccept.invalid_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedAccept.invalid_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedAccept.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedAccept.query
