-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcherCore
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalized
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredAccept
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
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
local notation "codec"=>RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire)
local notation "route"=>RegistrationNativePlatformPublicAdapterRouting.route
local instance nativeLocal :LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source) (StateT P ProbComp))):=
  RegistrationNativePlatformPublicAdapterLeaves.localOperations originalLocal
local instance nativeContainers :ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source) (StateT P ProbComp))):=
  RegistrationNativePlatformPublicAdapterLeaves.containerOperations originalContainers

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem membership (history :AdapterPublicWrapperStorage.ReplaySet) (identifier :Std.Array U8 64#usize) :
    AdapterPublicServerReplayPrefix.contains (m:=StateT Native (StateT P ProbComp)) history identifier=
      pure (configuration.views.replay history identifier) :=by
  change RegistrationNativePlatformPublicAdapterLeaves.lift
    (AdapterPublicServerReplayPrefix.contains (m:=StateT P ProbComp) history identifier)=_
  rw [configuration.replayMember]
  rfl

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem reservation (history :AdapterPublicWrapperStorage.ReplaySet) :
    (AdapterPublicServerAcceptBody.setReserve (m:=StateT Native (StateT P ProbComp)) history).run=
      RustM.ok <$>StateT.lift (configuration.replayAllocate history) :=by
  change StateT.lift (AdapterPublicServerAcceptBody.setReserve (m:=StateT P ProbComp) history).run=_
  rw [configuration.replayReserve]
  apply StateT.ext
  intro before
  simp only [StateT.run_lift,StateT.run_map,Functor.map_map,bind_pure_comp]

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem insertion (self :beaconcrypt_public_wrapper.server.Server) :
    AdapterPublicServerAgreementRetention.Standard (n:=n) (KemSK:=KemSK) (mlSource:=source) (m:=StateT P ProbComp)
      configuration.views self :=by
  constructor
  intro completed
  obtain ⟨result,operation,footprint⟩:=configuration.replayInsert self.consumed_registrations completed.pending.registration_id.bytes
  refine ⟨result,?_,footprint⟩
  change RegistrationNativePlatformPublicAdapterLeaves.lift
    (AdapterPublicServerAcceptBody.setInsert (m:=StateT P ProbComp) self.consumed_registrations completed.pending.registration_id.bytes)=_
  rw [operation]
  rfl

variable (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential source)
variable (current :RegistrationNativeExperiment.State n KemSK source×P)
variable (before :RegistrationNativePlatformPublicAdapterDispatcherCore.Private configuration created credential current)
variable (input :Slice U8)

omit [PublicWrapperPlatform.CryptoOperations] in
noncomputable def typedStep :=
  RegistrationNativePlatformSdkStrongServerSteps.accept (E:=E) coins setup codec checks route source.verify configuration.edFunctional
    RegistrationNativePlatformPublicAdapterDispatcherCore.recording
    (fun query=>StateT.lift (RegistrationNativePlatformConcreteSource.writer configuration.reservePackets query))
    configuration.generator configuration.view configuration.views configuration.agreement configuration.entropy created credential current before input
    (RegistrationNativePlatformPublicAdapterGetterLifts.ed_public coins configuration.view configuration.edGetter)
    (RegistrationNativePlatformPublicAdapterGetterLifts.mldsa configuration.view configuration.mlGetter)
    (membership configuration before.base.objects.server.consumed_registrations)
    (configuration.replayAllocate before.base.objects.server.consumed_registrations)
    (reservation configuration before.base.objects.server.consumed_registrations)
    (configuration.replayFootprint before.base.objects.server.consumed_registrations)
    (fun history=>insertion configuration {before.base.objects.server with consumed_registrations:=history})

omit [PublicWrapperPlatform.CryptoOperations] in
theorem target :
    (Prod.map RegistrationNativeRawAdapter.resultOption id <$>
      RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExtractedSdkServer.Accept.native coins setup codec checks
          (AdapterPublicServerSourceLens.admitted <$>configuration.replayAllocate before.base.objects.server.consumed_registrations)
          route source.verify configuration.agreement.representation created input) current)=
      ((RegistrationNativePlatformPublicAdapterDispatcherCore.model configuration created credential (.inr (.accept input))).run current) :=by
  have admission :AdapterPublicServerSourceLens.admitted <$>configuration.replayAllocate before.base.objects.server.consumed_registrations=
    configuration.reserveRegistration:=configuration.replayAdmission _
  rw [admission]
  change _=RegistrationNativePlatformExtractedSdkAdaptive.pack <$>
    (((RegistrationNativePlatformPublicAdapterDispatcherCore.native configuration created credential
      (.inr (.accept (TranscriptAuthParts.absSlice input)))).run current.1).run current.2)
  unfold RegistrationNativePlatformPublicAdapterDispatcherCore.native
  rw [RegistrationNativePlatformPublicAdapterRawModel.accept]
  simp only [RegistrationNativePlatformPackedState.pack,StateT.run_map,Functor.map_map]
  rfl

omit [PublicWrapperPlatform.CryptoOperations] in
noncomputable def step :RegistrationNativePlatformExtractedSdkPublic.TotalStep
    (RegistrationNativePlatformPublicAdapterDispatcherCore.Private configuration created credential)
    (((RegistrationNativePlatformPublicAdapterDispatcherCore.model configuration created credential (.inr (.accept input))).run current)) :=
  RegistrationNativePlatformPublicAdapterBuildRaw.modelCast (target configuration created credential current before input)
    (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption
      (typedStep configuration created credential current before input))

omit [PublicWrapperPlatform.CryptoOperations] in
noncomputable def sourceOperation (before :RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P) (input :Slice U8) :=
  RegistrationNativePlatformPublicAdapterAcceptStore.run originalContainers coins setup checks source.verify configuration.agreement.representation created
    configuration.generator configuration.view configuration.views input before

omit [PublicWrapperPlatform.CryptoOperations] in
theorem query :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      (RegistrationNativePlatformPublicAdapterDispatcherCore.physical configuration created credential)
      (step configuration created credential current before input)=
      sourceOperation configuration created
        (RegistrationNativePlatformPublicAdapterDispatcherCore.physical configuration created credential current before) input :=by
  rw [step,RegistrationNativePlatformPublicAdapterDispatcherCore.raw_cast]
  exact RegistrationNativePlatformPublicAdapterAcceptNormalized.query coins setup codec checks route source.verify configuration.edFunctional
    RegistrationNativePlatformPublicAdapterDispatcherCore.recording
    (fun query=>StateT.lift (RegistrationNativePlatformConcreteSource.writer configuration.reservePackets query))
    configuration.generator configuration.view configuration.views configuration.agreement configuration.entropy created credential current before input
    configuration.edGetter configuration.mlGetter
    (membership configuration before.base.objects.server.consumed_registrations)
    (configuration.replayAllocate before.base.objects.server.consumed_registrations)
    (reservation configuration before.base.objects.server.consumed_registrations)
    (configuration.replayFootprint before.base.objects.server.consumed_registrations)
    (fun history=>insertion configuration {before.base.objects.server with consumed_registrations:=history})

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredAccept
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredAccept.membership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredAccept.membership
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredAccept.reservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredAccept.reservation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredAccept.insertion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredAccept.insertion
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredAccept.target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredAccept.target
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredAccept.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredAccept.query
