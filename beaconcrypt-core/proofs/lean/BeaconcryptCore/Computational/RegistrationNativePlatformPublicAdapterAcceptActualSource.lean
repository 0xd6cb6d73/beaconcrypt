-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualLookup
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptReceiptNormal
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredAccept
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcherCore
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSource
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
variable (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
local notation "PhysicalM"=>StateT (RegistrationNativePlatformSdkReification.Backend n KemSK) (StateT P ProbComp)
@[instance_reducible] noncomputable def physicalCrypto :CryptoOperations (RustT (StateT (RegistrationNativePlatformSdkReification.Backend n KemSK) (StateT P ProbComp))):=
  RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography coins configuration.view
noncomputable local instance physicalLocal :LocalOperations (RustT (StateT (RegistrationNativePlatformSdkReification.Backend n KemSK) (StateT P ProbComp))):=
  RegistrationNativePlatformPublicAdapterLeaves.localOperations originalLocal
noncomputable local instance physicalContainers :ContainerOperations (RustT (StateT (RegistrationNativePlatformSdkReification.Backend n KemSK) (StateT P ProbComp))):=
  RegistrationNativePlatformPublicAdapterAcceptObserver.containers originalContainers
@[instance_reducible] noncomputable def physicalChildren :ChildOperations (RustT (StateT (RegistrationNativePlatformSdkReification.Backend n KemSK) (StateT P ProbComp))):=
  let :CryptoOperations (RustT PhysicalM):=physicalCrypto configuration
  RegistrationNativePlatformPublicAdapterAuthPhysical.children coins setup checks configuration.agreement.representation created source.verify configuration.edFunctional
    (RegistrationNativePlatformPublicAdapterDispatcherCore.recording (m:=PhysicalM)) (fun query=>StateT.lift (writer query))
local instance physicalCodecs :Codecs (RustT (StateT (RegistrationNativePlatformSdkReification.Backend n KemSK) (StateT P ProbComp))):=AdapterPublicConcreteCodecs.codecs

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem ed_getter (key :ed.PublicKey) :
    (physicalCrypto (n:=n) configuration |>.edPublicBytes key).run=pure (.ok (configuration.view.edPublic key)) :=by
  change (RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.transform coins (originalCrypto.edPublicBytes key)).run=_
  rw [configuration.edGetter,RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.pure_transform,RustT.run_pure]

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem ml_getter (identity :beaconcrypt_public_wrapper.auth.MldsaIdentity) :
    (physicalLocal (n:=n) (KemSK:=KemSK) (P:=P) |>.auth_MldsaIdentity_public_key identity).run=pure (.ok (configuration.view.mldsa identity).publicKey) :=by
  change StateT.lift (originalLocal.auth_MldsaIdentity_public_key identity).run=_
  rw [configuration.mlGetter]
  apply StateT.ext
  intro before
  simp only [StateT.run_lift,StateT.run_pure,pure_bind]

noncomputable def body (self :beaconcrypt_public_wrapper.server.Server) (input :Slice U8) (rng :R) :
    RustT PhysicalM (AdapterPublicServerAgreementReceipt.Word R):=
  let :CryptoOperations (RustT PhysicalM):=physicalCrypto configuration
  let :ChildOperations (RustT PhysicalM):=physicalChildren configuration created
  beaconcrypt_public_request.server.Server.get_shared_secret_with_rng (m:=RustT PhysicalM) configuration.generator self input rng

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem body_source (self :beaconcrypt_public_wrapper.server.Server) (input :Slice U8) (rng :R)
    (before :RegistrationNativePlatformSdkReification.Backend n KemSK) (previous :P) :
    ((body configuration created self input rng).run.run before).run previous=
      (fun result=>((result.1.1.2,RegistrationNativePlatformPublicAdapterAcceptActualLookup.mark configuration.view result.1.1.1 result.1.2),result.2)) <$>
        ((RegistrationNativePlatformPublicAdapterAccept.program originalContainers coins setup checks source.verify configuration.agreement.representation created
          configuration.generator configuration.view self input rng).run before).run previous :=by
  let :CryptoOperations (RustT PhysicalM):=physicalCrypto configuration
  let :ChildOperations (RustT PhysicalM):=physicalChildren configuration created
  unfold body
  dsimp only
  rw [AdapterPublicServerEntry.source]
  unfold AdapterPublicServerEntry.sequence
  simp only [RustT.run_bind,StateT.run_bind]
  have auth:=RegistrationNativePlatformPublicAdapterAuthPhysical.authenticate (n:=n) coins setup checks configuration.agreement.representation created source.verify
    configuration.edFunctional (RegistrationNativePlatformPublicAdapterDispatcherCore.recording (m:=PhysicalM)) (fun query=>StateT.lift (writer query))
    configuration.view (ed_getter configuration) (ml_getter configuration) self input
  rw [auth]
  unfold RegistrationNativePlatformPublicAdapterAccept.program
  cases decoded:RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none=>simp only [StateT.run_pure,map_pure,pure_bind,RustT.run_pure,RegistrationNativePlatformPublicAdapterAcceptActualLookup.mark]
  | some packet=>
    simp only [StateT.run_bind,map_bind]
    apply bind_congr
    rintro ⟨⟨checked,current⟩,post⟩
    cases checked with
    | fail error | div=>simp only [StateT.run_pure,map_pure,RegistrationNativePlatformPublicAdapterAcceptActualLookup.mark]
    | ok optional=>cases optional with
      | none=>simp only [RustT.run_pure,StateT.run_pure,map_pure,RegistrationNativePlatformPublicAdapterAcceptActualLookup.mark]
      | some pending=>
        exact RegistrationNativePlatformPublicAdapterAcceptActualLookup.lookup originalContainers setup checks configuration.view configuration.generator
          configuration.agreement coins self pending rng current post

noncomputable def finish (before :RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P)
    (result :RustM (AdapterPublicServerAgreementReceipt.Word R)×(RegistrationNativePlatformSdkReification.Backend n KemSK×P)) :
    RustM (Option Nat×RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P)×(RegistrationNativePlatformSdkReification.Backend n KemSK×P):=
  match result.1 with
  | .fail error=>(.fail error,result.2)
  | .div=>(.div,result.2)
  | .ok returned=>
    let after:=RegistrationNativePlatformPublicAdapterAccept.committed configuration.view configuration.views (none,returned) result.2
    (.ok (RegistrationNativePlatformPublicAdapterAcceptStore.handle before.nextSession returned,
      RegistrationNativePlatformPublicAdapterStore.accept before returned after),after)

noncomputable def sourceOperation (before :RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P) (input :Slice U8) :
    ProbComp (RustM (Option Nat×RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P)×(RegistrationNativePlatformSdkReification.Backend n KemSK×P)):=
  finish configuration before <$>
    ((fun result=>(result.1.1,(result.1.2,result.2))) <$>
      (((body configuration created before.server input before.rng).run.run before.backend.1).run before.backend.2))

noncomputable def originalProgram (before :RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P) (input :Slice U8) :=
  ((RegistrationNativePlatformPublicAdapterAccept.program originalContainers coins setup checks source.verify configuration.agreement.representation created
    configuration.generator configuration.view before.server input before.rng).run before.backend.1).run before.backend.2

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem finish_compatible (before :RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P)
    (receipt :AdapterPublicServerReservationReceipt.Receipt R) (word :AdapterPublicServerAgreementReceipt.Word R)
    (raw :RegistrationNativePlatformSdkReification.Backend n KemSK×P)
    (valid :receipt=none ∨∃capture,receipt=some (.ok capture)) :
    finish configuration before (.ok word,(RegistrationNativePlatformPublicAdapterAcceptActualLookup.mark configuration.view receipt raw.1,raw.2))=
      RegistrationNativePlatformPublicAdapterAcceptStore.finish configuration.view configuration.views before
        (RegistrationNativePlatformSdkAcceptInstrumentedSource.reply receipt (.ok word),raw) :=by
  rcases valid with absent |⟨capture,present⟩
  · rw [absent]
    rfl
  · rw [present]
    rfl

omit [PublicWrapperPlatform.CryptoOperations] in
theorem word_normal (credential :RegistrationNativeMldsa.Credential source)
    (current :RegistrationNativeExperiment.State n KemSK source×P)
    (stored :RegistrationNativePlatformPublicAdapterDispatcherCore.Private configuration created credential current)
    (input :Slice U8)
    (result :((AdapterPublicServerReservationReceipt.Receipt R×RustM (AdapterPublicServerAgreementReceipt.Word R))×
      RegistrationNativePlatformSdkReification.Backend n KemSK)×P)
    (supported :result∈support (originalProgram configuration created (physical configuration created credential current stored) input)) :
    ∃word,result.1.1.2=.ok word :=by
  let before:=physical configuration created credential current stored
  let finished:=RegistrationNativePlatformPublicAdapterAcceptStore.finish configuration.view configuration.views before
    (RegistrationNativePlatformSdkAcceptInstrumentedSource.reply result.1.1.1 result.1.1.2,(result.1.2,result.2))
  have allowed:finished∈support (RegistrationNativePlatformPublicAdapterConfiguredAccept.sourceOperation configuration created before input) :=by
    unfold RegistrationNativePlatformPublicAdapterConfiguredAccept.sourceOperation RegistrationNativePlatformPublicAdapterAcceptStore.run
    rw [support_map]
    exact ⟨result,supported,rfl⟩
  rw [←RegistrationNativePlatformPublicAdapterConfiguredAccept.query configuration created credential current stored input] at allowed
  unfold raw at allowed
  rw [support_map] at allowed
  obtain ⟨packet,_possible,same⟩:=allowed
  have outer:=congrArg Prod.fst same
  cases wordEq:result.1.1.2 with
  | ok word=>exact ⟨word,rfl⟩
  | fail error=>
    simp only [finished,RegistrationNativePlatformPublicAdapterAcceptStore.finish,
      RegistrationNativePlatformSdkAcceptInstrumentedSource.reply,wordEq] at outer
    cases outer
  | div=>
    simp only [finished,RegistrationNativePlatformPublicAdapterAcceptStore.finish,
      RegistrationNativePlatformSdkAcceptInstrumentedSource.reply,wordEq] at outer
    cases outer

omit [PublicWrapperPlatform.CryptoOperations] in
theorem stored_source (credential :RegistrationNativeMldsa.Credential source)
    (current :RegistrationNativeExperiment.State n KemSK source×P)
    (stored :RegistrationNativePlatformPublicAdapterDispatcherCore.Private configuration created credential current) (input :Slice U8) :
    RegistrationNativePlatformPublicAdapterConfiguredAccept.sourceOperation configuration created
      (physical configuration created credential current stored) input=
      sourceOperation configuration created (physical configuration created credential current stored) input :=by
  unfold sourceOperation
  rw [body_source]
  simp only [Functor.map_map]
  unfold RegistrationNativePlatformPublicAdapterConfiguredAccept.sourceOperation RegistrationNativePlatformPublicAdapterAcceptStore.run
  rw [map_eq_bind_pure_comp,map_eq_bind_pure_comp]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro result supported
  obtain ⟨word,normal⟩:=word_normal configuration created credential current stored input result supported
  have receipt:=RegistrationNativePlatformPublicAdapterAcceptReceiptNormal.program originalContainers coins configuration.generator setup checks source.verify
    configuration.agreement.representation created configuration.view
    (physical configuration created credential current stored).server input
    (physical configuration created credential current stored).rng
    (physical configuration created credential current stored).backend.1
    (physical configuration created credential current stored).backend.2 result word supported normal
  apply congrArg pure
  dsimp only [Function.comp_def]
  rw [normal]
  exact (finish_compatible configuration (physical configuration created credential current stored) result.1.1.1 word (result.1.2,result.2) receipt).symm

omit [PublicWrapperPlatform.CryptoOperations] in
theorem query_actual (credential :RegistrationNativeMldsa.Credential source)
    (current :RegistrationNativeExperiment.State n KemSK source×P)
    (stored :RegistrationNativePlatformPublicAdapterDispatcherCore.Private configuration created credential current) (input :Slice U8) :
    raw (physical configuration created credential)
      (RegistrationNativePlatformPublicAdapterConfiguredAccept.step configuration created credential current stored input)=
      sourceOperation configuration created (physical configuration created credential current stored) input :=
  (RegistrationNativePlatformPublicAdapterConfiguredAccept.query configuration created credential current stored input).trans
    (stored_source configuration created credential current stored input)

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSource.ed_getter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSource.ed_getter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSource.ml_getter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSource.ml_getter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSource.body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSource.body_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSource.finish_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSource.finish_compatible

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSource.word_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSource.word_normal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSource.stored_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSource.stored_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSource.query_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSource.query_actual
