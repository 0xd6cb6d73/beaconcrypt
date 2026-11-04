-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedOrdinary
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedCreate
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedBuild
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedAccept
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedEffects
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditedRefused
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceExecution
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLowModel
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcher
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

noncomputable def publicOperations :∀query :RegistrationNativePlatformPublicAdapterInterface.Spec.Domain,
    RegistrationNativePlatformPublicAdapterSourceExecution.Raw n KemSK R P (RegistrationNativePlatformPublicAdapterInterface.Spec.Range query)
  | .inl query=>RegistrationNativePlatformPublicAdapterConfiguredEffects.coinSource configuration created query
  | .inr (.create identityKey mlKey keyId)=>fun before=>RegistrationNativePlatformPublicAdapterCreateNormalized.source coins setup checks
      configuration.agreement.representation created configuration.view children configuration.generator keyId identityKey mlKey before
  | .inr (.accept input)=>fun before=>RegistrationNativePlatformPublicAdapterAcceptActualSource.sourceOperation configuration created before input
  | .inr (.bundle index)=>fun before=>RegistrationNativePlatformPublicAdapterBundlePhysical.run coins setup checks configuration.agreement.representation created configuration.view
      (RegistrationNativePlatformPublicAdapterLeaves.localOperations originalLocal) configuration.edFailure writer children configuration.generator before index
  | .inr (.build handle payload)=>fun before=>RegistrationNativePlatformPublicAdapterConfiguredBuild.sourceOperation configuration before handle payload
  | .inr (.finish index input)=>fun before=>RegistrationNativePlatformPublicAdapterConfiguredFinish.sourceCall configuration created before index input
  | .inr (.hmac key message)=>RegistrationNativePlatformPublicAdapterConfiguredEffects.hmacSource (setup:=setup) key message
  | .inr (.hash bytes)=>RegistrationNativePlatformPublicAdapterConfiguredEffects.hashSource configuration created bytes
  | .inr (.serverSend key bytes)=>fun before=>RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.send setup configuration.reserveFrame configuration.keyView configuration.sealFailure
      configuration.erased configuration.view configuration.views before bytes key
  | .inr (.serverRaw bytes)=>fun before=>RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.receive setup configuration.reserveFrame configuration.keyView configuration.sealFailure
      configuration.erased configuration.view configuration.views before bytes
  | .inr (.beaconSend index bytes)=>fun before=>RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.send setup configuration.reserveFrame configuration.keyView configuration.sealFailure
      configuration.erased before index bytes
  | .inr (.beaconRaw index bytes)=>fun before=>RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.receive setup configuration.reserveFrame configuration.keyView configuration.sealFailure
      configuration.erased before index bytes

noncomputable def publicCalls (query :RegistrationNativePlatformPublicAdapterInterface.Spec.Domain)
    (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before) :
    TotalStep auditPrivate ((auditModel query).run before) :=by
  cases query with
  | inl query=>exact RegistrationNativePlatformPublicAdapterAuditedEffects.coin configuration created credential before.1 before.2 stored query
  | inr command=>cases command with
    | create identityKey mlKey keyId=>exact RegistrationNativePlatformPublicAdapterAuditedCreate.step configuration created credential before stored identityKey mlKey keyId
    | accept input=>exact RegistrationNativePlatformPublicAdapterAuditedAccept.step configuration created credential before stored input
    | bundle index=>exact RegistrationNativePlatformPublicAdapterAuditedBundle.step configuration created credential before stored index
    | build handle payload=>exact RegistrationNativePlatformPublicAdapterAuditedBuild.step configuration created credential before stored handle payload
    | finish index input=>exact RegistrationNativePlatformPublicAdapterAuditedFinish.step configuration created credential before stored index input
    | hmac key message=>exact RegistrationNativePlatformPublicAdapterAuditedEffects.hmac configuration created credential before.1 before.2 stored key message
    | hash bytes=>exact RegistrationNativePlatformPublicAdapterAuditedEffects.hash configuration created credential before.1 before.2 stored bytes
    | serverSend key bytes=>exact RegistrationNativePlatformPublicAdapterAuditedOrdinary.serverSend configuration created credential before stored bytes key
    | serverRaw bytes=>exact RegistrationNativePlatformPublicAdapterAuditedOrdinary.serverReceive configuration created credential before stored bytes
    | beaconSend index bytes=>exact RegistrationNativePlatformPublicAdapterAuditedOrdinary.beaconSend configuration created credential before stored index bytes
    | beaconRaw index bytes=>exact RegistrationNativePlatformPublicAdapterAuditedOrdinary.beaconReceive configuration created credential before stored index bytes

theorem public_source (query :RegistrationNativePlatformPublicAdapterInterface.Spec.Domain)
    (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source) (stored :auditPrivate before) :
    raw auditPhysical (publicCalls configuration created credential query before stored)=
      publicOperations configuration created query (auditPhysical before stored) :=by
  cases query with
  | inl query=>exact RegistrationNativePlatformPublicAdapterAuditedEffects.coin_query configuration created credential before.1 before.2 stored query
  | inr command=>cases command with
    | create identityKey mlKey keyId=>exact RegistrationNativePlatformPublicAdapterAuditedCreate.query configuration created credential before stored identityKey mlKey keyId
    | accept input=>
      exact (RegistrationNativePlatformPublicAdapterAuditedAccept.query configuration created credential before stored input).trans
        (RegistrationNativePlatformPublicAdapterAcceptActualSource.stored_source configuration created credential before.1 stored input)
    | bundle index=>exact RegistrationNativePlatformPublicAdapterAuditedBundle.query configuration created credential before stored index
    | build handle payload=>exact RegistrationNativePlatformPublicAdapterAuditedBuild.query configuration created credential before stored handle payload
    | finish index input=>exact RegistrationNativePlatformPublicAdapterAuditedFinish.query configuration created credential before stored index input
    | hmac key message=>exact RegistrationNativePlatformPublicAdapterAuditedEffects.hmac_query configuration created credential before.1 before.2 stored key message
    | hash bytes=>exact RegistrationNativePlatformPublicAdapterAuditedEffects.hash_query configuration created credential before.1 before.2 stored bytes
    | serverSend key bytes=>exact RegistrationNativePlatformPublicAdapterAuditedOrdinary.serverSend_query configuration created credential before stored bytes key
    | serverRaw bytes=>exact RegistrationNativePlatformPublicAdapterAuditedOrdinary.serverReceive_query configuration created credential before stored bytes
    | beaconSend index bytes=>exact RegistrationNativePlatformPublicAdapterAuditedOrdinary.beaconSend_query configuration created credential before stored index bytes
    | beaconRaw index bytes=>exact RegistrationNativePlatformPublicAdapterAuditedOrdinary.beaconReceive_query configuration created credential before stored index bytes

noncomputable def operations :∀query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain,
    RegistrationNativePlatformPublicAdapterSourceExecution.Raw n KemSK R P (RegistrationNativePlatformPublicAdapterLowSpec.Spec.Range query)
  | .inl query=>publicOperations configuration created query
  | .inr _=>RegistrationNativePlatformPublicAdapterAuditedRefused.sourceOperation

noncomputable def calls (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain)
    (before :RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source)
    (stored :RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential before) :
    TotalStep (RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential)
      ((RegistrationNativePlatformPublicAdapterAuditLowModel.model (n:=n) configuration created credential query).run before) :=by
  cases query with
  | inl query=>
    exact RegistrationNativePlatformPublicAdapterBuildRaw.modelCast
      (congrArg (fun action=>action.run before) (RegistrationNativePlatformPublicAdapterAuditLowModel.public_query configuration created credential query).symm)
      (publicCalls configuration created credential query before stored)
  | inr query=>cases query with
    | serverSend key bytes oversized=>exact RegistrationNativePlatformPublicAdapterAuditedRefused.server configuration created credential before stored key bytes oversized
    | beaconSend owner bytes oversized=>exact RegistrationNativePlatformPublicAdapterAuditedRefused.beacon configuration created credential before stored owner bytes oversized

theorem local_source (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain)
    (before :RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source)
    (stored :RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential before) :
    raw (RegistrationNativePlatformPublicAdapterAuditLowModel.physical (n:=n) configuration created credential)
      (calls configuration created credential query before stored)=
      operations configuration created query (RegistrationNativePlatformPublicAdapterAuditLowModel.physical (n:=n) configuration created credential before stored) :=by
  cases query with
  | inl query=>
    unfold calls
    erw [raw_cast]
    exact public_source configuration created credential query before stored
  | inr query=>cases query with
    | serverSend key bytes oversized=>exact RegistrationNativePlatformPublicAdapterAuditedRefused.server_query configuration created credential before stored key bytes oversized
    | beaconSend owner bytes oversized=>exact RegistrationNativePlatformPublicAdapterAuditedRefused.beacon_query configuration created credential before stored owner bytes oversized

noncomputable def interpreter :QueryImpl RegistrationNativePlatformPublicAdapterLowSpec.Spec
    (RegistrationNativePlatformPublicAdapterSourceRuntime.M n KemSK R P):=
  RegistrationNativePlatformPublicAdapterSourceExecution.source (operations configuration created)

theorem query (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain)
    (before :RegistrationNativePlatformExtractedSdkPublic.State (RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential)) :
    (fun result=>RegistrationNativePlatformPublicAdapterSourceRuntime.embed (result.1,
      RegistrationNativePlatformPublicAdapterAuditLowModel.physical (n:=n) configuration created credential result.2.1 result.2.2)) <$>
      (RegistrationNativePlatformExtractedSdkPublic.handler (RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential)
        (RegistrationNativePlatformPublicAdapterAuditLowModel.model (n:=n) configuration created credential)
        (calls configuration created credential) query).run before=
      RegistrationNativePlatformPublicAdapterSourceRuntime.run (interpreter configuration created query)
        (RegistrationNativePlatformPublicAdapterAuditLowModel.physical (n:=n) configuration created credential before.1 before.2) :=
  RegistrationNativePlatformPublicAdapterSourceExecution.query
    (RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential)
    (RegistrationNativePlatformPublicAdapterAuditLowModel.model (n:=n) configuration created credential)
    (calls configuration created credential) (RegistrationNativePlatformPublicAdapterAuditLowModel.physical (n:=n) configuration created credential)
    (operations configuration created) (fun selected before=>local_source configuration created credential selected before.1 before.2) query before

theorem program {Value :Type} (work :OracleComp RegistrationNativePlatformPublicAdapterLowSpec.Spec Value)
    (before :RegistrationNativePlatformExtractedSdkPublic.State (RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential)) :
    (fun result=>RegistrationNativePlatformPublicAdapterSourceRuntime.embed (result.1,
      RegistrationNativePlatformPublicAdapterAuditLowModel.physical (n:=n) configuration created credential result.2.1 result.2.2)) <$>
      (simulateQ (RegistrationNativePlatformExtractedSdkPublic.handler (RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential)
        (RegistrationNativePlatformPublicAdapterAuditLowModel.model (n:=n) configuration created credential)
        (calls configuration created credential)) work).run before=
      RegistrationNativePlatformPublicAdapterSourceRuntime.run (simulateQ (interpreter configuration created) work)
        (RegistrationNativePlatformPublicAdapterAuditLowModel.physical (n:=n) configuration created credential before.1 before.2) :=
  RegistrationNativePlatformPublicAdapterSourceExecution.program
    (RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential)
    (RegistrationNativePlatformPublicAdapterAuditLowModel.model (n:=n) configuration created credential)
    (calls configuration created credential) (RegistrationNativePlatformPublicAdapterAuditLowModel.physical (n:=n) configuration created credential)
    (operations configuration created) (fun selected before=>local_source configuration created credential selected before.1 before.2) work before

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcher

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcher.publicCalls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcher.publicCalls

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcher.public_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcher.public_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcher.calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcher.calls

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcher.local_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcher.local_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcher.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcher.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcher.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcher.program
