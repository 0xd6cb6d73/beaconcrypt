-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionSecurity
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedExperiment
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityChangedBound
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureWarm
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordJointOriginBound
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteRecordBindingBound
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordJointBindingBound
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealSelected
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionWordBound
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointUniform
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionCoverage
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryObserverSecurity
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteEntropyFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformSamplerBounds
import BeaconcryptCore.Computational.RegistrationNativePrimitiveCosts
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryRecords
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicRecordOpaqueInitialized (Context prior)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations] [AdapterInitEdPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveBytes : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
open RegistrationNativePlatformG3UniformRecordProgram (Sample sample after program)
open PqxdhRecordLiftCtxProtocolBounds (BudgetKind categoryCost)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_bind weighted_run)
open PqxdhRecordLiftCtxBills (effectBill worldBill)
variable (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (previous : Platform)
local notation "wire" => RegistrationNativePlatformConcreteSource.wire
local notation "allocation" => RegistrationNativePlatformConcreteSource.rawAllocation reserveBytes
local notation "reserveFrame" => reserveBytes
local notation "helper" => RegistrationNativePlatformConcreteSource.helper reserveBytes
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets


variable (qInit qGenerate qSign qKem qKeygen qEncap : Nat) (caps : RegistrationNativePlatformPublicExternalCaps.Caps)
local notation "samplerCoins" => RegistrationNativePlatformG3UniformSamplerBounds.cost budget qKeygen qEncap
local notation "allowance" => RegistrationNativePlatformConcreteEntropyFrame.allowance qGenerate qSign qKem caps
local notation "reserveCoins" => caps.bytes
local notation "constructorCoins" => (qInit+32)
local notation "mlCoins" => qGenerate
variable (kind : RegistrationNativePlatformRecordSessionTargets.Kind)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (edFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
local notation "cap"=>budget.cap 4+budget.cap 5
local notation "canonical"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "job"=>RegistrationNativePlatformExtractedExperiment.profile (n:=cap) setup checks wire route representation source ensureInit identityIndex serverKeyId
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
noncomputable def original : ProbComp Bool:=
  Prod.fst <$> (job (RegistrationNativePlatformRecordSessionCoverage.event setup route source serverKeyId budget kind)).run previous
open RegistrationNativePlatformRecordSessionSecurity (originLoss targetLoss)

/-- The complete original public event executes the actual source dictionary on the same initialized native and persistent platform state. -/
theorem game_source
    (sealLength : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (openLength : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (edFunctional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto) :
    original setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget previous kind representation=
      RegistrationNativePlatformRecordSessionSecurity.original setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget previous kind representation := by
  unfold original RegistrationNativePlatformRecordSessionSecurity.original
  rw [RegistrationNativePlatformExtractedExperiment.profile_source (n:=cap) setup checks wire route representation source ensureInit identityIndex serverKeyId
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
    (RegistrationNativePlatformRecordSessionCoverage.event setup route source serverKeyId budget kind)
    sealLength openLength converted edFunctional]

include bounded in
/-- Both ordinary origin directions and both corrected public UKS events retain the original complete loss ledger on the actual extracted source dictionary. -/
theorem bound
    (initialized : (ensureInit.run ()).IsTotalQueryBound qInit)
    (generation : source.generate.IsTotalQueryBound qGenerate)
    (signing : ∀key request,(source.sign key request).IsTotalQueryBound qSign)
    (kemBound : ∀(selected:Fin (budget.create+1)) (parameters:Sample KemSK (budget.cap 4+budget.cap 5)) query before,
      ((RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val parameters.profile.pairs parameters.profile.publicKey parameters.profile.challenge parameters.candidate query).run before).IsTotalQueryBound qKem)
    (keygenBound : (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound : ∀publicKey,(simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps publicKey)).IsTotalQueryBound qEncap)
    (registrationBound : ∀before,(reserveRegistration.run before).IsTotalQueryBound caps.registration)
    (peerBound : ∀before,(reservePeer.run before).IsTotalQueryBound caps.peer)
    (bytesBound : ∀amount before,((reserveBytes amount).run before).IsTotalQueryBound caps.bytes)
    (packetsBound : ∀amount before,((reservePackets amount).run before).IsTotalQueryBound caps.packet)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (filler : PqxdhServerAuthKeySchedule.Output)
    (shortRejects : ∀(publicKey:PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length<64→setup.source.crypto.verify publicKey.toList bytes=none)
    (sealLength : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (openLength : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (edFunctional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto) :
    𝒟[original setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget previous kind representation] {true}≤
      originLoss setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget previous representation edFallback ordinaryFallback+
      ∑target:Fin budget.accept×Fin budget.capacity,targetLoss setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget previous qInit qGenerate qSign qKem qKeygen qEncap caps kind fallback target := by
  rw [game_source setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets
    bounds mode adversary budget previous kind representation sealLength openLength converted edFunctional]
  exact RegistrationNativePlatformRecordSessionSecurity.bound setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes
    erased reservePackets bounds mode adversary budget bounded previous qInit qGenerate qSign qKem qKeygen qEncap caps kind representation fallback edFallback ordinaryFallback
    initialized generation signing kemBound keygenBound encapBound registrationBound peerBound bytesBound packetsBound correct functional candidate filler shortRejects
end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryRecords
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryRecords.game_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryRecords.game_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryRecords.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryRecords.bound
