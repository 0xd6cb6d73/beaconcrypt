-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargetSecurity
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionSecurity
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicRecordOpaqueInitialized (Context prior)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
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
local notation "job"=>RegistrationNativePlatformOrdinaryExperiment.profile (n:=cap) setup checks wire route representation source ensureInit identityIndex serverKeyId
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
noncomputable def original : ProbComp Bool:=
  Prod.fst <$> (job (RegistrationNativePlatformRecordSessionCoverage.event setup route source serverKeyId budget kind)).run previous
noncomputable def originLoss : ℝ≥0∞:=
  ∑index:Fin (budget.create+1),PqxdhJointIdentity.advantage setup.joint
    (RegistrationNativePlatformIdentityOriginBound.reduction (n:=budget.cap 4+budget.cap 5) setup checks wire route representation view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit identityIndex serverKeyId bounds mode adversary
      (fun _=>false) previous budget.create edFallback ordinaryFallback index)
noncomputable def targetLoss (target : Fin budget.accept×Fin budget.capacity) : ℝ≥0∞:=
  RegistrationNativePlatformRecordSessionTargetSecurity.loss setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes
    erased reservePackets bounds mode adversary budget target previous qInit qGenerate qSign qKem qKeygen qEncap caps kind fallback
include bounded in
/-- The original corrected public origin and both UKS events have their complete current source-model bound. Changed is charged once outside the original parsed-accept by owner family; each target has one whole-prefix recovery client and its appropriate physical record term. -/
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
    (shortRejects : ∀(publicKey:PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length<64→setup.source.crypto.verify publicKey.toList bytes=none) :
    𝒟[original setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget previous kind representation] {true}≤
      originLoss setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget previous representation edFallback ordinaryFallback+
      ∑target:Fin budget.accept×Fin budget.capacity,targetLoss setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget previous qInit qGenerate qSign qKem qKeygen qEncap caps kind fallback target := by
  have coverage:=RegistrationNativePlatformRecordSessionCoverage.broad_probability (n:=cap) setup checks route representation view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded shortRejects kind
  unfold RegistrationNativePlatformRecordSessionCoverage.targetEvent at coverage
  have split : 𝒟[original setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget previous kind representation] {true}≤
      Pr{let result←((job (RegistrationNativeIdentityOriginEvents.event setup.joint canonical)).run previous)}[result.1=true]+
      ∑target:Fin budget.accept×Fin budget.capacity,
        𝒟[RegistrationNativePlatformRecordSessionTargetSource.real setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes
          erased reservePackets bounds mode adversary budget target previous kind representation] {true} := by
    simpa only [original,RegistrationNativePlatformRecordSessionTargetSource.real,RegistrationNativePlatformOrdinaryObserverSecurity.real,
      RegistrationNativePlatformRecordSessionCoverage.targetEvent,←prEvent_eq_evalDist_singleton _ true,prEvent_map] using coverage
  have changed:=RegistrationNativePlatformIdentityChangedBound.changed_prekey_bound (n:=cap) setup checks wire route representation view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded
    budget.create (Nat.le_succ _) edFallback ordinaryFallback
  have targets :=Finset.sum_le_sum (s:=Finset.univ) (fun target _=>RegistrationNativePlatformRecordSessionTargetSecurity.bound setup checks route source ensureInit identityIndex serverKeyId
    view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget bounded target previous qInit qGenerate qSign qKem qKeygen qEncap caps kind
    initialized generation signing (kemBound target.2) keygenBound encapBound registrationBound peerBound bytesBound packetsBound representation correct functional candidate fallback filler)
  exact split.trans (add_le_add changed targets)
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionSecurity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionSecurity.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionSecurity.bound
