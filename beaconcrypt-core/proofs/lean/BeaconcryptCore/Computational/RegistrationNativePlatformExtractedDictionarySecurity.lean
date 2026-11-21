-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedExperiment
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySecurity
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTargetSecurity
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryEventComposition
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSelected
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordObserverIdeal
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteEntropyFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformSamplerBounds
import BeaconcryptCore.Computational.RegistrationNativePrimitiveCosts
/-! LR and weighted APP bounds for the actual extracted request-body dictionary on the unchanged initialized native profile. Complete source execution transport preserves every original event, centered direction, weighted baseline and loss. Public SDK object-wrapper adaptive binding is a separate refinement. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionarySecurity
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
    (bounds : PqxdhDeploymentInterface.FreshBounds)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec PqxdhDeploymentInterface.Mode.P) Value)
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
variable (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "cap" => budget.cap 4+budget.cap 5
attribute [local irreducible] RegistrationNativePlatformOrdinaryExperiment.profile RegistrationNativePlatformConcreteObserverSecurity.loss


variable (initialized : (ensureInit.run ()).IsTotalQueryBound qInit)
    (generation : source.generate.IsTotalQueryBound qGenerate)
    (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (kemBound : ∀ (selected : Fin (budget.create+1)) (parameters : Sample KemSK (budget.cap 4+budget.cap 5)) query before,
      ((RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val parameters.profile.pairs parameters.profile.publicKey parameters.profile.challenge parameters.candidate query).run before).IsTotalQueryBound qKem)
    (keygenBound : (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound : ∀ publicKey, (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps publicKey)).IsTotalQueryBound qEncap)
    (registrationBound : ∀ before, (reserveRegistration.run before).IsTotalQueryBound caps.registration)
    (peerBound : ∀ before, (reservePeer.run before).IsTotalQueryBound caps.peer)
    (bytesBound : ∀ amount before, ((reserveBytes amount).run before).IsTotalQueryBound caps.bytes)
    (packetsBound : ∀ amount before, ((reservePackets amount).run before).IsTotalQueryBound caps.packet)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length<64 → setup.source.crypto.verify publicKey.toList bytes=none)
    (edFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
local notation "originLoss" => RegistrationNativePlatformOrdinaryEventComposition.originLoss (n := cap) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget.create edFallback ordinaryFallback

variable (sealLength : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (openLength : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (edFunctional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
local notation "sourceProfile"=>RegistrationNativePlatformExtractedExperiment.profile (n:=cap) setup checks wire route representation source ensureInit identityIndex serverKeyId
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds PqxdhDeploymentInterface.Mode.P adversary

section Lor
variable (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
noncomputable def lorLoss (target : Fin budget.accept × Fin budget.capacity) (winning : Bool) : ℝ≥0∞ :=
  RegistrationNativePlatformOrdinarySecurity.lorLoss setup checks route source ensureInit identityIndex serverKeyId view failure
    reserveRegistration reservePeer reserveBytes erased reservePackets bounds adversary budget previous
    qInit qGenerate qSign qKem qKeygen qEncap caps fallback filter guess target winning
local notation "loss" => lorLoss setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds adversary budget previous qInit qGenerate qSign qKem qKeygen qEncap caps fallback filter guess
noncomputable def lorBroad (winning : Bool) : ProbComp Bool :=
  Prod.fst <$> ((sourceProfile (fun actual=>RegistrationNativeLorCoverage.broad setup.source.crypto canonical serverKeyId budget filter guess winning
    (actual.1,actual.2.1))).run previous)
local notation "broad(" winning ")"=>lorBroad setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes
  erased reservePackets bounds adversary budget previous representation filter guess winning

include bounded initialized generation signing kemBound keygenBound encapBound registrationBound peerBound bytesBound packetsBound correct functional candidate shortRejects sealLength openLength converted edFunctional in
/-- Original broad winning and eligibility events satisfy both centered LR bounds, with the source signature-origin family charged once. -/
theorem lor :
    (𝒟[broad(true)] {true} ≤ 2⁻¹ * 𝒟[broad(false)] {true} + originLoss + (∑ target,loss target true) + 2⁻¹*(∑ target,loss target false)) ∧
    (2⁻¹ * 𝒟[broad(false)] {true} ≤ 𝒟[broad(true)] {true} + originLoss + (∑ target,loss target true) + 2⁻¹*(∑ target,loss target false)) := by
  have transported (winning : Bool) := RegistrationNativePlatformExtractedExperiment.profile_source (n:=cap)
    setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds PqxdhDeploymentInterface.Mode.P adversary
    (fun actual=>RegistrationNativeLorCoverage.broad setup.source.crypto canonical serverKeyId budget filter guess winning (actual.1,actual.2.1))
    sealLength openLength converted edFunctional
  simp only [lorBroad,transported]
  exact RegistrationNativePlatformOrdinarySecurity.lor setup checks route source ensureInit identityIndex serverKeyId view failure
    reserveRegistration reservePeer reserveBytes erased reservePackets bounds adversary budget bounded previous
    qInit qGenerate qSign qKem qKeygen qEncap caps fallback initialized generation signing kemBound keygenBound encapBound
    registrationBound peerBound bytesBound packetsBound representation correct functional candidate shortRejects edFallback ordinaryFallback filter guess
end Lor

section App
variable (claim : Value → Option (Nat × Pqxdh.Bytes))
noncomputable def appLoss (target : Fin budget.accept × Fin budget.capacity) (winning : Bool) : ℝ≥0∞ :=
  RegistrationNativePlatformOrdinarySecurity.appLoss setup checks route source ensureInit identityIndex serverKeyId view failure
    reserveRegistration reservePeer reserveBytes erased reservePackets bounds adversary budget previous
    qInit qGenerate qSign qKem qKeygen qEncap caps fallback claim target winning
local notation "loss" => appLoss setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds adversary budget previous qInit qGenerate qSign qKem qKeygen qEncap caps fallback claim
noncomputable def appBroad : ProbComp Bool :=
  Prod.fst <$> ((sourceProfile (fun actual=>RegistrationNativeEvents.ceAppEvent setup.source.crypto canonical serverKeyId budget claim
    (actual.1,(actual.2.1,())))).run previous)
local notation "broad"=>appBroad setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes
  erased reservePackets bounds adversary budget previous representation claim

include bounded initialized generation signing kemBound keygenBound encapBound registrationBound peerBound bytesBound packetsBound correct functional candidate shortRejects sealLength openLength converted edFunctional in
/-- Weighted original APP success retains one same-run selector baseline and charges the source signature-origin family once. -/
theorem app_weighted :
    𝒟[broad] {true} ≤ originLoss + ((256^bounds.min : Nat) : ℝ≥0∞)⁻¹ + (∑ target,loss target true) +
      ((256^bounds.min : Nat) : ℝ≥0∞)⁻¹*(∑ target,loss target false) := by
  have transported := RegistrationNativePlatformExtractedExperiment.profile_source (n:=cap)
    setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds PqxdhDeploymentInterface.Mode.P adversary
    (fun actual=>RegistrationNativeEvents.ceAppEvent setup.source.crypto canonical serverKeyId budget claim (actual.1,(actual.2.1,())))
    sealLength openLength converted edFunctional
  simp only [appBroad,transported]
  exact RegistrationNativePlatformOrdinarySecurity.app_weighted setup checks route source ensureInit identityIndex serverKeyId view failure
    reserveRegistration reservePeer reserveBytes erased reservePackets bounds adversary budget bounded previous
    qInit qGenerate qSign qKem qKeygen qEncap caps fallback initialized generation signing kemBound keygenBound encapBound
    registrationBound peerBound bytesBound packetsBound representation correct functional candidate shortRejects edFallback ordinaryFallback claim
end App
end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionarySecurity


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionarySecurity.lor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionarySecurity.lor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionarySecurity.app_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionarySecurity.app_weighted
