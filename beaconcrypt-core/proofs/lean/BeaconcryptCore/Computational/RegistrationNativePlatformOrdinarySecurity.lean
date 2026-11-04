-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTargetSecurity
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryEventComposition
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSelected
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordObserverIdeal
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteEntropyFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformSamplerBounds
import BeaconcryptCore.Computational.RegistrationNativePrimitiveCosts
/-! Original initialized source LR and weighted APP bounds with concrete source dictionaries. Source designation, warm initialization and complete resource bills are derived internally. Both centered LR directions charge the original signature-origin family once; weighted APP retains one original selector baseline. The shared classical 512-bit CTX random-oracle model and named primitive reductions remain explicit. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySecurity
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

section Lor
variable (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
noncomputable def lorLoss (target : Fin budget.accept × Fin budget.capacity) (winning : Bool) : ℝ≥0∞ :=
  RegistrationNativePlatformConcreteObserverSecurity.loss setup checks route source ensureInit identityIndex serverKeyId target.1.val
    view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds .P adversary budget target.2 previous
    qInit qGenerate qSign qKem qKeygen qEncap caps
    (RegistrationNativeLorRecordSecurity.observer setup.source.crypto canonical serverKeyId budget filter guess target winning) fallback
local notation "loss" => lorLoss setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds adversary budget previous qInit qGenerate qSign qKem qKeygen qEncap caps fallback filter guess
local notation "broad(" winning ")" => RegistrationNativePlatformOrdinaryEventComposition.lorBroad (n := cap) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget filter guess winning

include bounded initialized generation signing kemBound keygenBound encapBound registrationBound peerBound bytesBound packetsBound correct functional candidate shortRejects in
/-- Original broad winning and eligibility events satisfy both centered LR bounds, with the source signature-origin family charged once. -/
theorem lor :
    (𝒟[broad(true)] {true} ≤ 2⁻¹ * 𝒟[broad(false)] {true} + originLoss + (∑ target,loss target true) + 2⁻¹*(∑ target,loss target false)) ∧
    (2⁻¹ * 𝒟[broad(false)] {true} ≤ 𝒟[broad(true)] {true} + originLoss + (∑ target,loss target true) + 2⁻¹*(∑ target,loss target false)) := by
  apply RegistrationNativePlatformOrdinaryEventComposition.lor_centered_of_targets (n := cap) setup checks route representation view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous
    budget filter guess bounded shortRejects budget.create (Nat.le_succ _) edFallback ordinaryFallback loss
  intro target
  exact RegistrationNativePlatformOrdinaryTargetSecurity.lor setup checks route source ensureInit identityIndex serverKeyId view failure
      reserveRegistration reservePeer reserveBytes erased reservePackets bounds adversary budget bounded target previous
      qInit qGenerate qSign qKem qKeygen qEncap caps fallback filter guess initialized generation signing (kemBound target.2)
      keygenBound encapBound registrationBound peerBound bytesBound packetsBound representation correct functional candidate
end Lor

section App
variable (claim : Value → Option (Nat × Pqxdh.Bytes))
noncomputable def appLoss (target : Fin budget.accept × Fin budget.capacity) (winning : Bool) : ℝ≥0∞ :=
  RegistrationNativePlatformConcreteObserverSecurity.loss setup checks route source ensureInit identityIndex serverKeyId target.1.val
    view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds .P adversary budget target.2 previous
    qInit qGenerate qSign qKem qKeygen qEncap caps
    (Bool.rec (fun actual => RegistrationNativeCanonicalSelector.selected setup.source.crypto canonical serverKeyId budget claim target (Prod.fst actual) (Prod.snd actual))
      (RegistrationNativeCanonicalCoverage.decision setup.source.crypto canonical serverKeyId budget claim target) winning) fallback
local notation "loss" => appLoss setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds adversary budget previous qInit qGenerate qSign qKem qKeygen qEncap caps fallback claim
local notation "broad" => RegistrationNativePlatformOrdinaryEventComposition.appBroad (n := cap) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous budget claim

include bounded initialized generation signing kemBound keygenBound encapBound registrationBound peerBound bytesBound packetsBound correct functional candidate shortRejects in
/-- Weighted original APP success retains one same-run selector baseline and charges the source signature-origin family once. -/
theorem app_weighted :
    𝒟[broad] {true} ≤ originLoss + ((256^bounds.min : Nat) : ℝ≥0∞)⁻¹ + (∑ target,loss target true) +
      ((256^bounds.min : Nat) : ℝ≥0∞)⁻¹*(∑ target,loss target false) := by
  apply RegistrationNativePlatformOrdinaryEventComposition.app_weighted_of_targets (n := cap) setup checks route representation view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reservePackets source ensureInit identityIndex serverKeyId bounds adversary previous
    budget claim bounded shortRejects budget.create (Nat.le_succ _) edFallback ordinaryFallback loss
  intro target
  exact RegistrationNativePlatformOrdinaryTargetSecurity.fresh_bytes setup checks route source ensureInit identityIndex serverKeyId view failure
      reserveRegistration reservePeer reserveBytes erased reservePackets bounds adversary budget bounded target previous
      qInit qGenerate qSign qKem qKeygen qEncap caps fallback claim initialized generation signing (kemBound target.2)
      keygenBound encapBound registrationBound peerBound bytesBound packetsBound representation correct functional candidate
end App
end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySecurity.lor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySecurity.lor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySecurity.app_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySecurity.app_weighted
