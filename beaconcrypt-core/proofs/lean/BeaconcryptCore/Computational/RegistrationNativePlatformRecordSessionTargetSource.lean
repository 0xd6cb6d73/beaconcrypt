-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteRecordSlotComparison
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargetSource
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
    (target : Fin budget.accept ×Fin budget.capacity) (previous : Platform)
local notation "selected"=>Prod.snd target
local notation "selectedAccept"=>Fin.val (Prod.fst target)
local notation "wire" => RegistrationNativePlatformConcreteSource.wire
local notation "allocation" => RegistrationNativePlatformConcreteSource.rawAllocation reserveBytes
local notation "reserveFrame" => reserveBytes
local notation "helper" => RegistrationNativePlatformConcreteSource.helper reserveBytes
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets
local notation "work" => program setup checks wire source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous


variable (qInit qGenerate qSign qKem qKeygen qEncap : Nat) (caps : RegistrationNativePlatformPublicExternalCaps.Caps)
local notation "samplerCoins" => RegistrationNativePlatformG3UniformSamplerBounds.cost budget qKeygen qEncap
local notation "allowance" => RegistrationNativePlatformConcreteEntropyFrame.allowance qGenerate qSign qKem caps
local notation "reserveCoins" => caps.bytes
local notation "constructorCoins" => (qInit+32)
local notation "mlCoins" => qGenerate
variable (kind : RegistrationNativePlatformRecordSessionTargets.Kind)
local notation "canonical"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "observe"=>RegistrationNativePlatformRecordSessionTargets.pinnedEvent setup.source.crypto canonical serverKeyId budget route kind target
local notation "decision"=>fun value:Value×RegistrationNativeLedger.State=>@decide
  (RegistrationNativePlatformRecordSessionTargets.PinnedAt setup.source.crypto canonical serverKeyId budget route kind target value) (Classical.propDecidable _)
noncomputable def real (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) : ProbComp Bool:=
  RegistrationNativePlatformOrdinaryObserverSecurity.real setup checks wire route source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget previous decision representation
noncomputable def ideal : ProbComp Bool:=
  (fun result=>RegistrationNativePlatformG3UniformOpaqueRecord.event source observe
    (RegistrationNativeRecordPackage.nativeView (result.1,result.2.2.2.2.1) result.2.2.2.2.2.base.produced)) <$>
    RegistrationNativePlatformRecordPartnerJointUniform.joint setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous
noncomputable def loss (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) : ℝ≥0∞:=
  RegistrationNativePlatformConcreteRecordSlotComparison.loss setup checks route source ensureInit identityIndex serverKeyId selectedAccept
    view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget selected previous
    qInit qGenerate qSign qKem qKeygen qEncap caps observe fallback
include bounded in
/-- The original public pin-filtered target event reaches the SAME full uniform sampler/source joint analysis with the existing ordinary comparison loss. Slots and descriptor traces are not exposed to the reduction observer. -/
theorem forward
    (initialized : (ensureInit.run ()).IsTotalQueryBound qInit)
    (generation : source.generate.IsTotalQueryBound qGenerate)
    (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (kemBound : ∀ (parameters : Sample KemSK (budget.cap 4+budget.cap 5)) query before,
      ((RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem (Fin.val (Prod.snd target)) parameters.profile.pairs parameters.profile.publicKey parameters.profile.challenge parameters.candidate query).run before).IsTotalQueryBound qKem)
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
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[real setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets
      bounds mode adversary budget target previous kind representation] {true}≤
    𝒟[ideal setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets
      bounds mode adversary budget target previous kind] {true}+
    loss setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets
      bounds mode adversary budget target previous qInit qGenerate qSign qKem qKeygen qEncap caps kind fallback := by
  have compared:=RegistrationNativePlatformConcreteRecordSlotComparison.forward setup checks route source ensureInit identityIndex serverKeyId selectedAccept
    view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget bounded selected previous
    qInit qGenerate qSign qKem qKeygen qEncap caps observe initialized generation signing kemBound keygenBound encapBound registrationBound peerBound bytesBound packetsBound
    representation correct functional candidate fallback
  rw [RegistrationNativePlatformRecordPartnerJointUniform.ideal_source] at compared
  convert compared using 1 <;>rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargetSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargetSource.forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargetSource.forward
