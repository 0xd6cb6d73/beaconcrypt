-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteObserverSecurity
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordObserverIdeal
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteEntropyFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformSamplerBounds
import BeaconcryptCore.Computational.RegistrationNativePrimitiveCosts
/-! Local original-target probability composition uses concrete source dictionaries and internally derived complete-prefix resource bills. Same-result selected/claimed data is an explicit intermediate receipt here; the final original event wrapper must derive it from the actual ideal source. No whole callback, Frame or startup-cap premise is introduced. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTargetComparison
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
    (target : Fin budget.accept × Fin budget.capacity) (previous : Platform)
local notation "selected" => Prod.snd target
local notation "selectedAccept" => Fin.val (Prod.fst target)
local notation "wire" => RegistrationNativePlatformConcreteSource.wire
local notation "allocation" => RegistrationNativePlatformConcreteSource.rawAllocation reserveBytes
local notation "reserveFrame" => reserveBytes
local notation "helper" => RegistrationNativePlatformConcreteSource.helper reserveBytes
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets
local notation "work" => program setup checks wire source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds PqxdhDeploymentInterface.Mode.P adversary budget selected previous


variable (qInit qGenerate qSign qKem qKeygen qEncap : Nat) (caps : RegistrationNativePlatformPublicExternalCaps.Caps)
local notation "samplerCoins" => RegistrationNativePlatformG3UniformSamplerBounds.cost budget qKeygen qEncap
local notation "allowance" => RegistrationNativePlatformConcreteEntropyFrame.allowance qGenerate qSign qKem caps
local notation "reserveCoins" => caps.bytes
local notation "constructorCoins" => (qInit+32)
local notation "mlCoins" => qGenerate
variable (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "cap" => budget.cap 4+budget.cap 5
local notation "TraceView" => RegistrationNativeRecordPackage.View cap
  (RegistrationNativePlatformSelectiveRecordTraceStartup.Extra cap KemSK RegistrationNativeKemSwitchSource.Phase Platform source) Value
local notation "traced" => RegistrationNativePlatformG3UniformRecordTraceView.run setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous
  (fun _ => PqxdhRecordLiftIdeal.KeyMode.random)

section Lor
variable (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
local notation "observe(" winning ")" => RegistrationNativeLorRecordSecurity.observer setup.source.crypto canonical serverKeyId budget filter guess target winning
local notation "real(" winning "," representation ")" => RegistrationNativePlatformOrdinaryObserverSecurity.real setup checks wire route source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds PqxdhDeploymentInterface.Mode.P adversary budget previous (observe(winning)) representation
local notation "ideal(" winning ")" => RegistrationNativePlatformOrdinaryObserverSecurity.ideal setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds PqxdhDeploymentInterface.Mode.P adversary budget selected previous (observe(winning))
local notation "loss(" winning ")" => RegistrationNativePlatformConcreteObserverSecurity.loss setup checks route source ensureInit identityIndex serverKeyId selectedAccept view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds PqxdhDeploymentInterface.Mode.P adversary budget selected previous qInit qGenerate qSign qKem qKeygen qEncap caps (observe(winning)) fallback

include bounded in
/-- The actual source target observer has both centered directions once its same-result ideal descriptor receipt is attached. All callback, sampler and startup bills are derived from individual primitive and allocator caps. -/
theorem lor_of_selected
    (initialized : (ensureInit.run ()).IsTotalQueryBound qInit)
    (generation : source.generate.IsTotalQueryBound qGenerate)
    (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (kemBound : ∀ (parameters : Sample KemSK (budget.cap 4+budget.cap 5)) query before,
      ((RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem (Fin.val selected) parameters.profile.pairs parameters.profile.publicKey parameters.profile.challenge parameters.candidate query).run before).IsTotalQueryBound qKem)
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

    (designation : ∀ (parameters : Sample KemSK cap) (observed : TraceView), (parameters,observed) ∈ support traced →
      ∀ finished ∈ observed.result,
        RegistrationNativeLorCanonical.GoodAt setup.source.crypto canonical serverKeyId budget filter target finished.2.1 →
        RegistrationNativeLorSelectedTests.TestsSelected setup.source.crypto canonical serverKeyId finished.2.1.2 finished.2.2.2.events
          (RegistrationNativePlatformInstallKernelStorage.Selected setup parameters.seed parameters.scalar parameters.candidate)) :
    (𝒟[real(true,representation)] {true} ≤ 2⁻¹ * 𝒟[real(false,representation)] {true} + loss(true) + 2⁻¹ * loss(false)) ∧
    (2⁻¹ * 𝒟[real(false,representation)] {true} ≤ 𝒟[real(true,representation)] {true} + loss(true) + 2⁻¹ * loss(false)) := by
  have into (winning : Bool) := RegistrationNativePlatformConcreteObserverSecurity.forward setup checks route source ensureInit identityIndex serverKeyId selectedAccept view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds PqxdhDeploymentInterface.Mode.P adversary budget bounded selected previous qInit qGenerate qSign qKem qKeygen qEncap caps (observe(winning)) initialized generation signing kemBound keygenBound encapBound registrationBound peerBound bytesBound packetsBound representation correct functional candidate fallback
  have back (winning : Bool) := RegistrationNativePlatformConcreteObserverSecurity.reverse setup checks route source ensureInit identityIndex serverKeyId selectedAccept view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds PqxdhDeploymentInterface.Mode.P adversary budget bounded selected previous qInit qGenerate qSign qKem qKeygen qEncap caps (observe(winning)) initialized generation signing kemBound keygenBound encapBound registrationBound peerBound bytesBound packetsBound representation correct functional candidate fallback
  have fair := RegistrationNativePlatformG3UniformRecordObserverIdeal.lor_of_selected
    setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous filter guess target designation
  constructor
  · have bound := (into true).trans (add_le_add (fair.le.trans (mul_le_mul' le_rfl (back false))) le_rfl)
    simpa only [mul_add,add_assoc,add_comm,add_left_comm] using bound
  · have scaled := mul_le_mul' (le_refl (2⁻¹ : ℝ≥0∞)) (into false)
    rw [mul_add] at scaled
    have bound := scaled.trans (add_le_add (fair.ge.trans (back true)) le_rfl)
    simpa only [add_assoc,add_comm,add_left_comm] using bound
end Lor

section App
variable (claim : Value → Option (Nat × Pqxdh.Bytes))
local notation "observe(" winning ")" => (Bool.rec
  (fun actual => RegistrationNativeCanonicalSelector.selected setup.source.crypto canonical serverKeyId budget claim target (Prod.fst actual) (Prod.snd actual))
  (RegistrationNativeCanonicalCoverage.decision setup.source.crypto canonical serverKeyId budget claim target) winning)
local notation "real(" winning "," representation ")" => RegistrationNativePlatformOrdinaryObserverSecurity.real setup checks wire route source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds PqxdhDeploymentInterface.Mode.P adversary budget previous (observe(winning)) representation
local notation "ideal(" winning ")" => RegistrationNativePlatformOrdinaryObserverSecurity.ideal setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds PqxdhDeploymentInterface.Mode.P adversary budget selected previous (observe(winning))
local notation "loss(" winning ")" => RegistrationNativePlatformConcreteObserverSecurity.loss setup checks route source ensureInit identityIndex serverKeyId selectedAccept view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds PqxdhDeploymentInterface.Mode.P adversary budget selected previous qInit qGenerate qSign qKem qKeygen qEncap caps (observe(winning)) fallback

include bounded in
/-- The fresh-byte target returns its selector to the same original source game before any target sum. -/
theorem fresh_bytes_of_claimed
    (initialized : (ensureInit.run ()).IsTotalQueryBound qInit)
    (generation : source.generate.IsTotalQueryBound qGenerate)
    (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (kemBound : ∀ (parameters : Sample KemSK (budget.cap 4+budget.cap 5)) query before,
      ((RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem (Fin.val selected) parameters.profile.pairs parameters.profile.publicKey parameters.profile.challenge parameters.candidate query).run before).IsTotalQueryBound qKem)
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

    (designation : ∀ (parameters : Sample KemSK cap) (observed : TraceView), (parameters,observed) ∈ support traced →
      ∀ finished ∈ observed.result,
        RegistrationNativePrekeyEvents.GoodAt setup.source.crypto canonical serverKeyId budget target claim (finished.2.1.1,(finished.2.1.2,())) →
        RegistrationNativeInstallTarget.Claimed claim finished.2.1.1 finished.2.1.2 finished.2.2.2.events
          (RegistrationNativePlatformInstallKernelStorage.Selected setup parameters.seed parameters.scalar parameters.candidate)) :
    𝒟[real(true,representation)] {true} ≤ ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ * 𝒟[real(false,representation)] {true} +
      loss(true) + ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ * loss(false) := by
  have into := RegistrationNativePlatformConcreteObserverSecurity.forward setup checks route source ensureInit identityIndex serverKeyId selectedAccept view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds PqxdhDeploymentInterface.Mode.P adversary budget bounded selected previous qInit qGenerate qSign qKem qKeygen qEncap caps (observe(true)) initialized generation signing kemBound keygenBound encapBound registrationBound peerBound bytesBound packetsBound representation correct functional candidate fallback
  have back := RegistrationNativePlatformConcreteObserverSecurity.reverse setup checks route source ensureInit identityIndex serverKeyId selectedAccept view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds PqxdhDeploymentInterface.Mode.P adversary budget bounded selected previous qInit qGenerate qSign qKem qKeygen qEncap caps (observe(false)) initialized generation signing kemBound keygenBound encapBound registrationBound peerBound bytesBound packetsBound representation correct functional candidate fallback
  have entropy := RegistrationNativePlatformG3UniformRecordObserverIdeal.fresh_bytes_of_claimed
    setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous claim target designation
  have bound := into.trans (add_le_add (entropy.trans (mul_le_mul' le_rfl back)) le_rfl)
  simpa only [Bool.false_eq_true,ite_true,ite_false,mul_add,add_assoc,add_comm,add_left_comm] using bound
end App
end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTargetComparison

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTargetComparison.lor_of_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTargetComparison.lor_of_selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTargetComparison.fresh_bytes_of_claimed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTargetComparison.fresh_bytes_of_claimed
