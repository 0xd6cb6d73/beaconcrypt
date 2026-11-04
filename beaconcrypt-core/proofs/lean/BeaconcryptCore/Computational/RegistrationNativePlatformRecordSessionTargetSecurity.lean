-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargetSource
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargetSecurity
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
local notation "hashCap"=>RegistrationNativePlatformG3UniformRecordBounds.bill bounds budget samplerCoins allowance reserveCoins constructorCoins mlCoins PqxdhRecordLiftCtxProtocolBounds.BudgetKind.hash
noncomputable def recoveryLoss : ℝ≥0∞:=
  ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
    (RegistrationNativeSuffixKeyRecovery.adversary setup.source
      (RegistrationNativeSecretWordRecoveryCompiler.guesses
        (RegistrationNativePlatformRecordPartnerExposureWarm.client setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous))))+
    (budget.cap 4+budget.cap 5)*(256^160:ℝ≥0∞)⁻¹+(budget.cap 4+budget.cap 5)*(256^32:ℝ≥0∞)⁻¹
noncomputable def physicalLoss : ℝ≥0∞:=
  match kind with
  | .origin _=>budget.sends*(2*budget.receives*((2^512:Nat):ℝ≥0∞)⁻¹)
  | _=>((budget.sends*(budget.sends+hashCap):Nat):ℝ≥0∞)/(2:ℝ≥0∞)^512
noncomputable def loss (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) : ℝ≥0∞:=
  RegistrationNativePlatformRecordSessionTargetSource.loss setup checks route source ensureInit identityIndex serverKeyId view failure
    reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget target previous qInit qGenerate qSign qKem qKeygen qEncap caps kind fallback+
  recoveryLoss setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget target previous+
  physicalLoss bounds budget qInit qGenerate qSign qKem qKeygen qEncap caps kind
local notation "joint"=>RegistrationNativePlatformRecordPartnerJointUniform.joint setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous
local notation "unused"=>fun (_ : RegistrationNativeSuffixKeyPrf.Secret)=>RegistrationNativePlatformLorIdealSelected.unused (n:=budget.cap 4+budget.cap 5)
private def PhysicalBad (result : RegistrationNativeEntropyRun.Outcome
    (RegistrationNativePlatformSelectiveEntropyEnvironment.State (budget.cap 4+budget.cap 5) KemSK RegistrationNativeKemSwitchSource.Phase Platform source) Value ×
    (RegistrationNativePlatformPublicRecordSlots.State (budget.cap 4+budget.cap 5) ×RegistrationNativeG2Trace.State ×
      RegistrationNativePlatformLorIdealPhysical.State (budget.cap 4+budget.cap 5) (PqxdhRecordLiftIdeal.CtxPrivate (budget.cap 4+budget.cap 5)))) : Prop :=
  match kind with
  | .origin _=>PqxdhRecordLiftIdeal.UnpublishedAccept (RegistrationNativeWire.ledgerCodec wire) route
      (PqxdhRecordLiftIdeal.viewOf (RegistrationNativeRecordPackage.encode result.1,result.2.2.2.2.1) [])
  | _=>PqxdhRecordLiftIdeal.CrossAccept (RegistrationNativeWire.ledgerCodec wire) route
      (PqxdhRecordLiftIdeal.viewOf (RegistrationNativeRecordPackage.encode result.1,result.2.2.2.2.1) [])
include bounded in
private theorem physical_bound
    (initialized : (ensureInit.run ()).IsTotalQueryBound qInit)
    (generation : source.generate.IsTotalQueryBound qGenerate)
    (signing : ∀key request,(source.sign key request).IsTotalQueryBound qSign)
    (kemBound : ∀(parameters:Sample KemSK (budget.cap 4+budget.cap 5)) query before,
      ((RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem (Fin.val (Prod.snd target)) parameters.profile.pairs parameters.profile.publicKey parameters.profile.challenge parameters.candidate query).run before).IsTotalQueryBound qKem)
    (keygenBound : (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound : ∀publicKey,(simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps publicKey)).IsTotalQueryBound qEncap)
    (registrationBound : ∀before,(reserveRegistration.run before).IsTotalQueryBound caps.registration)
    (peerBound : ∀before,(reservePeer.run before).IsTotalQueryBound caps.peer)
    (bytesBound : ∀amount before,((reserveBytes amount).run before).IsTotalQueryBound caps.bytes)
    (packetsBound : ∀amount before,((reservePackets amount).run before).IsTotalQueryBound caps.packet) :
    Pr{let result←joint}[PhysicalBad route source budget kind result]≤
      physicalLoss bounds budget qInit qGenerate qSign qKem qKeygen qEncap caps kind := by
  cases kind with
  | origin direction=>
    exact RegistrationNativePlatformRecordJointOriginBound.joint_bound setup checks source view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      route ensureInit identityIndex serverKeyId selectedAccept bounds mode adversary budget bounded selected previous
  | receiver=>
    exact RegistrationNativePlatformRecordJointBindingBound.bound setup checks route source ensureInit identityIndex serverKeyId selectedAccept view failure
      reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget bounded selected previous
      qInit qGenerate qSign qKem qKeygen qEncap caps initialized generation signing kemBound keygenBound encapBound registrationBound peerBound bytesBound packetsBound
  | sender=>
    exact RegistrationNativePlatformRecordJointBindingBound.bound setup checks route source ensureInit identityIndex serverKeyId selectedAccept view failure
      reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget bounded selected previous
      qInit qGenerate qSign qKem qKeygen qEncap caps initialized generation signing kemBound keygenBound encapBound registrationBound peerBound bytesBound packetsBound
include bounded in
/-- The unchanged ideal public target event pays one physical record loss and one actual complete-prefix recovery client, with no supplied designation, slot or exposure inclusion. -/
theorem ideal_bound
    (initialized : (ensureInit.run ()).IsTotalQueryBound qInit)
    (generation : source.generate.IsTotalQueryBound qGenerate)
    (signing : ∀key request,(source.sign key request).IsTotalQueryBound qSign)
    (kemBound : ∀(parameters:Sample KemSK (budget.cap 4+budget.cap 5)) query before,
      ((RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem (Fin.val (Prod.snd target)) parameters.profile.pairs parameters.profile.publicKey parameters.profile.challenge parameters.candidate query).run before).IsTotalQueryBound qKem)
    (keygenBound : (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound : ∀publicKey,(simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps publicKey)).IsTotalQueryBound qEncap)
    (registrationBound : ∀before,(reserveRegistration.run before).IsTotalQueryBound caps.registration)
    (peerBound : ∀before,(reservePeer.run before).IsTotalQueryBound caps.peer)
    (bytesBound : ∀amount before,((reserveBytes amount).run before).IsTotalQueryBound caps.bytes)
    (packetsBound : ∀amount before,((reservePackets amount).run before).IsTotalQueryBound caps.packet)
    (filler : PqxdhServerAuthKeySchedule.Output) :
    𝒟[RegistrationNativePlatformRecordSessionTargetSource.ideal setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget target previous kind] {true}≤
      recoveryLoss setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget target previous+physicalLoss bounds budget qInit qGenerate qSign qKem qKeygen qEncap caps kind := by
  have included:=RegistrationNativePlatformRecordSessionWordBound.bound setup checks route source ensureInit identityIndex serverKeyId
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets bounds mode adversary budget target previous bounded kind
  have physical:=physical_bound setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget bounded target previous qInit qGenerate qSign qKem qKeygen qEncap caps kind initialized generation signing kemBound keygenBound encapBound registrationBound peerBound bytesBound packetsBound
  have exposed:=RegistrationNativePlatformRecordPartnerExposureWarm.bound setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous unused filler bounded
  have total:=included.trans (add_le_add physical exposed)
  unfold RegistrationNativePlatformRecordSessionWordBound.Pinned at total
  rw [←prEvent_eq_evalDist_singleton,RegistrationNativePlatformRecordSessionTargetSource.ideal,prEvent_map]
  simpa only [recoveryLoss,add_comm] using total
include bounded in
/-- Original pin-filtered record targets have the explicit primitive, recovery and physical-record bound on the literal initialized profile. -/
theorem bound
    (initialized : (ensureInit.run ()).IsTotalQueryBound qInit)
    (generation : source.generate.IsTotalQueryBound qGenerate)
    (signing : ∀key request,(source.sign key request).IsTotalQueryBound qSign)
    (kemBound : ∀(parameters:Sample KemSK (budget.cap 4+budget.cap 5)) query before,
      ((RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem (Fin.val (Prod.snd target)) parameters.profile.pairs parameters.profile.publicKey parameters.profile.challenge parameters.candidate query).run before).IsTotalQueryBound qKem)
    (keygenBound : (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound : ∀publicKey,(simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps publicKey)).IsTotalQueryBound qEncap)
    (registrationBound : ∀before,(reserveRegistration.run before).IsTotalQueryBound caps.registration)
    (peerBound : ∀before,(reservePeer.run before).IsTotalQueryBound caps.peer)
    (bytesBound : ∀amount before,((reserveBytes amount).run before).IsTotalQueryBound caps.bytes)
    (packetsBound : ∀amount before,((reservePackets amount).run before).IsTotalQueryBound caps.packet)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (filler : PqxdhServerAuthKeySchedule.Output) :
    𝒟[RegistrationNativePlatformRecordSessionTargetSource.real setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget target previous kind representation] {true}≤
      loss setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget target previous qInit qGenerate qSign qKem qKeygen qEncap caps kind fallback := by
  have sourceBound:=RegistrationNativePlatformRecordSessionTargetSource.forward setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget bounded target previous qInit qGenerate qSign qKem qKeygen qEncap caps kind initialized generation signing kemBound keygenBound encapBound registrationBound peerBound bytesBound packetsBound representation correct functional candidate fallback
  have idealBound:=ideal_bound setup checks route source ensureInit identityIndex serverKeyId view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget bounded target previous qInit qGenerate qSign qKem qKeygen qEncap caps kind initialized generation signing kemBound keygenBound encapBound registrationBound peerBound bytesBound packetsBound filler
  have lifted:=add_le_add idealBound (le_refl (RegistrationNativePlatformRecordSessionTargetSource.loss setup checks route source ensureInit identityIndex serverKeyId
    view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget target previous qInit qGenerate qSign qKem qKeygen qEncap caps kind fallback))
  exact sourceBound.trans (by simpa only [loss,add_assoc,add_comm,add_left_comm] using lifted)
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargetSecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargetSecurity.ideal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargetSecurity.ideal_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargetSecurity.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargetSecurity.bound
