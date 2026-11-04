-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteRecordBindingBound
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordJointConflictSource
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordBounds
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordJointBindingBound
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicRecordOpaqueInitialized (Context prior)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (selectedAccept : Nat)
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
    (selected : Fin (budget.create + 1)) (previous : Platform)
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
local notation "codec"=>RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
local notation "hashCap"=>RegistrationNativePlatformG3UniformRecordBounds.bill bounds budget samplerCoins allowance reserveCoins constructorCoins mlCoins PqxdhRecordLiftCtxProtocolBounds.BudgetKind.hash

include bounded in
/-- The actual complete joint record run has the concrete cross-handle commitment bound, with the same physical sampler and all primitive and source resource bills derived internally. -/
theorem bound
    (initialized : (ensureInit.run ()).IsTotalQueryBound qInit)
    (generation : source.generate.IsTotalQueryBound qGenerate)
    (signing : ∀key request,(source.sign key request).IsTotalQueryBound qSign)
    (kemBound : ∀(parameters:Sample KemSK (budget.cap 4+budget.cap 5)) query before,
      ((RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val parameters.profile.pairs parameters.profile.publicKey parameters.profile.challenge parameters.candidate query).run before).IsTotalQueryBound qKem)
    (keygenBound : (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound : ∀publicKey,(simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps publicKey)).IsTotalQueryBound qEncap)
    (registrationBound : ∀before,(reserveRegistration.run before).IsTotalQueryBound caps.registration)
    (peerBound : ∀before,(reservePeer.run before).IsTotalQueryBound caps.peer)
    (bytesBound : ∀amount before,((reserveBytes amount).run before).IsTotalQueryBound caps.bytes)
    (packetsBound : ∀amount before,((reservePackets amount).run before).IsTotalQueryBound caps.packet) :
    Pr{let result←(RegistrationNativePlatformRecordPartnerJointUniform.joint setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous)}[
      PqxdhRecordLiftIdeal.CrossAccept codec route
        (PqxdhRecordLiftIdeal.viewOf (RegistrationNativeRecordPackage.encode result.1,result.2.2.2.2.1) [])]≤
      ((budget.sends*(budget.sends+hashCap):Nat):ℝ≥0∞)/(2:ℝ≥0∞)^512 := by
  classical
  have sourceLaw:=RegistrationNativePlatformRecordJointConflictSource.conflict_source setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous
  have probability:=congrArg (fun game=>𝒟[game] {true}) sourceLaw
  have rawBound:=RegistrationNativePlatformConcreteRecordBindingBound.conflict_bound setup checks route source ensureInit identityIndex serverKeyId selectedAccept
    view failure reserveRegistration reservePeer reserveBytes erased reservePackets bounds mode adversary budget bounded selected previous
    qInit qGenerate qSign qKem qKeygen qEncap caps initialized generation signing kemBound keygenBound encapBound registrationBound peerBound bytesBound packetsBound
  calc
    _≤Pr{let result←(RegistrationNativePlatformRecordPartnerJointUniform.joint setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous)}[
          PqxdhRecordFactsBindingEvent.conflictEvent result.2.2.2.2.2=true] := by
      apply prEvent_mono_of_support
      intro result supported crossed
      have conflicted:=RegistrationNativePlatformRecordJointConflictSource.cross_conflict setup checks route source ensureInit identityIndex serverKeyId selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous result supported crossed
      exact decide_eq_true conflicted
    _=𝒟[(fun result=>PqxdhRecordFactsBindingEvent.conflictEvent result.2.2.2.2.2) <$>
      RegistrationNativePlatformRecordPartnerJointUniform.joint setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous] {true} := by
      rw [←prEvent_eq_evalDist_singleton,prEvent_map]
    _≤_:=probability.trans_le rawBound
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordJointBindingBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordJointBindingBound.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordJointBindingBound.bound
