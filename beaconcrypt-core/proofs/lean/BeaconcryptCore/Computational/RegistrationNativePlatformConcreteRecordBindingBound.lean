-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordBindingSource
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformConcreteRecordBindingBound
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
/-- The SAME complete physical sampler/startup/source cache has the original seal-times-shared-hash commitment bound. Concrete startup, external source and primitive bills are derived internally. -/
theorem conflict_bound
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
    𝒟[(fun result=>PqxdhRecordFactsBindingEvent.conflictEvent result.2) <$>
      (simulateQ (PqxdhRecordLiftIdeal.ctxInterpreter (fun _=>PqxdhRecordLiftIdeal.KeyMode.random) id setup codec)
        (RegistrationNativeRecordOriginProgram.program codec route work)).run PqxdhRecordLiftIdeal.CtxPrivate.initial] {true}≤
      ((budget.sends*(budget.sends+hashCap):Nat):ℝ≥0∞)/(2:ℝ≥0∞)^512 := by
  apply RegistrationNativeRecordBindingSource.conflict_bound (fun _=>PqxdhRecordLiftIdeal.KeyMode.random) id setup codec route work
    (fun _=>by decide) budget
    (RegistrationNativePlatformG3UniformRecordBounds.record_bounded setup checks wire source ensureInit identityIndex serverKeyId selectedAccept
      view failure allocation reserveRegistration reservePeer reserveBytes erased helper writer bounds mode adversary budget bounded selected previous) hashCap
  exact RegistrationNativePlatformG3UniformRecordBounds.program_categories setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
    view failure allocation reserveRegistration reservePeer reserveBytes erased helper writer bounds mode adversary budget bounded selected previous
    samplerCoins (RegistrationNativePlatformG3UniformSamplerBounds.sample_bound setup budget selected qKeygen qEncap keygenBound encapBound)
    allowance (fun parameters credential=>RegistrationNativePlatformConcreteEntropyFrame.frame setup checks wire source credential parameters.seed parameters.scalar parameters.candidate
      (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val parameters.profile.pairs parameters.profile.publicKey parameters.profile.challenge parameters.candidate)
      selected.val selectedAccept view failure reserveRegistration reservePeer reserveBytes reservePackets erased qGenerate qSign qKem caps
      generation signing (kemBound parameters) registrationBound peerBound bytesBound packetsBound (pure none) 0 (by trivial))
    caps.bytes bytesBound (qInit+32) qGenerate
    (RegistrationNativePrimitiveCosts.constructor_bound setup.joint ensureInit qInit initialized identityIndex serverKeyId)
    (RegistrationNativePrimitiveCosts.generation_bound source qGenerate generation) .hash
end BeaconcryptCore.Computational.RegistrationNativePlatformConcreteRecordBindingBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformConcreteRecordBindingBound.conflict_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformConcreteRecordBindingBound.conflict_bound
