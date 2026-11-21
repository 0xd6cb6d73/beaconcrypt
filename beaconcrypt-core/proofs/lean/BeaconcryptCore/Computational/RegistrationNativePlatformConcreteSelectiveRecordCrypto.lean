-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceCrypto
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteEntropyFrame
import BeaconcryptCore.Computational.RegistrationNativePrimitiveCosts
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSelectiveRecordCrypto
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec coinLift effectLift)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePlatformSelectiveEntropyEnvironment (State)
open RegistrationNativePlatformSelectiveEntropyEffects (close close_run effect_source)
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK ProviderState Platform E Secret Reader Response Value : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (checks : Checks)
    (source : RegistrationNativeMldsa.Source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveBytes : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))




open PqxdhRecordLiftBudget (RecordKind WorldRecord recordBudget)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
variable (previous : Platform) (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
variable (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)


local notation "wire" => RegistrationNativePlatformConcreteSource.wire
local notation "allocation" => RegistrationNativePlatformConcreteSource.rawAllocation reserveBytes
local notation "reserveFrame" => reserveBytes
local notation "helper" => RegistrationNativePlatformConcreteSource.helper reserveBytes
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets

local notation "sourceProgram" => RegistrationNativePlatformSelectiveEntropyStartup.program (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary
local notation "referenceProgram" => RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary


variable (qInit qGenerate qSign qKem : Nat) (caps : RegistrationNativePlatformPublicExternalCaps.Caps)
local notation "allowance" => RegistrationNativePlatformConcreteEntropyFrame.allowance qGenerate qSign qKem caps
/-- The actual concrete parser, helpers, allocators and writers have the ordered record comparison from individual primitive and platform cost bills, with the environment Frame and genuine startup bill derived internally. -/
theorem source_random_bound (route : RawCtxServerRouting.SenderDecoder)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (initialized : (ensureInit.run ()).IsTotalQueryBound qInit)
    (generation : source.generate.IsTotalQueryBound qGenerate)
    (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (kem : ∀ query before, ((provider query).run before).IsTotalQueryBound qKem)
    (registrationBound : ∀ before, (reserveRegistration.run before).IsTotalQueryBound caps.registration)
    (peerBound : ∀ before, (reservePeer.run before).IsTotalQueryBound caps.peer)
    (bytesBound : ∀ amount before, ((reserveBytes amount).run before).IsTotalQueryBound caps.bytes)
    (packetsBound : ∀ amount before, ((reservePackets amount).run before).IsTotalQueryBound caps.packet)
    (observe : RegistrationNativeRecordPackage.View n (State n KemSK ProviderState Platform source) Value → Bool)
    (hmac : PqxdhSecretInputKdf.HmacSha512)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal ((observe <$> RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route sourceProgram).boolDistance
      (observe <$> RegistrationNativeRecordPackage.ctx (fun _ => .random) setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route sourceProgram)) ≤
      RegistrationNativeRecordViewCrypto.chainLoss setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route referenceProgram budget observe hmac +
        RegistrationNativeRecordViewCrypto.authLoss setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route referenceProgram budget observe fallback
          (RegistrationNativePlatformSelectiveReferenceBills.programBill budget bounds allowance caps.bytes (qInit+32) qGenerate .hash) (RegistrationNativePlatformSelectiveReferenceBills.programBill budget bounds allowance caps.bytes (qInit+32) qGenerate .raw) +
        RegistrationNativeRecordViewCrypto.privacyLoss setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route referenceProgram budget observe := by
  apply RegistrationNativePlatformSelectiveReferenceCrypto.source_random_bound setup checks wire source seed scalar candidate provider selectedOwner selectedAccept
    view failure allocation reserveRegistration reservePeer reserveBytes erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary
    route budget bounded allowance ?_ caps.bytes bytesBound (qInit+32) qGenerate
    (RegistrationNativePrimitiveCosts.constructor_bound setup.joint ensureInit qInit initialized identityIndex serverKeyId) (RegistrationNativePrimitiveCosts.generation_bound source qGenerate generation) observe hmac correct fallback
  intro credential
  exact RegistrationNativePlatformConcreteEntropyFrame.frame setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept
    view failure reserveRegistration reservePeer reserveBytes reservePackets erased qGenerate qSign qKem caps generation signing kem
    registrationBound peerBound bytesBound packetsBound (pure none) 0 (by trivial)

end BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSelectiveRecordCrypto

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSelectiveRecordCrypto.source_random_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSelectiveRecordCrypto.source_random_bound
