-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedExperiment
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedSecurity
/-! Original broad final-owner unsigned-tuple publication strictly before acceptance is transported to the exact current extracted source dictionary, with the identical ordinary joint-EUF loss and same original initialized event. SDK object composition remains separate. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryCausal
variable {Value : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable [BeaconcryptCore.Refinement.FrameDispatchFallback.Operations] [BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I}
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (CoreModels.core.result.Result Unit E)) (erased : beaconcrypt_core.commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (reserve : Usize → StateT Platform ProbComp (CoreModels.core.result.Result Unit E))

variable (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (previous : Platform)

local notation "wire" => RegistrationNativePlatformConcreteSource.wire
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reserve


variable (sealLength : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (openLength : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (edFunctional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)

include sealLength openLength converted edFunctional in
theorem causal_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication,RegistrationNativeInterface.Respects budget (adversary publication))
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length<64 → setup.source.crypto.verify publicKey.toList bytes=none)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (fallback : PqxdhJointIdentity.Forgery) :
    Pr{let result←((RegistrationNativePlatformExtractedExperiment.profile setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
        (RegistrationNativeIdentityOriginalCausalInitialized.event (n := n) setup wire source)).run previous)}[result.1=true] ≤
    RegistrationNativeIdentityUnissuedInitialized.loss (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous budget fallback+
    RegistrationNativeIdentityCensorIssuedSecurity.loss (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      source ensureInit identityIndex serverKeyId bounds mode adversary previous budget placeholder fallback := by
  rw [RegistrationNativePlatformExtractedExperiment.profile_source setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary _ sealLength openLength converted edFunctional]
  exact RegistrationNativeIdentityCensorIssuedSecurity.causal_bound setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded shortRejects placeholder fallback

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryCausal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryCausal.causal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryCausal.causal_bound
