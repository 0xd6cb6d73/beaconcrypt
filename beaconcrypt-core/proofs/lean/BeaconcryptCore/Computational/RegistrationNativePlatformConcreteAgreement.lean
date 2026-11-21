-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerConcreteBound
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource
/-! The simultaneous agreement endpoint fixes the actual source-backed registration Wire, source serializers and fixed-three helper. Public capacity reservations remain dynamic on the same P, including their failures. Every protected finish in the unchanged mandatory-ML initialized runtime has the existing complete staged-content partner subject to one shared birthday term, ordinary generated-key ML-EUF and actual same-run KEM failure. This is staged issuance and does not assert prior successful response publication. -/
open OracleComp OracleSpec CoreModels ENNReal Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformConcreteAgreement
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformKemInitializedJournal (History)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value AD PT CT : Type} {base : OracleSpec ι}

variable (setup : Setup base KemSK) (checks : Checks)
local notation "wire" => RegistrationNativePlatformConcreteSource.wire
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (source : RegistrationNativeMldsa.Source)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (reserveBytes : Nat → StateT Platform ProbComp (core.result.Result Unit E))
variable (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "rawAllocation" => RegistrationNativePlatformConcreteSource.rawAllocation reserveBytes
local notation "serializer" => RegistrationNativePlatformConcreteSource.serializer (Platform := Platform)
local notation "helper" => RegistrationNativePlatformConcreteSource.helper reserveBytes
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets
variable (bounds : FreshBounds) (mode : Mode)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
variable (previous : Platform)


variable (budget : Budget) (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))
variable (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)

include bounded functional in
/-- Every protected successful finish of every owner has an actual earlier same-run staged partner except for the concrete shared hash, ML-EUF and ordinary KEM losses. -/
theorem bound (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT) (correct : view.Correct) :
    Pr{let failed ← (RegistrationNativePlatformOrdinaryAllOwnerNative.game (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased
      rawAllocation serializer writer bounds mode adversary previous crypto)}[failed = true] ≤
      (((RegistrationNativePlatformIdentityCtxResourceSecurity.hashBudget bounds budget + 1).choose 2 : ℝ≥0∞) / (2 : ℝ≥0∞)^512 +
      ∑ target : Fin (budget.create + 1), RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativePlatformOrdinaryMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) publicValue.serverKeyId bounds mode (adversary publicValue))
          previous ensureInit identityIndex serverKeyId))) + budget.create * budget.accept * RegistrationNativeRecipientFailure.failureRate setup := by
  exact RegistrationNativePlatformOrdinaryAllOwnerConcreteBound.bound (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer reserveFrame erased rawAllocation serializer writer bounds mode adversary previous budget bounded functional crypto correct
end BeaconcryptCore.Computational.RegistrationNativePlatformConcreteAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformConcreteAgreement.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformConcreteAgreement.bound
