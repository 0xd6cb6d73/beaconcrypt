-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxResourceSecurity
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerNative
/-! Simultaneous staged-content agreement of the literal original initialized runtime now pays its one concrete warm-cache birthday term. The ordinary generated-key ML-EUF family and actual same-run KEM failure term are retained, with no additional owner union or perfect KEM correctness. -/
open OracleComp OracleSpec CoreModels ENNReal Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerConcreteBound
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformKemInitializedJournal (History)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value AD PT CT : Type} {base : OracleSpec ι}

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (source : RegistrationNativeMldsa.Source)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (rawAllocation : alloc.vec.Vec U8 → Usize → StateT Platform ProbComp (RustM (core.result.Result Unit E)))
variable (serializer : U64 → U64 → Std.Array (Slice U8) 3#usize → Slice U8 → StateT Platform ProbComp (RustM (Usize × Slice U8)))
local notation "helper" => AdapterRecordRawBytes.helper rawAllocation serializer
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
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
  have prior := RegistrationNativePlatformOrdinaryAllOwnerNative.bound (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer reserveFrame erased rawAllocation serializer writer bounds mode adversary previous budget bounded functional crypto correct
  have collision := RegistrationNativePlatformIdentityCtxResourceSecurity.raw_bound (n := n) setup checks wire route representation source view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded
  exact prior.trans (add_le_add (add_le_add collision le_rfl) le_rfl)
end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerConcreteBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerConcreteBound.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerConcreteBound.bound
