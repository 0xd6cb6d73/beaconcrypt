-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaInitializedUnion
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaDynamicEuf

/-! The joint complete initialized true-count table protected unsigned-origin failure or final collision event is bounded by one literal final shared-cache collision event and one sum of ordinary generated-key ML signing advantages. Each reduction is executable from only its challenge public key, and the original raw-adversary creation budget determines the target family. Primitive security is invoked only through ordinary EUF advantages; no authentication, source-correspondence or event-coverage conclusion is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaUnionSecurity
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source)
variable {n : Nat} {ι KemSK Platform E V : Type} {base : OracleSpec ι}
variable (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable [primitive : AdapterSealPrimitive.Operations]
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (previous : Platform)

/-- The actual initialized protected native event has one final-cache collision charge and one ordinary primitive EUF advantage per permitted generation attempt. -/
theorem typed (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (cap : Nat) (bounded : ∀ publicValue, (adversary publicValue).IsQueryBoundP
      (fun query => RegistrationNativeRawAdapter.kind query = (1 : Fin 12)) cap)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    Pr{let bad ← (RegistrationNativePlatformMldsaInitializedUnion.badGame (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous
      ensureInit identityIndex serverKeyId)}[bad = true] ≤
      Pr{let collision ← (RegistrationNativePlatformMldsaInitializedUnion.collisionGame (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous
        ensureInit identityIndex serverKeyId)}[collision = true] +
      ∑ target : Fin (cap + 1), RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativePlatformMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous ensureInit identityIndex serverKeyId)) := by
  apply (RegistrationNativePlatformMldsaInitializedUnion.bound source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous cap bounded
    ensureInit identityIndex serverKeyId).trans
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro target _member
  exact RegistrationNativePlatformMldsaDynamicEuf.typed source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous
    ensureInit identityIndex serverKeyId cap bounded target

/-- The unchanged full raw-adversary resource contract supplies exactly budget.create+1 ordinary generated-key targets, in every native mode and through all actual failed source prefixes. -/
theorem compiled (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    Pr{let bad ← (RegistrationNativePlatformMldsaInitializedUnion.badGame (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer
      (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
      previous ensureInit identityIndex serverKeyId)}[bad = true] ≤
      Pr{let collision ← (RegistrationNativePlatformMldsaInitializedUnion.collisionGame (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer
        (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
        previous ensureInit identityIndex serverKeyId)}[collision = true] +
      ∑ target : Fin (budget.create + 1), RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativePlatformMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer
          (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
          previous ensureInit identityIndex serverKeyId)) := by
  apply typed source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer previous _ budget.create _ ensureInit identityIndex serverKeyId
  intro publicValue
  simpa only [RegistrationNativeIdentityProfileCreateCaps.wrap_create_sum] using
    RegistrationNativeFullCompiler.compile_bound setup.source.crypto wire publicValue.serverKeyId bounds mode
      (adversary publicValue) budget (bounded publicValue) (1 : Fin 12)
end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaUnionSecurity


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaUnionSecurity.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaUnionSecurity.typed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaUnionSecurity.compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaUnionSecurity.compiled
