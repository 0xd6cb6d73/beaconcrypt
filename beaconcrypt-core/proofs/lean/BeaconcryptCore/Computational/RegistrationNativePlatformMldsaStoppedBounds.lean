-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaStoppedGame
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGenerateBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformStoppedBounds
import BeaconcryptCore.Computational.RegistrationNativeMldsaEager

/-! The actual initialized stopped source program fits the finite ordinary-EUF generation tape at qCreate+1. The bound counts every attempted named generation, including failures; actual key-generation/signing coin costs are irrelevant to this syntactic bill. The original raw-adversary compiler supplies qCreate without a caller program-bound premise. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaStoppedBounds
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaOpaque (handleSource)
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)

private theorem eager_iff (query : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Domain) :
    RegistrationNativeMldsaGenerateBounds.IsGenerate query ↔ RegistrationNativeMldsaEager.IsGenerate source query := by
  rcases query with coin | call
  · simp [RegistrationNativeMldsaGenerateBounds.IsGenerate, RegistrationNativeMldsaNoGenerate.Allowed, RegistrationNativeMldsaEager.IsGenerate]
  · cases call <;> simp [RegistrationNativeMldsaGenerateBounds.IsGenerate, RegistrationNativeMldsaNoGenerate.Allowed, RegistrationNativeMldsaEager.IsGenerate]

/-- The complete actual source startup plus early-stop original typed execution has at most cap+1 named generation attempts. -/
theorem program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    [primitive : AdapterSealPrimitive.Operations]
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (previous : Platform)
    (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (cap : Nat) (bounded : ∀ publicValue, (adversary publicValue).IsQueryBoundP
      (fun query => RegistrationNativeRawAdapter.kind query = (1 : Fin 12)) cap)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : Std.U64)
    (publicKey : RegistrationNativeMldsaEuf.PublicKey) :
    (RegistrationNativePlatformMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer adversary previous ensureInit identityIndex serverKid publicKey).IsQueryBoundP
      (RegistrationNativeMldsaEager.IsGenerate source) (cap + 1) := by
  apply (isQueryBoundP_congr_pred (eager_iff source)).mp
  unfold RegistrationNativePlatformMldsaStoppedGame.program
  rw [Nat.add_comm cap 1]
  apply isQueryBoundP_bind (RegistrationNativeMldsaGenerateBounds.start (n := n) (source := handleSource source) setup ensureInit identityIndex serverKid)
  intro initialized _
  cases initialized with
  | none => exact isQueryBoundP_pure _ _ _
  | some initial =>
    rw [RegistrationNativePlatformMldsaStoppedGame.continued, isQueryBoundP_map_iff]
    exact RegistrationNativePlatformStoppedBounds.stopped _ RegistrationNativeMldsaGenerateBounds.IsGenerate
      (RegistrationNativePlatformMldsaProfile.handler setup checks wire route representation initial.created initial.credential
        view failure allocation reserveRegistration reservePeer erased helper writer)
      (RegistrationNativePlatformMldsaGenerateBounds.handler setup checks wire route representation initial.created initial.credential
        view failure allocation reserveRegistration reservePeer erased helper writer)
      _ RegistrationNativeMldsaTableStop.defaultReply (adversary initial.public) cap (bounded initial.public) (initial.state, previous) none

/-- The unchanged full raw native adversary resource contract yields the finite selected-key tape cap qCreate+1 for every challenge public key. -/
theorem compiled (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    [primitive : AdapterSealPrimitive.Operations]
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (previous : Platform)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : Std.U64)
    (publicKey : RegistrationNativeMldsaEuf.PublicKey) :
    (RegistrationNativePlatformMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer
      (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
      previous ensureInit identityIndex serverKid publicKey).IsQueryBoundP
      (RegistrationNativeMldsaEager.IsGenerate source) (budget.create + 1) := by
  apply program source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer previous _ budget.create _ ensureInit identityIndex serverKid publicKey
  intro publicValue
  simpa only [RegistrationNativeIdentityProfileCreateCaps.wrap_create_sum] using
    RegistrationNativeFullCompiler.compile_bound setup.source.crypto wire publicValue.serverKeyId bounds mode
      (adversary publicValue) budget (bounded publicValue) (1 : Fin 12)

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaStoppedBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaStoppedBounds.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaStoppedBounds.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaStoppedBounds.compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaStoppedBounds.compiled
