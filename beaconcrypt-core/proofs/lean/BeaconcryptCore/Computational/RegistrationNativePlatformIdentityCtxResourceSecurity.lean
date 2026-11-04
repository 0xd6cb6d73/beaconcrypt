-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHashBounds
/-! The literal original initialized runtime pays one shared physical CTX birthday term with its concrete API resource bill. Actual startup supplies the warm cache, typed callbacks supply every future allowance, and the full public command compiler supplies every typed cap. No static hash-count or whole-controller resource premise remains. -/
open OracleComp OracleSpec CoreModels ENNReal Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxResourceSecurity
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (source : RegistrationNativeMldsa.Source)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)

/-- Concrete shared hash cap after the original full public command and fresh-byte compiler. -/
def hashBudget (fresh : FreshBounds) (budget : Budget) : Nat :=
  ∑ kind, RegistrationNativePlatformIdentityCtxTypedHashBounds.cost kind *
    (∑ full, PqxdhDeploymentCompileSecrecy.wrapCost fresh kind full * budget.cap full)

/-- The unchanged initialized typed runtime pays one warm-cache birthday term with derived concrete callback bills. -/
theorem typed_bound (adversary : RegistrationNativeExperiment.Public → OracleComp TypedSpec A)
    (previous : Platform) (caps : Fin 12 → Nat)
    (bounded : ∀ publicInput kind, (adversary publicInput).IsQueryBoundP
      (fun query => RegistrationNativeRawAdapter.kind query = kind) (caps kind)) :
    Pr{let collision ← (RegistrationNativePlatformOrdinaryMldsaOriginUnionSecurity.collisionGame (n := n) source setup checks wire route representation keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer adversary previous ensureInit identityIndex serverKeyId)}[collision = true] ≤
      (((∑ kind, RegistrationNativePlatformIdentityCtxTypedHashBounds.cost kind * caps kind) + 1).choose 2 : ℝ≥0∞) / (2 : ℝ≥0∞)^512 := by
  apply RegistrationNativePlatformIdentityCtxRuntimeBirthday.runtime_bound setup checks wire route representation keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId adversary previous
  intro initial _
  exact RegistrationNativePlatformIdentityCtxTypedHashBounds.program_bound setup checks wire route representation initial.created initial.credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer (adversary initial.public) caps (bounded initial.public)
    (RegistrationNativePlatformIdentityCtxInitial.fromInitial initial previous PqxdhDynamicIdentityPool.initialState).1

/-- The full raw deployment profile instantiates the same one-cache birthday bound without a native hash-cap premise. -/
theorem raw_bound (fresh : FreshBounds) (mode : Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (previous : Platform) (budget : Budget)
    (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput)) :
    Pr{let collision ← (RegistrationNativePlatformOrdinaryMldsaOriginUnionSecurity.collisionGame (n := n) source setup checks wire route representation keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer
      (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
        publicValue.serverKeyId fresh mode (adversary publicValue)) previous ensureInit identityIndex serverKeyId)}[collision = true] ≤
      ((hashBudget fresh budget + 1).choose 2 : ℝ≥0∞) / (2 : ℝ≥0∞)^512 :=
  typed_bound setup checks wire route representation source keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    ensureInit identityIndex serverKeyId _ previous _
    (fun publicValue => RegistrationNativeFullCompiler.compile_bound setup.source.crypto
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) publicValue.serverKeyId fresh mode
      (adversary publicValue) budget (bounded publicValue))
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxResourceSecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxResourceSecurity.typed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxResourceSecurity.typed_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxResourceSecurity.raw_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxResourceSecurity.raw_bound
