-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicSource
import BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicBounds
import BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicEagerAbsent
import BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedEufBudget

/-! Each actual initialized dynamic protected-key monitor is reduced to an ordinary generated-key complete-request ML signing adversary. The source game receives only a generation ordinal; target-first sampling is applied before the observed key is learned. Failed selected generation contributes zero, and all successful branches preserve their literal source signing prefix. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicEuf
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource)
variable {n : Nat} {ι KemSK V : Type} {base : OracleSpec ι}
variable (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec V)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)

private noncomputable def reference {cap : Nat} (target : Fin (cap + 1)) : ProbComp Bool := do
  let generated ← RegistrationNativeMldsa.generate source
  let others ← RegistrationNativeMldsaEager.family source cap
  match generated with
  | none => pure false
  | some challenge => do
      let result ← (simulateQ (RegistrationNativeMldsaEager.handler source (List.ofFn (target.insertNth (some challenge) others)))
        (RegistrationNativeMldsaStoppedGame.program (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId challenge.publicKey)).run {}
      pure result.1.isSome

private theorem reference_eq {cap : Nat} (target : Fin (cap + 1)) :
    EvalDistEq (reference (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId target)
      (RegistrationNativeMldsaStoppedEuf.game (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId target) := by
  unfold reference RegistrationNativeMldsaStoppedEuf.game
  apply EvalDistEq.bind_right
  intro generated
  cases generated with
  | none => exact OracleComp.EvalDistEq.bind_const _ (pure false)
  | some challenge => rfl

/-- Every actual dynamic selected-generation monitor has the ordinary primitive EUF upper bound under its original typed creation resource contract. -/
theorem typed (cap : Nat) (bounded : ∀ publicValue, (adversary publicValue).IsQueryBoundP
    (fun query => RegistrationNativeRawAdapter.kind query = (1 : Fin 12)) cap) (target : Fin (cap + 1)) :
    Pr{let candidate ← (RegistrationNativeMldsaDynamicSource.game (n := n) source setup checks wire route representation adversary
      false target.val ensureInit identityIndex serverKeyId)}[candidate.isSome = true] ≤
      RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativeMldsaStoppedGame.program (n := n) source setup checks wire route representation adversary
          ensureInit identityIndex serverKeyId)) := by
  rw [RegistrationNativeMldsaDynamicSource.probability]
  rw [(RegistrationNativeMldsaDynamicBounds.target_first source setup checks wire route representation adversary cap bounded
    target ensureInit identityIndex serverKeyId).prEvent_eq (fun result => result.1.isSome = true)]
  have upper : Pr{let won ← (reference (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId target)}[won = true] ≤
      RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativeMldsaStoppedGame.program (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId)) := by
    rw [(reference_eq (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKeyId target).prEvent_eq (fun won => won = true)]
    exact RegistrationNativeMldsaStoppedEufBudget.typed source setup checks wire route representation adversary cap bounded
      ensureInit identityIndex serverKeyId target
  apply le_trans _ upper
  unfold reference
  apply prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _
  intro generated _possible
  apply prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _
  intro others _reserved
  have chosen : (List.ofFn (target.insertNth generated others))[target.val]? = some generated := by
    simp only [List.getElem?_ofFn, target.isLt, _root_.dite_true, Fin.eta, Fin.insertNth_apply_same]
  cases generated with
  | none =>
      rw [RegistrationNativeMldsaDynamicEagerAbsent.zero source setup checks wire route representation adversary target.val _ chosen]
      exact zero_le
  | some challenge =>
      dsimp only
      rw [bind_pure_comp, prEvent_map]
      exact RegistrationNativeMldsaDynamicEagerStartup.bound source setup checks wire route representation adversary
        target.val _ challenge chosen ensureInit identityIndex serverKeyId

/-- The original full raw-adversary contract gives the concrete per-ordinal ordinary EUF reduction for every native mode, with target range budget.create+1. -/
theorem compiled (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (rawAdversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (rawAdversary publicValue))
    (target : Fin (budget.create + 1)) :
    Pr{let candidate ← (RegistrationNativeMldsaDynamicSource.game (n := n) source setup checks wire route representation
      (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (rawAdversary publicValue))
      false target.val ensureInit identityIndex serverKeyId)}[candidate.isSome = true] ≤
      RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativeMldsaStoppedGame.program (n := n) source setup checks wire route representation
          (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (rawAdversary publicValue))
          ensureInit identityIndex serverKeyId)) := by
  apply typed source setup checks wire route representation _ ensureInit identityIndex serverKeyId budget.create _ target
  intro publicValue
  simpa only [RegistrationNativeIdentityProfileCreateCaps.wrap_create_sum] using
    RegistrationNativeFullCompiler.compile_bound setup.source.crypto wire publicValue.serverKeyId bounds mode
      (rawAdversary publicValue) budget (bounded publicValue) (1 : Fin 12)
end BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicEuf

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicEuf.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicEuf.typed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicEuf.compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicEuf.compiled
