-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds
import BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateStoppedBounds

/-! The ordinary-EUF adversary's external signing-query cap is derived from the original raw native command contract. Startup and creation do not sign; each bundle or response build contributes at most one complete request, and stopping never increases this bill. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaSignStoppedBounds
open Classical
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativeMldsaSignBounds (IsSigningCallback)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)

private theorem union_bound {Query Result : Type} {queries : OracleSpec Query}
    (work : OracleComp queries Result) (left right : Query → Prop)
    [DecidablePred left] [DecidablePred right] (leftCount rightCount : Nat)
    (first : work.IsQueryBoundP left leftCount) (second : work.IsQueryBoundP right rightCount) :
    work.IsQueryBoundP (fun query => left query ∨ right query) (leftCount + rightCount) := by
  induction work using OracleComp.inductionOn generalizing leftCount rightCount with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at first second ⊢
      refine ⟨?_, fun reply => ?_⟩
      · by_cases activeLeft : left query
        · exact Or.inr (by have := first.1.resolve_left (not_not.mpr activeLeft); omega)
        · by_cases activeRight : right query
          · exact Or.inr (by have := second.1.resolve_left (not_not.mpr activeRight); omega)
          · exact Or.inl (by simp only [activeLeft, activeRight, or_self, not_false_eq_true])
      · apply (ih reply _ _ (first.2 reply) (second.2 reply)).mono
        have positiveLeft : left query → 0 < leftCount := fun active => first.1.resolve_left (not_not.mpr active)
        have positiveRight : right query → 0 < rightCount := fun active => second.1.resolve_left (not_not.mpr active)
        by_cases activeLeft : left query <;> by_cases activeRight : right query <;>
          simp only [activeLeft, activeRight, ite_true, ite_false, true_or, false_or, true_implies, false_implies] at positiveLeft positiveRight ⊢ <;> omega

private theorem wrap_bundle (bounds : PqxdhDeploymentInterface.FreshBounds) (budget : PqxdhDeploymentInterface.Budget) :
    (∑ full, PqxdhDeploymentCompileSecrecy.wrapCost bounds (2 : Fin 12) full * budget.cap full) = budget.bundle := by
  have cost (full : Fin 14) : PqxdhDeploymentCompileSecrecy.wrapCost bounds (2 : Fin 12) full = if full = (2 : Fin 14) then 1 else 0 := by
    fin_cases full <;> rfl
  simp [cost, PqxdhDeploymentInterface.Budget.cap]

private theorem wrap_build (bounds : PqxdhDeploymentInterface.FreshBounds) (budget : PqxdhDeploymentInterface.Budget) :
    (∑ full, PqxdhDeploymentCompileSecrecy.wrapCost bounds (4 : Fin 12) full * budget.cap full) = budget.build := by
  have cost (full : Fin 14) : PqxdhDeploymentCompileSecrecy.wrapCost bounds (4 : Fin 12) full = if full = (4 : Fin 14) then 1 else 0 := by
    fin_cases full <;> rfl
  simp [cost, PqxdhDeploymentInterface.Budget.cap]

/-- The unchanged raw compiler contributes at most bundle+build signing-capable typed callbacks. -/
theorem compile_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (serverKid : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) :
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKid bounds mode work).IsQueryBoundP
      IsSigningCallback (budget.bundle + budget.build) := by
  have bundles := RegistrationNativeFullCompiler.compile_bound setup.source.crypto wire serverKid bounds mode work budget bounded (2 : Fin 12)
  have builds := RegistrationNativeFullCompiler.compile_bound setup.source.crypto wire serverKid bounds mode work budget bounded (4 : Fin 12)
  rw [wrap_bundle] at bundles
  rw [wrap_build] at builds
  exact union_bound _ _ _ _ _ bundles builds

/-- The complete actual initialized stopped program has no extra startup signature slot. -/
theorem program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (cap : Nat) (bounded : ∀ publicValue, (adversary publicValue).IsQueryBoundP IsSigningCallback cap)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : Std.U64)
    (publicKey : RegistrationNativeMldsaEuf.PublicKey) :
    (RegistrationNativeMldsaStoppedGame.program (n := n) source setup checks wire route representation adversary ensureInit identityIndex serverKid publicKey).IsQueryBoundP
      (RegistrationNativeMldsaEufTapeCosts.IsSign source) cap := by
  apply (isQueryBoundP_congr_pred (p := RegistrationNativeMldsaSignBounds.IsSign) (p' := RegistrationNativeMldsaEufTapeCosts.IsSign source)
    (fun query => by cases query with
      | inl coin => rfl
      | inr query => cases query <;> rfl)).mp
  unfold RegistrationNativeMldsaStoppedGame.program
  rw [← Nat.zero_add cap]
  apply isQueryBoundP_bind (n := 0) (m := cap)
    (RegistrationNativeMldsaSignBounds.start (n := n) (source := handleSource source) setup ensureInit identityIndex serverKid)
  intro initialized _
  cases initialized with
  | none => trivial
  | some initial =>
    rw [RegistrationNativeMldsaStoppedGame.continued, isQueryBoundP_map_iff]
    exact RegistrationNativeMldsaSignBounds.stopped setup checks wire route representation initial.created initial.credential
      _ RegistrationNativeMldsaTableStop.defaultReply (adversary initial.public) cap (bounded initial.public) initial.state none

/-- Every original native observation mode gives qBundle+qBuild complete source signing slots. -/
theorem compiled (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : Std.U64)
    (publicKey : RegistrationNativeMldsaEuf.PublicKey) :
    (RegistrationNativeMldsaStoppedGame.program (n := n) source setup checks wire route representation
      (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
      ensureInit identityIndex serverKid publicKey).IsQueryBoundP
      (RegistrationNativeMldsaEufTapeCosts.IsSign source) (budget.bundle + budget.build) := by
  apply program source setup checks wire route representation _ (budget.bundle + budget.build) _ ensureInit identityIndex serverKid publicKey
  intro publicValue
  exact compile_bound setup wire publicValue.serverKeyId bounds mode (adversary publicValue) budget (bounded publicValue)

/-- The actual selected-key ordinary-EUF reduction makes at most qBundle+qBuild external signing queries. -/
theorem reduction_signs (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : Std.U64)
    (target : Fin (budget.create + 1)) (publicKey : RegistrationNativeMldsaEuf.PublicKey) :
    (RegistrationNativeMldsaEufTapeReduction.adversary source target
      (RegistrationNativeMldsaStoppedGame.program (n := n) source setup checks wire route representation
        (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
        ensureInit identityIndex serverKid) publicKey).IsQueryBoundP
      RegistrationNativeMldsaChosen.IsSigning (budget.bundle + budget.build) :=
  RegistrationNativeMldsaEufTapeCosts.reduction_signs source target _ publicKey (budget.bundle + budget.build)
    (compiled source setup checks wire route representation bounds mode adversary budget bounded ensureInit identityIndex serverKid publicKey)
end BeaconcryptCore.Computational.RegistrationNativeMldsaSignStoppedBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignStoppedBounds.compile_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignStoppedBounds.compile_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignStoppedBounds.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignStoppedBounds.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignStoppedBounds.compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignStoppedBounds.compiled

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignStoppedBounds.reduction_signs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignStoppedBounds.reduction_signs
