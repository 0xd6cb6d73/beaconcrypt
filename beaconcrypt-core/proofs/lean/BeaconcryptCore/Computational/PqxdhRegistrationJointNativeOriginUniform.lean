-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginBound
import BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform

/-! The actual native-origin reductions pay the complete all-reply client uniform bill and the ordinary family reservation cost. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginUniform
open PqxdhJointIdentity PqxdhDynamicIdentityPool PqxdhServerAuthExperiment
open PqxdhDynamicIdentityReports PqxdhDynamicIdentityRouting PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhRegistrationJointFinalCandidate (Choice client)
open PqxdhRegistrationJointNativeOriginBound (reduction)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhRegistrationJointIdentityUniform (total)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Reader Response : Type}

/-- Both source coin routes become the ordinary endpoint's explicit uniform class. -/
theorem uniform_class (query : DynamicSpec.Domain) :
    PqxdhRegistrationJointIdentityCosts.dynamicKind query = .uniform ↔
      dynamicClass (IsClass .uniform) query := by
  rcases query with coin | request
  · simp [PqxdhRegistrationJointIdentityCosts.dynamicKind, dynamicClass, IsClass]
  · cases request
    case service index service => cases service <;>
      simp [PqxdhRegistrationJointIdentityCosts.dynamicKind, PqxdhRegistrationJointServiceCosts.poolClass,
        dynamicClass, IsClass]
    all_goals simp [PqxdhRegistrationJointIdentityCosts.dynamicKind, PqxdhRegistrationJointServiceCosts.poolClass,
      dynamicClass]

/-- Source budgets supply the complete ordinary client's uniform cap, including the final public candidate batch. -/
theorem client_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : KemCaps) (bounded : KemBound setup caps) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Choice) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (client setup codec checks ensureInit supplied count program runtime).IsQueryBoundP
      (PqxdhJointPhase1Reports.SourceClass (dynamicClass (IsClass .uniform))) (total caps qInit budget) := by
  have original := PqxdhRegistrationJointIdentityUniform.initialized setup codec checks ensureInit qInit initBound
    caps bounded supplied program runtime budget certified
  exact PqxdhRegistrationJointFinalCandidate.client_bound setup codec checks ensureInit supplied count program runtime
    _ _ ((isQueryBoundP_congr_pred uniform_class).mp original)

/-- Each explicit one-identity reduction pays the other N-1 reserved identity seeds in addition to all actual local compiler work, for any challenger public identity. -/
theorem reduction_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : KemCaps) (bounded : KemBound setup caps) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Choice) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (fallback : DynamicForgery) (ordinaryFallback : Forgery) (target : Fin (count + 1)) (jointPublic : PublicIdentity) :
    (reduction setup codec checks ensureInit supplied count program runtime fallback ordinaryFallback target jointPublic).IsQueryBoundP
      (IsClass .uniform) (32 * count + total caps qInit budget) := by
  exact PqxdhJointPhase1Reports.fieldReduction_query_bound setup.joint count target fallback ordinaryFallback
    (client setup codec checks ensureInit supplied (count + 1) program runtime) .uniform _
    (client_bound setup codec checks ensureInit qInit initBound caps bounded supplied (count + 1) program runtime budget certified) jointPublic

/-- The complete ordinary weak-EUF endpoint additionally samples its private target identity, so all N reserved seeds are included. -/
theorem game_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : KemCaps) (bounded : KemBound setup caps) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Choice) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (fallback : DynamicForgery) (ordinaryFallback : Forgery) (target : Fin (count + 1)) :
    (game setup.joint (reduction setup codec checks ensureInit supplied count program runtime fallback ordinaryFallback target)).IsTotalQueryBound
      (32 * (count + 1) + total caps qInit budget) :=
  PqxdhJointPhase1Reports.fieldReductionGame_uniform_bound setup.joint count target fallback ordinaryFallback
    (client setup codec checks ensureInit supplied (count + 1) program runtime) _
    (client_bound setup codec checks ensureInit qInit initBound caps bounded supplied (count + 1) program runtime budget certified)

end BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginUniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginUniform.uniform_class' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginUniform.uniform_class

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginUniform.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginUniform.client_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginUniform.reduction_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginUniform.reduction_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginUniform.game_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginUniform.game_bound
