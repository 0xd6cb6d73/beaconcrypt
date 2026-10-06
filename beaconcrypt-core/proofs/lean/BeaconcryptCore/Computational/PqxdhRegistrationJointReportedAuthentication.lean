-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointReportAttempts

/-! The existing ordinary joint-use weak-EUF reduction applied to the actual initialized registration client with original public candidate reports after successful raw acceptance. The generated-target sum is explicit; no field, report-position or session guessing factor is inserted. This remains a field-origin result, not full authenticated-root or whole-protocol secrecy. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointReportedAuthentication
open PqxdhJointIdentity PqxdhDynamicIdentityPool PqxdhServerAuthExperiment
open PqxdhDynamicIdentityReports PqxdhDynamicIdentityRouting PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Reader Response Result : Type}

/-- Each ordinary single-identity adversary is the actual public-report translator, first-fresh-report stopping client and generated-index family reduction. The target seed remains inside the ordinary joint-use challenger. -/
noncomputable def reduction (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery) (target : Fin (count + 1)) :=
  globalReduction setup.joint target ordinaryFallback
    (routedAdversary count ordinaryFallback
      (reportExtractor setup.joint (count + 1) fallback
        (PqxdhJointPhase1Reports.routedClient setup.joint (count + 1)
          (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied (count + 1) program runtime))))

/-- Fresh original-field reports from the actual initialized successful-accept experiment reduce to the explicit generated-identity sum. Actual all-reply source budgets discharge the creation premise; there is no honest selected-owner or public-key injectivity premise. -/
theorem field_origin_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (capacity : (if supplied.isNone then 1 else 0) + budget (.inl 1) ≤ count + 1)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery) :
    𝒟[(fun result => result.2.1.occurred) <$> PqxdhJointPhase1Reports.run setup.joint (count + 1)
        (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied (count + 1) program runtime)] {true} ≤
      ∑ target : Fin (count + 1), advantage setup.joint
        (reduction setup codec checks ensureInit supplied count program runtime fallback ordinaryFallback target) := by
  rw [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map]
  exact PqxdhJointPhase1Reports.fieldOrigin_advantage_le_sum setup.joint count _ fallback ordinaryFallback
    ((PqxdhRegistrationJointReportCosts.initialized_creates setup codec checks ensureInit supplied (count + 1)
      program runtime budget certified).mono capacity)

/-- The standard endpoint signing/DH classes match the actual source service partition exactly, including malformed/missing handles and report bookkeeping. -/
theorem service_class (signing : Bool) (query : PqxdhJointPhase1Reports.ProtocolSpec.Domain) :
    PqxdhJointPhase1Reports.SourceClass
      (fun request => PqxdhRegistrationJointIdentityCosts.dynamicKind request =
        (if signing then PqxdhRegistrationJointServiceCosts.Kind.signing else .staticDh)) query ↔
      PqxdhJointPhase1Reports.SourceClass (dynamicClass (IsClass (if signing then .sign else .staticDh))) query := by
  rcases query with (coin | request) | report
  · cases signing <;> simp [PqxdhJointPhase1Reports.SourceClass, PqxdhRegistrationJointIdentityCosts.dynamicKind, dynamicClass, IsClass]
  · cases request with
    | create => cases signing <;> simp [PqxdhJointPhase1Reports.SourceClass, PqxdhRegistrationJointIdentityCosts.dynamicKind,
        PqxdhRegistrationJointServiceCosts.poolClass, dynamicClass]
    | reveal index => cases signing <;> simp [PqxdhJointPhase1Reports.SourceClass, PqxdhRegistrationJointIdentityCosts.dynamicKind,
        PqxdhRegistrationJointServiceCosts.poolClass, dynamicClass]
    | service index request => cases request <;> cases signing <;>
        simp [PqxdhJointPhase1Reports.SourceClass, PqxdhRegistrationJointIdentityCosts.dynamicKind,
          PqxdhRegistrationJointServiceCosts.poolClass, dynamicClass, IsClass]
  · rfl

/-- Every constructed single-identity reduction makes at most three signing requests per source bundle attempt and one converted-DH request per accept or finish attempt. No identity-selection multiplier is charged to these per-reduction request caps. -/
theorem reduction_service_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (fallback : DynamicForgery) (ordinaryFallback : Forgery) (target : Fin (count + 1))
    (jointPublic : PublicIdentity) (signing : Bool) :
    (reduction setup codec checks ensureInit supplied count program runtime fallback ordinaryFallback target jointPublic).IsQueryBoundP
      (IsClass (if signing then .sign else .staticDh))
      (if signing then 3 * budget (.inl 2) else budget (.inl 5) + budget (.inl 3)) := by
  have source := PqxdhRegistrationJointReportCosts.initialized_private setup codec checks ensureInit supplied (count + 1)
    program runtime budget certified (if signing then .signing else .staticDh) (by cases signing <;> decide)
  have bounded := PqxdhJointPhase1Reports.fieldReduction_query_bound setup.joint count target fallback ordinaryFallback
    (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied (count + 1) program runtime)
    (if signing then .sign else .staticDh) _ ((isQueryBoundP_congr_pred (service_class signing)).mp source) jointPublic
  cases signing <;> simpa only [Bool.false_eq_true, ite_false, ite_true,
    PqxdhRegistrationJointOpenCosts.privateTotal, reduceCtorEq, false_and, Nat.zero_add, reduction] using bounded

end BeaconcryptCore.Computational.PqxdhRegistrationJointReportedAuthentication

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportedAuthentication.field_origin_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportedAuthentication.field_origin_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportedAuthentication.service_class' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportedAuthentication.service_class

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportedAuthentication.reduction_service_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportedAuthentication.reduction_service_bound
