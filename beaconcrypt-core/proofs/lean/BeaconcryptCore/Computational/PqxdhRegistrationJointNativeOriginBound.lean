-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginEvent

/-! Construct the ordinary joint Ed25519/X25519 reductions for the actual chosen native tuple-origin event. The generated-index sum is explicit and there is no field or stopping-position loss. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginBound
open PqxdhJointIdentity PqxdhDynamicIdentityPool PqxdhServerAuthExperiment
open PqxdhDynamicIdentityReports PqxdhDynamicIdentityRouting PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhRegistrationJointFinalCandidate (Choice client)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Reader Response : Type}

/-- The actual initialized adaptive source client and its final original candidate feed the existing first-fresh-report and ordinary generated-identity reduction. -/
noncomputable def reduction (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Choice) (runtime : A)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery) (target : Fin (count + 1)) :=
  globalReduction setup.joint target ordinaryFallback
    (routedAdversary count ordinaryFallback
      (reportExtractor setup.joint (count + 1) fallback
        (PqxdhJointPhase1Reports.routedClient setup.joint (count + 1)
          (client setup codec checks ensureInit supplied (count + 1) program runtime))))

/-- Complete-tuple origin at the actual addressed generated source owner reduces to the explicit ordinary joint-use target family. Actual source budgets discharge creation capacity; imported candidates, rejection and compromise are retained without an honest-target premise. -/
theorem native_origin_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Choice) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (capacity : (if supplied.isNone then 1 else 0) + budget (.inl 1) ≤ count + 1)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery) :
    letI := Classical.propDecidable
    𝒟[(fun result => decide (PqxdhRegistrationJointNativeOriginEvent.Failure setup codec result)) <$>
      PqxdhJointPhase1Reports.run setup.joint (count + 1)
        (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied (count + 1) program runtime)] {true} ≤
      ∑ target : Fin (count + 1), advantage setup.joint
        (reduction setup codec checks ensureInit supplied count program runtime fallback ordinaryFallback target) := by
  classical
  apply (PqxdhRegistrationJointNativeOriginEvent.transport setup codec checks ensureInit supplied (count + 1) program runtime).trans
  have creates := PqxdhRegistrationJointFinalCandidate.reported_bound setup codec checks ensureInit supplied (count + 1)
    program runtime IsCreate _
    (PqxdhRegistrationJointReportCosts.initialized_creates setup codec checks ensureInit supplied (count + 1) program runtime budget certified)
  rw [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map]
  exact PqxdhJointPhase1Reports.fieldOrigin_advantage_le_sum setup.joint count _ fallback ordinaryFallback (creates.mono capacity)

/-- Each ordinary reduction preserves the source-derived signing and converted-DH caps. Public terminal reporting adds neither private operation. -/
theorem service_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Choice) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (fallback : DynamicForgery) (ordinaryFallback : Forgery) (target : Fin (count + 1))
    (jointPublic : PublicIdentity) (signing : Bool) :
    (reduction setup codec checks ensureInit supplied count program runtime fallback ordinaryFallback target jointPublic).IsQueryBoundP
      (IsClass (if signing then .sign else .staticDh))
      (if signing then 3 * budget (.inl 2) else budget (.inl 5) + budget (.inl 3)) := by
  have prior := PqxdhRegistrationJointReportCosts.initialized_private setup codec checks ensureInit supplied (count + 1)
    program runtime budget certified (if signing then .signing else .staticDh) (by cases signing <;> decide)
  have source := PqxdhRegistrationJointFinalCandidate.reported_bound setup codec checks ensureInit supplied (count + 1)
    program runtime _ _ prior
  have bounded := PqxdhJointPhase1Reports.fieldReduction_query_bound setup.joint count target fallback ordinaryFallback
    (client setup codec checks ensureInit supplied (count + 1) program runtime)
    (if signing then .sign else .staticDh) _
    ((isQueryBoundP_congr_pred (PqxdhRegistrationJointReportedAuthentication.service_class signing)).mp source) jointPublic
  cases signing <;> simpa only [Bool.false_eq_true, ite_false, ite_true,
    PqxdhRegistrationJointOpenCosts.privateTotal, reduceCtorEq, false_and, Nat.zero_add, reduction] using bounded

end BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginBound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginBound.native_origin_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginBound.native_origin_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginBound.service_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginBound.service_bound
