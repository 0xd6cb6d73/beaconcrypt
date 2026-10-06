-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutReports

/-! The ordinary joint Ed25519/X25519 weak-EUF family and its complete query bills, instantiated at the selected raw-accept prefix program `AcceptCut.selected`. The address-free final-report event is bounded with coefficient one by the explicit sum over the `count + 1` generated identity positions. The source caps of the complete program discharge every cap premise; no owner address, field or report position is selected. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutEuf
open PqxdhJointIdentity PqxdhDynamicIdentityPool PqxdhServerAuthExperiment
open PqxdhDynamicIdentityReports PqxdhDynamicIdentityRouting PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhRegistrationJointRevealSchedule (Spec)
open PqxdhRegistrationJointAcceptCut (selected)
open PqxdhRegistrationJointFinalCandidate (client)
open PqxdhRegistrationJointNativeOriginBound (reduction)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhRegistrationJointIdentityUniform (total)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Reader Response X : Type}

/-- The selected prefix program inherits each of the fourteen source caps of the complete program. -/
theorem selected_certified (work : OracleComp (Spec KemSK) X) (index owner : Nat) (fallback : Pqxdh.Bytes)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    ∀ source, (selected work index owner fallback).IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source) :=
  fun source => PqxdhRegistrationJointAcceptCut.selected_bound work index owner fallback _ (budget source) (certified source)

/-- The address-free final-report failure of the selected prefix program is bounded by the ordinary joint-use weak-EUF family with coefficient one. The owner constant of `AcceptCut.selected` is never read by the event or by the reductions. -/
theorem selected_report_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (runtime : A) (index owner : Nat) (fallback : Pqxdh.Bytes)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (capacity : (if supplied.isNone then 1 else 0) + budget (.inl 1) ≤ count + 1)
    (dynamicFallback : DynamicForgery) (ordinaryFallback : Forgery) :
    letI := Classical.propDecidable
    𝒟[(fun result => decide (PqxdhRegistrationJointFinalReportEvent.Failure setup.joint codec result)) <$>
      PqxdhJointPhase1Reports.run setup.joint (count + 1)
        (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied (count + 1)
          (selected work index owner fallback) runtime)] {true} ≤
      ∑ target : Fin (count + 1), advantage setup.joint
        (reduction setup codec checks ensureInit supplied count (selected work index owner fallback) runtime
          dynamicFallback ordinaryFallback target) := by
  classical
  apply (PqxdhRegistrationJointFinalReportEvent.transport setup codec checks ensureInit supplied (count + 1)
    (selected work index owner fallback) runtime).trans
  have creates := PqxdhRegistrationJointFinalCandidate.reported_bound setup codec checks ensureInit supplied (count + 1)
    (selected work index owner fallback) runtime IsCreate _
    (PqxdhRegistrationJointReportCosts.initialized_creates setup codec checks ensureInit supplied (count + 1)
      (selected work index owner fallback) runtime budget (selected_certified work index owner fallback budget certified))
  rw [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map]
  exact PqxdhJointPhase1Reports.fieldOrigin_advantage_le_sum setup.joint count _ dynamicFallback ordinaryFallback
    (creates.mono capacity)

/-- Each reduction of the selected prefix makes at most `3 * qBundle` signing requests and at most `qFinish + qAccept` converted-DH requests. -/
theorem selected_service_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (runtime : A) (index owner : Nat) (fallback : Pqxdh.Bytes)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (dynamicFallback : DynamicForgery) (ordinaryFallback : Forgery) (target : Fin (count + 1))
    (jointPublic : PublicIdentity) (signing : Bool) :
    (reduction setup codec checks ensureInit supplied count (selected work index owner fallback) runtime
      dynamicFallback ordinaryFallback target jointPublic).IsQueryBoundP
      (IsClass (if signing then .sign else .staticDh))
      (if signing then 3 * budget (.inl 2) else budget (.inl 5) + budget (.inl 3)) :=
  PqxdhRegistrationJointNativeOriginBound.service_bound setup codec checks ensureInit supplied count
    (selected work index owner fallback) runtime budget (selected_certified work index owner fallback budget certified)
    dynamicFallback ordinaryFallback target jointPublic signing

/-- The client of the selected prefix with its terminal batch makes at most `(count + 1) * (qAccept + 1)` public candidate reports. -/
theorem selected_reports_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (runtime : A) (index owner : Nat) (fallback : Pqxdh.Bytes)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (client setup codec checks ensureInit supplied (count + 1) (selected work index owner fallback) runtime).IsQueryBoundP
      PqxdhJointPhase1Reports.IsCandidateReport ((count + 1) * (budget (.inl 3) + 1)) :=
  PqxdhRegistrationJointFinalCandidate.reports_bound setup codec checks ensureInit supplied (count + 1)
    (selected work index owner fallback) runtime budget (selected_certified work index owner fallback budget certified)

/-- The client of the selected prefix pays at most the complete all-reply uniform bill `total caps qInit budget`. -/
theorem selected_client_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : KemCaps) (bounded : KemBound setup caps) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (runtime : A) (index owner : Nat) (fallback : Pqxdh.Bytes)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (client setup codec checks ensureInit supplied (count + 1) (selected work index owner fallback) runtime).IsQueryBoundP
      (PqxdhJointPhase1Reports.SourceClass (dynamicClass (IsClass .uniform))) (total caps qInit budget) :=
  PqxdhRegistrationJointNativeOriginUniform.client_bound setup codec checks ensureInit qInit initBound caps bounded
    supplied (count + 1) (selected work index owner fallback) runtime budget
    (selected_certified work index owner fallback budget certified)

/-- Each reduction of the selected prefix pays the other `count` reserved identity seeds and the complete client uniform bill. -/
theorem selected_reduction_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : KemCaps) (bounded : KemBound setup caps) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (runtime : A) (index owner : Nat) (fallback : Pqxdh.Bytes)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (dynamicFallback : DynamicForgery) (ordinaryFallback : Forgery) (target : Fin (count + 1))
    (jointPublic : PublicIdentity) :
    (reduction setup codec checks ensureInit supplied count (selected work index owner fallback) runtime
      dynamicFallback ordinaryFallback target jointPublic).IsQueryBoundP
      (IsClass .uniform) (32 * count + total caps qInit budget) :=
  PqxdhRegistrationJointNativeOriginUniform.reduction_bound setup codec checks ensureInit qInit initBound caps bounded
    supplied count (selected work index owner fallback) runtime budget
    (selected_certified work index owner fallback budget certified) dynamicFallback ordinaryFallback target jointPublic

/-- The complete ordinary weak-EUF game of each reduction of the selected prefix also samples its own target seed, so all `count + 1` reserved seeds are paid. -/
theorem selected_game_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : KemCaps) (bounded : KemBound setup caps) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (runtime : A) (index owner : Nat) (fallback : Pqxdh.Bytes)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (dynamicFallback : DynamicForgery) (ordinaryFallback : Forgery) (target : Fin (count + 1)) :
    (game setup.joint (reduction setup codec checks ensureInit supplied count (selected work index owner fallback) runtime
      dynamicFallback ordinaryFallback target)).IsTotalQueryBound (32 * (count + 1) + total caps qInit budget) :=
  PqxdhRegistrationJointNativeOriginUniform.game_bound setup codec checks ensureInit qInit initBound caps bounded
    supplied count (selected work index owner fallback) runtime budget
    (selected_certified work index owner fallback budget certified) dynamicFallback ordinaryFallback target

end BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutEuf

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutEuf.selected_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutEuf.selected_certified

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutEuf.selected_report_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutEuf.selected_report_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutEuf.selected_service_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutEuf.selected_service_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutEuf.selected_reports_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutEuf.selected_reports_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutEuf.selected_client_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutEuf.selected_client_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutEuf.selected_reduction_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutEuf.selected_reduction_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutEuf.selected_game_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutEuf.selected_game_uniform
