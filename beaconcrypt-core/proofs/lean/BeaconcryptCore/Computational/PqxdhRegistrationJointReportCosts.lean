-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointReportSource

/-! Exact private capability preservation through original-candidate reporting, with explicit public report work. Reports have the fixed Unit reply and therefore cannot hide extra oracle branches or invalidate an all-reply cap. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointReportCosts
open PqxdhRegistrationJointReportLift (Spec erase)
variable {ι : Type} {source : OracleSpec ι} {Result : Type}

def original (predicate : source.Domain → Prop) : (Spec source).Domain → Prop
  | .inl query => predicate query
  | .inr _ => False
instance (predicate : source.Domain → Prop) [DecidablePred predicate] : DecidablePred (original predicate) :=
  fun query => by cases query <;> simp only [original] <;> infer_instance

/-- Bookkeeping erasure preserves each original oracle-class cap in both directions over every typed reply. -/
theorem erase_bound (predicate : source.Domain → Prop) [DecidablePred predicate]
    (program : OracleComp (Spec source) Result) (budget : Nat) :
    (simulateQ erase program).IsQueryBoundP predicate budget ↔
      program.IsQueryBoundP (original predicate) budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => simp
  | query_bind query next ih =>
      cases query with
      | inl query =>
          simp only [simulateQ_bind, simulateQ_spec_query, erase,
            isQueryBoundP_query_bind_iff, original, ih]
          rfl
      | inr report =>
          simp only [simulateQ_bind, simulateQ_spec_query, erase, pure_bind,
            isQueryBoundP_query_bind_iff, original, not_false_eq_true, true_or, true_and]
          change (simulateQ erase (next ())).IsQueryBoundP predicate budget ↔
            ∀ u : Unit, (next u).IsQueryBoundP (original predicate) budget
          constructor
          · intro bounded answer
            cases answer
            exact (ih () budget).mp bounded
          · intro bounded
            exact (ih () budget).mpr (bounded ())

variable {baseSpec : OracleSpec ι} {KemSK A Reader Response : Type}
open PqxdhServerAuthExperiment
open PqxdhRegistrationJointServiceCosts (Kind)

set_option backward.isDefEq.respectTransparency false in
/-- Every actual reported initialized client retains the earlier all-reply private capability bounds. Public target enumeration adds no identity creation, signature, converted-DH or reveal request. -/
theorem initialized_private (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (kind : Kind) (nonuniform : kind ≠ .uniform) :
    (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count program runtime).IsQueryBoundP
      (PqxdhJointPhase1Reports.SourceClass (fun query => PqxdhRegistrationJointIdentityCosts.dynamicKind query = kind))
      ((if kind = .identityCreate ∧ supplied.isNone = true then 1 else 0) +
        PqxdhRegistrationJointOpenCosts.privateTotal budget kind) := by
  have prior := PqxdhRegistrationJointIdentityCosts.initialized_private setup codec checks ensureInit supplied program runtime budget certified kind nonuniform
  rw [← PqxdhRegistrationJointReportCompiler.initialized_erase setup codec checks ensureInit supplied count program runtime] at prior
  have lifted := (erase_bound (fun query => PqxdhRegistrationJointIdentityCosts.dynamicKind query = kind) _ _).mp prior
  exact (isQueryBoundP_congr_pred (fun query => by cases query <;> rfl)).mp lifted


/-- Generated-target accounting includes each generated Beacon and the Server only when its seed was not supplied by the caller. Imported identities never consume this target budget. -/
theorem initialized_creates (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count program runtime).IsQueryBoundP
      (PqxdhJointPhase1Reports.SourceClass PqxdhDynamicIdentityPool.IsCreate)
      ((if supplied.isNone then 1 else 0) + budget (.inl 1)) := by
  have bounded := initialized_private setup codec checks ensureInit supplied count program runtime budget certified .identityCreate (by decide)
  simp only [PqxdhRegistrationJointOpenCosts.privateTotal, true_and] at bounded
  apply (isQueryBoundP_congr_pred (p := PqxdhJointPhase1Reports.SourceClass
    (fun query => PqxdhRegistrationJointIdentityCosts.dynamicKind query = .identityCreate)) ?_).mp bounded
  rintro (query | report)
  · rcases query with coin | request
    · simp [PqxdhJointPhase1Reports.SourceClass, PqxdhRegistrationJointIdentityCosts.dynamicKind, PqxdhDynamicIdentityPool.IsCreate]
    · cases request with
      | create => simp [PqxdhJointPhase1Reports.SourceClass, PqxdhRegistrationJointIdentityCosts.dynamicKind, PqxdhRegistrationJointServiceCosts.poolClass, PqxdhDynamicIdentityPool.IsCreate]
      | reveal index => simp [PqxdhJointPhase1Reports.SourceClass, PqxdhRegistrationJointIdentityCosts.dynamicKind, PqxdhRegistrationJointServiceCosts.poolClass, PqxdhDynamicIdentityPool.IsCreate]
      | service index request =>
          cases request <;> simp [PqxdhJointPhase1Reports.SourceClass, PqxdhRegistrationJointIdentityCosts.dynamicKind, PqxdhRegistrationJointServiceCosts.poolClass, PqxdhDynamicIdentityPool.IsCreate]
  · rfl

/-- Real execution of the complete public-report experiment retains the original evaluated uniform/base bill. Public signature verification adds no oracle randomness; no bound on its CPU cost or on a replaced challenger is inferred. -/
theorem initialized_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count program runtime)).IsTotalQueryBound
      ((qInit + if supplied.isNone then 32 else 0) + ∑ source, PqxdhRegistrationJointRevealCosts.uniformCost caps source * budget source) := by
  have prior := PqxdhRegistrationJointIdentityCosts.initialized_uniform setup codec checks ensureInit qInit initBound
    caps bounded supplied program runtime budget certified
  have projection := PqxdhRegistrationJointReportSource.program_projection setup.joint count
    (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count program runtime)
    (PqxdhJointPhase1Reports.initialMonitor count,
      ⟨PqxdhDynamicIdentityReports.initialSource count, PqxdhDynamicIdentityReports.initialSnapshot count, false, []⟩)
  rw [PqxdhRegistrationJointReportCompiler.initialized_erase] at projection
  change _ = (simulateQ (PqxdhDynamicIdentityPool.lazyImpl setup.joint)
    (PqxdhRegistrationJointIdentityCompiler.initialized setup codec checks ensureInit supplied program runtime)).run PqxdhDynamicIdentityPool.initialState at projection
  rw [← projection] at prior
  simpa only [PqxdhJointPhase1Reports.run, IsTotalQueryBound, isQueryBound_map_iff] using prior

end BeaconcryptCore.Computational.PqxdhRegistrationJointReportCosts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportCosts.erase_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportCosts.erase_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportCosts.initialized_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportCosts.initialized_private

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportCosts.initialized_creates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportCosts.initialized_creates

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportCosts.initialized_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportCosts.initialized_uniform
