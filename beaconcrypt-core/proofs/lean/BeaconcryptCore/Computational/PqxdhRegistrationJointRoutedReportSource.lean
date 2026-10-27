-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportHistory
import BeaconcryptCore.Computational.PqxdhRegistrationJointReportSource

/-! The actual report experiment retains the native index audit alongside the ordinary generated-identity signing history. The correspondence is derived for arbitrary source schedules, including known imports and reveals. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportSource
open PqxdhJointIdentity PqxdhDynamicIdentityPool PqxdhDynamicIdentityReports
open PqxdhRegistrationJointIdentityRouting (Registry route)
open PqxdhRegistrationJointReportLift (Spec extend erase)
open PqxdhRegistrationJointRoutedHistory (messagesAt Tracked)

/-- Forgetting the public report monitors preserves both complete routing states and the result of every adaptive continuation. -/
theorem projection {Result : Type} (joint : Primitives) (count : Nat)
    (work : OracleComp (Spec PqxdhRegistrationJointIdentityRouting.Spec) Result)
    (registry : Registry)
    (state : PqxdhJointPhase1Reports.Monitor count × ReportingState count) :
    (fun result => (result.1.1, (result.1.2, result.2.2.source.2))) <$>
      (simulateQ (PqxdhJointPhase1Reports.sourceImpl joint count)
        ((simulateQ (extend (route joint)) work).run registry)).run state =
      PqxdhRegistrationJointIdentityRouting.run joint
        (simulateQ (route joint) (simulateQ erase work)) (registry, state.2.source.2) := by
  have same := PqxdhRegistrationJointReportSource.program_projection joint count
    ((simulateQ (extend (route joint)) work).run registry) state
  rw [PqxdhRegistrationJointReportLift.extend_erase] at same
  simpa only [Functor.map_map, PqxdhRegistrationJointIdentityRouting.run, StateT.run] using
    congrArg (fun computation => (fun result : (Result × Registry) × SourceState =>
      (result.1.1, (result.1.2, result.2))) <$> computation) same

/-- Every report-bearing source prefix derives the native-to-generated signing relation from the actual empty initial states. Reports do not impose a new history hypothesis. -/
theorem tracked {Result : Type} (joint : Primitives) (count : Nat)
    (work : OracleComp (Spec PqxdhRegistrationJointIdentityRouting.Spec) Result)
    (result : (Result × Registry) × (PqxdhJointPhase1Reports.Monitor count × ReportingState count))
    (supported : result ∈ support (PqxdhJointPhase1Reports.run joint count
      ((simulateQ (extend (route joint)) work).run ⟨[], []⟩))) :
    Tracked (result.1.2, result.2.2.source.2) := by
  have actual : (result.1.1, (result.1.2, result.2.2.source.2)) ∈ support
      ((fun result => (result.1.1, (result.1.2, result.2.2.source.2))) <$>
        PqxdhJointPhase1Reports.run joint count
          ((simulateQ (extend (route joint)) work).run ⟨[], []⟩)) := by
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  unfold PqxdhJointPhase1Reports.run at actual
  rw [projection] at actual
  exact PqxdhRegistrationJointRoutedHistorySchedule.program joint (simulateQ erase work)
    _ PqxdhRegistrationJointRoutedHistory.initial _ actual

/-- An actual generated handle's native signing log equals the exact snapshot consumed by a report at this prefix. Known imports, unsuccessful services and later stopping are retained. -/
theorem generated_history {Result : Type} (joint : Primitives) (count : Nat)
    (work : OracleComp (Spec PqxdhRegistrationJointIdentityRouting.Spec) Result)
    (result : (Result × Registry) × (PqxdhJointPhase1Reports.Monitor count × ReportingState count))
    (supported : result ∈ support (PqxdhJointPhase1Reports.run joint count
      ((simulateQ (extend (route joint)) work).run ⟨[], []⟩)))
    (index : Nat) (target : Fin count)
    (found : result.1.2.refs[index]? = some (.generated target.val)) :
    messagesAt index result.1.2.transcript =
      signedMessages (result.2.1.snapshot.history.histories target) :=
  ((tracked joint count work result supported).generated index target.val found).trans
    ((PqxdhRegistrationJointRoutedReportHistory.snapshot joint count _ result supported).2 target).symm

/-- Generated ownership is by creation index. The actual source public key and report snapshot key coincide even if distinct generated slots have equal public-key bytes. -/
theorem generated_key {Result : Type} (joint : Primitives) (count : Nat)
    (work : OracleComp (Spec PqxdhRegistrationJointIdentityRouting.Spec) Result)
    (result : (Result × Registry) × (PqxdhJointPhase1Reports.Monitor count × ReportingState count))
    (supported : result ∈ support (PqxdhJointPhase1Reports.run joint count
      ((simulateQ (extend (route joint)) work).run ⟨[], []⟩)))
    (index target : Nat) (found : result.1.2.refs[index]? = some (.generated target)) :
    result.2.1.snapshot.keys target = sourceKeys joint
      (PqxdhRegistrationJointIdentityRouting.project (result.1.2, result.2.2.source.2)).seeds index := by
  have valid := (tracked joint count work result supported).valid target (List.mem_of_getElem? found)
  rw [(PqxdhRegistrationJointRoutedReportHistory.snapshot joint count _ result supported).1]
  simp [sourceSnapshot, sourceKeys, PqxdhRegistrationJointIdentityRouting.project,
    List.getElem?_map, found, PqxdhRegistrationJointIdentityRouting.resolve,
    List.getElem?_eq_getElem valid]

/-- A literal unissued accepted source field is the ordinary endpoint's field-origin event at this same prefix. Freshness is explicitly the report-time successful-reveal history, not a restriction forbidding later compromise. -/
theorem field_origin {Result : Type} (joint : Primitives) (count : Nat)
    (work : OracleComp (Spec PqxdhRegistrationJointIdentityRouting.Spec) Result)
    (result : (Result × Registry) × (PqxdhJointPhase1Reports.Monitor count × ReportingState count))
    (supported : result ∈ support (PqxdhJointPhase1Reports.run joint count
      ((simulateQ (extend (route joint)) work).run ⟨[], []⟩)))
    (index : Nat) (target : Fin count)
    (found : result.1.2.refs[index]? = some (.generated target.val))
    (publicKey : PublicIdentity) (candidate : PqxdhEd25519EufCma.Phase1Candidate)
    (decoded : PqxdhEd25519EufCma.Phase1KeyTuple)
    (key : sourceKeys joint (PqxdhRegistrationJointIdentityRouting.project
      (result.1.2, result.2.2.source.2)).seeds index = some publicKey)
    (accepted : PqxdhEd25519EufCma.acceptPhase1Candidate joint.verify candidate =
      some (publicKey.ed25519, decoded))
    (fresh : target ∉ result.2.1.snapshot.history.reveals)
    (unissued : ∃ field ∈ PqxdhJointPhase1Reports.candidateFields candidate,
      field.message ∉ messagesAt index result.1.2.transcript) :
    PqxdhJointPhase1Reports.FieldOriginFailure joint ⟨target.val, candidate⟩ result.2.1.snapshot := by
  refine ⟨target.isLt, publicKey, decoded, (generated_key joint count work result supported index target.val found).trans key,
    accepted, fresh, ?_⟩
  simpa only [generated_history joint count work result supported index target found] using unissued

end BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportSource

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportSource.projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportSource.projection

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportSource.tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportSource.tracked

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportSource.generated_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportSource.generated_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportSource.generated_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportSource.generated_key

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportSource.field_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReportSource.field_origin
