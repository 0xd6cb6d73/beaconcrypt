-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistory

/-! Every actual monitored source query maintains exact chronological signing history, so the final audit is tied to the same native source outcome and its existing constructor receipts. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInvariant
open PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhEd25519EufCma
open PqxdhDeploymentPublicationSuppressionTrace
open PqxdhDeploymentPublicationAuditHistory
open PqxdhRegistrationJointIssuedAttempts
open PqxdhRegistrationJointSigningTranscript (messagesAt)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- Missing, inactive, failed and successful bundle requests preserve the same literal message/audit correspondence. -/
theorem bundle_held (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (priorMessages : Nat → List Pqxdh.Bytes) (address : Nat) (state : State KemSK)
    (held : Held priorMessages state) (result : Option Pqxdh.Bytes × State KemSK)
    (supported : result ∈ support ((bundle setup codec address).run state)) : Held priorMessages result.2 := by
  cases found : state.1.owners[address]? with
  | none =>
    simp only [bundle, StateT.run, found, mem_support_pure_iff] at supported
    subst result
    simpa [Held, keysAt_record, history] using held
  | some entry =>
    simp only [bundle, StateT.run, found, support_map, Set.mem_image] at supported
    obtain ⟨returned, returnedSupport, rfl⟩ := supported
    exact trace_held setup codec priorMessages address entry.identityIndex entry.owner state.1.pool.1
      state.2 held returned returnedSupport

/-- Forwarded source commands retain their exact transcript prefix and add no unrecorded signature. -/
theorem forwarded_held (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (serverIndex : Nat)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (notBundle : ∀ address, query ≠ .inl (.inr (.bundle address)))
    (priorMessages : Nat → List Pqxdh.Bytes) (state : State KemSK) (held : Held priorMessages state)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × State KemSK)
    (supported : result ∈ support ((onSource
      (PqxdhRegistrationJointServerSchedule.source setup codec checks seed serverIndex query)).run state)) :
    Held priorMessages result.2 := by
  simp only [onSource, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨returned, returnedSupport, rfl⟩ := supported
  intro selected
  rw [source_nonbundle_messages setup codec checks seed serverIndex query notBundle state.1 returned
    returnedSupport selected]
  exact held selected

/-- All actual source commands preserve the same chronological signing/audit invariant. -/
theorem query_held (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (serverIndex : Nat)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (priorMessages : Nat → List Pqxdh.Bytes) (state : State KemSK) (held : Held priorMessages state)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × State KemSK)
    (supported : result ∈ support ((handler setup codec checks seed serverIndex query).run state)) :
    Held priorMessages result.2 := by
  rcases query with (coin | request) | read
  case inl.inr =>
    cases request
    case bundle address => exact bundle_held setup codec priorMessages address state held result supported
    all_goals
      exact forwarded_held setup codec checks seed serverIndex _ (by intro address; simp)
        priorMessages state held result supported
  all_goals
    exact forwarded_held setup codec checks seed serverIndex _ (by intro address; simp)
      priorMessages state held result supported

/-- The complete adaptive source execution preserves exact prior signing history and every audited tuple. -/
theorem program_held (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (serverIndex : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (priorMessages : Nat → List Pqxdh.Bytes) (state : State KemSK) (held : Held priorMessages state)
    (result : Result × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks seed serverIndex) program).run state)) :
    Held priorMessages result.2 := by
  exact (run_rel (handler setup codec checks seed serverIndex)
    (fun before after => Held priorMessages before → Held priorMessages after)
    (fun _ previous => previous) (fun _ _ _ first second previous => second (first previous))
    (fun query before after member previous =>
      query_held setup codec checks seed serverIndex query priorMessages before previous after member)
    program state result supported) held

/-- The actual initial transcript is retained as a prefix, with no assumed constructor or publication success. -/
theorem initial_held (state : PqxdhRegistrationJointSchedule.State KemSK) :
    Held (fun index => messagesAt index state.pool.1.transcript) (state, Audit.empty) := by
  simp [Held, keysAt, Audit.empty, history]

/-- The global audit exactly accounts for every newly signed message in the same complete source run. -/
theorem program_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (serverIndex : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (result : Result × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks seed serverIndex) program).run
      (state, Audit.empty))) (selected : Nat) :
    messagesAt selected result.2.1.pool.1.transcript = messagesAt selected state.pool.1.transcript ++
      history (keysAt selected result.2.2) := by
  exact program_held setup codec checks seed serverIndex program
    (fun index => messagesAt index state.pool.1.transcript) (state, Audit.empty) (initial_held state)
    result supported selected

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInvariant

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInvariant.bundle_held' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInvariant.bundle_held

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInvariant.forwarded_held' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInvariant.forwarded_held

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInvariant.query_held' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInvariant.query_held

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInvariant.program_held' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInvariant.program_held

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInvariant.initial_held' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInvariant.initial_held

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInvariant.program_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInvariant.program_history
