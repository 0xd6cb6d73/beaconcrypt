-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationFacts
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionTrace

/-! The chronological source audit and the literal per-index signing transcript contain the same complete tuple blocks. Injectivity of those blocks relates the audit to the existing constructor ledger at the same reached native state; independent unconstrained history witnesses are not combined. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistory
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhEd25519EufCma
open PqxdhDeploymentPublicationSuppressionTrace
open PqxdhRegistrationJointIssuedAttempts
open PqxdhRegistrationJointSigningTranscript (messagesAt)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- Complete attempted tuples in one exact private identity slot, in their actual global order. -/
def keysAt (index : Nat) (audit : Audit) : List Phase1KeyTuple :=
  audit.occurrences.filterMap fun occurrence =>
    if occurrence.identityIndex = index then some occurrence.keys else none

/-- Recording a real prepared call appends only its own slot's tuples. -/
theorem keysAt_record (audit : Audit) (address index selected : Nat) (reply : Option Pqxdh.Bytes)
    (tuples : List Phase1KeyTuple) :
    keysAt selected (audit.record address index reply tuples) =
      keysAt selected audit ++ if index = selected then tuples else [] := by
  by_cases same : index = selected
  · simp [keysAt, Audit.record, same]
  · simp [keysAt, Audit.record, same]

private theorem annotated_finish_messages (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex target : Nat) (retained : Option Phase1Candidate) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (state : PqxdhRegistrationJointFinish.State KemSK)
    (result : (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) ×
      PqxdhRegistrationJointFinish.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointFinish.annotatedFinish setup codec identityIndex kemIndex
      retained raw owner).run state)) :
    messagesAt target result.2.1.1.transcript = messagesAt target state.1.1.transcript := by
  cases phase : owner.beacon.phase <;>
    simp only [PqxdhRegistrationJointFinish.annotatedFinish, phase] at supported
  all_goals try { rw [StateT.run_pure, mem_support_pure_iff] at supported; cases supported; rfl }
  case initSent control prekey oneTime kem =>
    cases retained with
    | none =>
      change result ∈ support (pure ((none, PqxdhBeaconPhase2Preparation.abort control owner), state)) at supported
      rw [mem_support_pure_iff] at supported
      cases supported
      rfl
    | some init =>
      cases decoded : PqxdhServerAuthExperiment.responseOf codec raw with
      | none =>
        simp only [decoded, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        rfl
      | some response =>
        simp only [decoded] at supported
        rw [StateT.run_bind, mem_support_bind_iff] at supported
        obtain ⟨hashed, hashSupport, nativeSupport⟩ := supported
        have keeps : hashed.2.1 = state.1 := by
          simp only [PqxdhRegistrationJointFinish.onNative, StateT.run, support_map] at hashSupport
          obtain ⟨answer, _, rfl⟩ := hashSupport
          rfl
        have preserved := PqxdhRegistrationJointNonSigningHistory.finish
          (completedBinding := PqxdhTranscriptAd.completedOf control hashed.1) setup codec identityIndex kemIndex target
          codec.frameRead raw owner hashed.2 result nativeSupport
        simpa only [keeps] using preserved

/-- Every other literal source command preserves all successful signing messages. -/
theorem source_nonbundle_messages (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (serverIndex : Nat)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (notBundle : ∀ address, query ≠ .inl (.inr (.bundle address)))
    (state : PqxdhRegistrationJointSchedule.State KemSK)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query ×
      PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support
      ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed serverIndex query).run state))
    (selected : Nat) : messagesAt selected result.2.pool.1.transcript =
      messagesAt selected state.pool.1.transcript := by
  rcases query with (coin | request) | read
  case inl.inr =>
    cases request
    case create pin keyId =>
      simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
        PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.create,
        StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨material, _, rfl⟩ := supported
      exact PqxdhRegistrationJointAttemptInvariant.created_messages setup state.pool material selected
    case bundle address => exact False.elim (notBundle address rfl)
    case finish address raw =>
      cases found : state.owners[address]? with
      | none =>
        simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
          PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.finish,
          StateT.run, found, mem_support_pure_iff] at supported
        subst result
        rfl
      | some entry =>
        simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
          PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.finish,
          StateT.run, found, support_map, Set.mem_image] at supported
        obtain ⟨reached, reachedMember, rfl⟩ := supported
        exact annotated_finish_messages setup codec entry.identityIndex entry.kemIndex selected (state.inits address)
          raw entry.owner (state.pool, state.shared) reached reachedMember
    all_goals
      exact (PqxdhDeploymentSigningHistory.quiet_step setup codec checks seed serverIndex _ rfl
        state result supported).messages selected
  all_goals
    exact (PqxdhDeploymentSigningHistory.quiet_step setup codec checks seed serverIndex _ rfl
      state result supported).messages selected

/-- Every actual prepared block appends its three messages before either writer result. -/
theorem after_messages (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index selected : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes)
    (pool : PqxdhDynamicIdentityPool.SourceState) :
    messagesAt selected (PqxdhRegistrationJointBundle.after setup codec index owner generated pool).2.transcript =
      messagesAt selected pool.transcript ++ if index = selected then
        history (PqxdhRegistrationJointAttemptTrace.issued setup owner generated) else [] := by
  cases ready : PqxdhBeaconPhase1Publication.prepare owner generated with
  | none => simp [PqxdhRegistrationJointBundle.after, PqxdhRegistrationJointAttemptTrace.issued, ready, history]
  | some prepared =>
    rw [PqxdhRegistrationJointBundle.after_history setup codec index owner generated pool prepared ready,
      PqxdhRegistrationJointSigningTranscript.signed]
    simp [PqxdhRegistrationJointAttemptTrace.issued, ready, history, PqxdhRegistrationJointAttemptTrace.keys]

/-- The current signing transcript is its unchanged initial prefix followed by exactly the audited blocks. -/
def Held (priorMessages : Nat → List Pqxdh.Bytes) (state : State KemSK) : Prop :=
  ∀ index, messagesAt index state.1.pool.1.transcript = priorMessages index ++ history (keysAt index state.2)

/-- The real prepared block and audit record extend the same prior signing prefix. -/
theorem after_held (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (priorMessages : Nat → List Pqxdh.Bytes) (index address : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes)
    (pool : PqxdhDynamicIdentityPool.SourceState) (audit : Audit)
    (held : ∀ selected, messagesAt selected pool.transcript = priorMessages selected ++ history (keysAt selected audit))
    (selected : Nat) :
    messagesAt selected (PqxdhRegistrationJointBundle.after setup codec index owner generated pool).2.transcript =
      priorMessages selected ++ history (keysAt selected (audit.record address index
        (PqxdhRegistrationJointBundle.after setup codec index owner generated pool).1.1
        (PqxdhRegistrationJointAttemptTrace.issued setup owner generated))) := by
  rw [after_messages, held selected, keysAt_record]
  by_cases same : index = selected
  · simp [same, history, List.append_assoc]
  · simp [same, history]

/-- Every source draw returns exactly the recorded blocks, independently of publication success. -/
theorem trace_held (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (priorMessages : Nat → List Pqxdh.Bytes) (address index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState) (audit : Audit)
    (held : ∀ selected, messagesAt selected pool.transcript = priorMessages selected ++ history (keysAt selected audit))
    (result : PqxdhRegistrationJointAttemptTrace.NativeResult KemSK × Audit)
    (supported : result ∈ support (trace setup codec address index owner pool audit)) :
    ∀ selected, messagesAt selected result.1.2.transcript = priorMessages selected ++ history (keysAt selected result.2) := by
  rw [trace_after] at supported
  cases phase : owner.beacon.phase <;> simp only [phase] at supported
  case fresh =>
    simp only [support_map, Set.mem_image] at supported
    obtain ⟨scalar, _, rfl⟩ := supported
    exact after_held setup codec priorMessages index address owner (some scalar) pool audit held
  case freshWithCoins =>
    simp only [mem_support_pure_iff] at supported
    subst result
    exact after_held setup codec priorMessages index address owner none pool audit held
  all_goals
    simp only [mem_support_pure_iff] at supported
    subst result
    intro selected
    simpa only [keysAt_record, ite_self, List.append_nil, history] using held selected

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistory

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistory.keysAt_record' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistory.keysAt_record

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistory.source_nonbundle_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistory.source_nonbundle_messages

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistory.after_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistory.after_messages

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistory.after_held' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistory.after_held

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistory.trace_held' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistory.trace_held
