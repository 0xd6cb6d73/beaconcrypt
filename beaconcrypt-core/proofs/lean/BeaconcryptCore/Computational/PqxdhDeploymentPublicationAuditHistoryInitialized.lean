-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInvariant
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit

/-! The actual initialized source audit has exactly the original full signing history. Its chronological tuple blocks therefore determine the same constructor receipt history, including every failed attempt, at the identical reached native/private state. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInitialized
open PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhEd25519EufCma
open PqxdhDeploymentPublicationSuppressionTrace
open PqxdhDeploymentPublicationAuditHistory
open PqxdhDeploymentPublicationAuditHistoryInvariant
open PqxdhRegistrationJointIssuedAttempts
open PqxdhRegistrationJointSigningTranscript (messagesAt)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

/-- Starting from the real empty service pools derives the literal audit/signing equality without a caller history premise. -/
theorem initialized_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (outcome : PqxdhDeploymentPublicationSecurityAudit.SourceOutcome KemSK Result)
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support
      ((PqxdhDeploymentPublicationSecurityAudit.initialized setup codec checks ensureInit supplied program).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))) :
    ∀ selected, messagesAt selected outcome.2.2.1.pool.1.transcript = history (keysAt selected outcome.2.2.2) := by
  simp only [PqxdhDeploymentPublicationSecurityAudit.initialized, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨⟨(_ | created), born⟩, bornMember, continued⟩ := supported
  · simp only [mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at continued
  · simp only [support_map, Set.mem_image] at continued
    obtain ⟨executed, executedMember, equal⟩ := continued
    have same : outcome = (PqxdhRegistrationJointServerBirth.encode created, executed.1, executed.2) :=
      (Option.some.inj (congrArg Prod.fst equal)).symm
    rw [same]
    intro selected
    have unsigned : messagesAt selected born.1.1.transcript = [] := by
      rw [(PqxdhRegistrationJointServerBirth.source_constructor setup.joint ensureInit setup.serverKeyId
        supplied ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) born created bornMember).1,
        PqxdhRegistrationJointAttemptInitialized.install_messages]
      rfl
    simpa only [PqxdhRegistrationJointSchedule.initial, unsigned, List.nil_append] using
      program_history setup codec checks created.seed created.server.server.metadata.identityIndex program
        (PqxdhRegistrationJointSchedule.initial born.1 (PqxdhRegistrationSchedule.initial created).shared)
        executed executedMember selected

/-- The existing actual constructor receipt ledger has exactly the audited per-slot attempts, by literal history injectivity. -/
theorem constructor_witness (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (outcome : PqxdhDeploymentPublicationSecurityAudit.SourceOutcome KemSK Result)
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support
      ((PqxdhDeploymentPublicationSecurityAudit.initialized setup codec checks ensureInit supplied program).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))) :
    ∃ ledger, PqxdhRegistrationJointAttemptInvariant.Invariant setup (outcome.2.2.1, ledger) ∧
      ∀ index, PqxdhRegistrationJointAttemptInvariant.attempts ledger index = keysAt index outcome.2.2.2 := by
  have original : (some (PqxdhDeploymentPublicationSecurityAudit.erase outcome), after) ∈ support
      ((PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied program).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)) := by
    rw [← PqxdhDeploymentPublicationSecurityAudit.source, support_map]
    exact ⟨(some outcome, after), supported, rfl⟩
  obtain ⟨ledger, _, valid⟩ := PqxdhRegistrationJointAttemptInitialized.source_witness
    setup codec checks ensureInit supplied program runtime after _ original
  refine ⟨ledger, valid, ?_⟩
  intro index
  exact PqxdhDeploymentPublicationFacts.history_injective _ _
    ((valid.exactHistory index).symm.trans
      (initialized_history setup codec checks ensureInit supplied program runtime outcome after supported index))

/-- Every reached owner has fixed constructor public fields throughout all its actual audited attempts. -/
theorem owner_fixed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (outcome : PqxdhDeploymentPublicationSecurityAudit.SourceOutcome KemSK Result)
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support
      ((PqxdhDeploymentPublicationSecurityAudit.initialized setup codec checks ensureInit supplied program).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)))
    (address : Nat) (entry : PqxdhRegistrationJointOwnership.Entry KemSK)
    (found : outcome.2.2.1.owners[address]? = some entry) :
    ∃ prekey pqKey, Fixed prekey pqKey (keysAt entry.identityIndex outcome.2.2.2) := by
  obtain ⟨ledger, valid, exactAudit⟩ := constructor_witness setup codec checks ensureInit supplied
    program runtime outcome after supported
  obtain ⟨receipt, recorded, _, _⟩ := valid.live entry (List.mem_of_getElem? found)
  change ledger entry.identityIndex = some receipt at recorded
  refine ⟨receipt.prekey, receipt.pqKey, ?_⟩
  have same := exactAudit entry.identityIndex
  simp only [PqxdhRegistrationJointAttemptInvariant.attempts, recorded, Option.map_some,
    Option.getD_some] at same
  simpa only [← same] using valid.fixed entry.identityIndex receipt recorded

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInitialized

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInitialized.initialized_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInitialized.initialized_history

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInitialized.constructor_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInitialized.constructor_witness

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInitialized.owner_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInitialized.owner_fixed
