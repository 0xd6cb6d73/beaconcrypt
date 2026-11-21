-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditLedger

/-! The actual initialized deployment audit and its final public transcript share exactly their successful bundle publications. The witness includes the same generated Server, native state, private identity/KEM pools and runtime; no independent audit alignment assumption is used. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit
open PqxdhServerAuthExperiment
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
open PqxdhDeploymentPublicationSuppressionTrace (Occurrence)
open PqxdhDeploymentPublicationAuditLedger
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

/-- Every actual initialized audit retains precisely the successful public bundle replies of its own final ledger. -/
theorem actual_publications (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : SourceOutcome KemSK (PqxdhDeploymentPublicationSecurityExecution.Result X))
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support (actual setup codec checks route ensureInit bounds mode adversary runtime)) :
    publications outcome.2.2.2 = ledgerPublications outcome.2.1.1.2.transcript := by
  simp only [actual, initialized, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨⟨(_ | created), born⟩, _, continued⟩ := supported
  · simp only [mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at continued
  · simp only [support_map, Set.mem_image] at continued
    obtain ⟨executed, member, equal⟩ := continued
    have same : outcome = (PqxdhRegistrationJointServerBirth.encode created, executed.1, executed.2) :=
      (Option.some.inj (congrArg Prod.fst equal)).symm
    rw [same]
    exact compileFull_publications setup codec checks created.seed created.server.server.metadata.identityIndex route
      bounds mode adversary _ executed member

/-- A successful prepared occurrence of the initialized source is an actual bundle publication at that same address in the final public ledger. -/
theorem actual_occurrence_published (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : SourceOutcome KemSK (PqxdhDeploymentPublicationSecurityExecution.Result X))
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support (actual setup codec checks route ensureInit bounds mode adversary runtime))
    (occurrence : Occurrence) (member : occurrence ∈ outcome.2.2.2.occurrences) (bytes : Pqxdh.Bytes)
    (published : occurrence.reply = some bytes) :
    (⟨.inl (.inr (.bundle occurrence.ownerAddress)), some bytes⟩ : PqxdhDeploymentInterface.Entry) ∈
      outcome.2.1.1.2.transcript := by
  have logged : (occurrence.ownerAddress, bytes) ∈ publications outcome.2.2.2 :=
    List.mem_filterMap.mpr ⟨occurrence, member, by rw [published]; rfl⟩
  rw [actual_publications setup codec checks route ensureInit bounds mode adversary runtime outcome after supported,
    mem_ledgerPublications] at logged
  exact logged

/-- Final public bundle lookup is exactly first-success lookup in that same initialized audit. -/
theorem actual_bundleOf (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : SourceOutcome KemSK (PqxdhDeploymentPublicationSecurityExecution.Result X))
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support (actual setup codec checks route ensureInit bounds mode adversary runtime))
    (address : Nat) :
    PqxdhDeploymentTranscript.bundleOf outcome.2.1.1.2.transcript address =
      firstPublication (publications outcome.2.2.2) address := by
  rw [actual_publications setup codec checks route ensureInit bounds mode adversary runtime outcome after supported]
  exact (firstPublication_ledger _ address).symm

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_publications' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_publications

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_occurrence_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_occurrence_published

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_bundleOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit.actual_bundleOf
