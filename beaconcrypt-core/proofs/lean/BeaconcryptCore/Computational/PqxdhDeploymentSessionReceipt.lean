-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhServerAuthCommonEvent

/-!
The accepted registration record retains the assigned Beacon identifier, application payload and associated data of the actual partner seal. CompleteAgreement keeps these explicit fields together with the original source token, common root, initializer and publication receipts; it does not posit root equality or reconstruct a root from an evolved kernel.

The source connection is through PqxdhServerAuthExperiment.acceptedOf: it records fields only when the actual finish returns some payload. Accepted.ofStaged reads the authenticated assigned identifier, the opened plaintext after its eight-byte identifier prefix and the native associated data. PqxdhServerAuthRootInitialization.finish_receipt proves that this same plaintext tail is the actual returned payload; PqxdhServerAuthRootAcceptance.path_finish identifies the frozen snapshot with that staged acceptance and its installed owner. These are derived facts of supported source executions, rather than caller-supplied agreement premises.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentSessionReceipt

open PqxdhServerAuthExperiment PqxdhServerAuthRootExecution
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The first actual acceptance and one seal of its source session agree on every delivered record field. -/
def RecordAgreement (result : Outcome KemSK) (index : Nat) : Prop :=
  ∃ snap context, result.state.1.ghost.acceptance = some snap ∧
    (index, context) ∈ snap.seals ∧
    snap.accepted.keyId = context.targetId ∧
    snap.accepted.payload = context.plaintext.drop 8 ∧
    snap.accepted.associatedData = context.associatedData

/-- Source root agreement and both actual initializers, with explicit delivered identifier, payload and AD agreement. -/
def CompleteAgreement (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (result : Outcome KemSK) (index : Nat) : Prop :=
  PqxdhServerAuthRootCommon.Common setup codec checks result index ∧ RecordAgreement result index

/-- A source matching publication determines the concrete assigned identifier, payload and AD. -/
theorem matching_fields (setup : Setup baseSpec KemSK) (result : Outcome KemSK) (index : Nat)
    (matching : PqxdhServerAuthRootCommon.MatchingPublication setup result index) :
    RecordAgreement result index := by
  obtain ⟨snap, context, accepted, _, logged, matched, _⟩ := matching
  exact ⟨snap, context, accepted, logged,
    congrArg Accepted.keyId matched.symm,
    congrArg Accepted.payload matched.symm,
    congrArg Accepted.associatedData matched.symm⟩

/-- Every existing common source receipt already supplies the complete delivered fields, without another premise. -/
theorem common_complete (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (result : Outcome KemSK) (index : Nat)
    (common : PqxdhServerAuthRootCommon.Common setup codec checks result index) :
    CompleteAgreement setup codec checks result index :=
  ⟨common, matching_fields setup result index common.2.1⟩

/-- One actual published source session agrees on its root and all delivered record fields. -/
def Authenticated (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (result : Outcome KemSK) : Prop :=
  ∃ index, CompleteAgreement setup codec checks result index ∧
    PqxdhServerAuthRecordPublicationEvent.RecordPublished codec index (result.state.2.map publicCall)

/-- The explicit delivered-field agreement retains exactly the original complete authentication event. -/
theorem authenticated_iff (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (result : Outcome KemSK) :
    Authenticated setup codec checks result ↔
      PqxdhServerAuthCommonEvent.Authenticated setup codec checks result :=
  ⟨fun ⟨index, complete, published⟩ => ⟨index, complete.1, published⟩,
    fun ⟨index, common, published⟩ => ⟨index, common_complete setup codec checks result index common, published⟩⟩

/-- Acceptance without full root and delivered-field agreement, on the same source outcome. -/
def Failure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (result : Outcome KemSK) : Prop :=
  (∃ snap, result.state.1.ghost.acceptance = some snap) ∧ ¬ Authenticated setup codec checks result

/-- Explicit identifier, payload and AD agreement adds no new loss to the source authentication bound. -/
theorem failure_iff (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (result : Outcome KemSK) :
    Failure setup codec checks result ↔ PqxdhServerAuthCommonEvent.Failure setup codec checks result := by
  simp only [Failure, PqxdhServerAuthCommonEvent.Failure, authenticated_iff]

end BeaconcryptCore.Computational.PqxdhDeploymentSessionReceipt

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionReceipt.matching_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionReceipt.matching_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionReceipt.common_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionReceipt.common_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionReceipt.authenticated_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionReceipt.authenticated_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionReceipt.failure_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionReceipt.failure_iff
