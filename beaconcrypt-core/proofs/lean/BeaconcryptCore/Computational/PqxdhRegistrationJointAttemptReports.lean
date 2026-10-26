-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedReports
import BeaconcryptCore.Computational.PqxdhRegistrationJointReportEvents

/-! Actual complete constructor/signing-attempt origin or an ordinary joint-use weak-EUF report, with native source freshness and the full initialized source state preserved. The report batch charges no guessed field or report position. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptReports
open PqxdhJointIdentity PqxdhDynamicIdentityReports PqxdhEd25519EufCma PqxdhServerAuthExperiment
open PqxdhRegistrationJointInitializedReports
open PqxdhRegistrationJointSigningTranscript (messagesAt)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Result Reader Response : Type}

/-- Every reached generated owner has its actual immutable KEM receipt and complete chronological signing attempts. An accepted fresh tuple outside those attempts is the existing original-field EUF event. -/
theorem owner_origin (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (result : ReportResult KemSK A Result count)
    (supported : result ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count work runtime)))
    (encoded : PqxdhRegistrationJointInitializedSchedule.Outcome KemSK Result)
    (finished : (sourceResult result).1 = some encoded)
    (address : Nat) (owner : PqxdhRegistrationJointGeneratedFinish.EncodedEntry)
    (found : encoded.2.2.owners[address]? = some owner)
    (target : Fin count) (generated : result.1.2.refs[owner.1]? = some (.generated target.val))
    (publicKey : PublicIdentity) (candidate : Phase1Candidate) (decoded : Phase1KeyTuple)
    (key : sourceKeys setup.joint (sourceResult result).2.1.1.seeds owner.1 = some publicKey)
    (accepted : acceptPhase1Candidate setup.joint.verify candidate = some (publicKey.ed25519, decoded))
    (fresh : PqxdhRegistrationJointRoutedReveals.revealedAt owner.1 (sourceResult result).2.1.1.transcript = false) :
    ∃ receipt : PqxdhRegistrationJointAttemptLedger.Receipt,
      PqxdhRegistrationJointIssuedAttempts.Fixed receipt.prekey receipt.pqKey receipt.attempts ∧
      messagesAt owner.1 (sourceResult result).2.1.1.transcript = PqxdhRegistrationJointIssuedAttempts.history receipt.attempts ∧
      ((sourceResult result).2.1.2.keys[owner.2.1]?).map Prod.fst = some receipt.pqKey ∧
      (decoded ∈ receipt.attempts ∨ PqxdhJointPhase1Reports.FieldOriginFailure setup.joint ⟨target.val, candidate⟩ result.2.1.snapshot) := by
  obtain ⟨original, ledger, _, encodedSame, valid⟩ := successful_witness setup codec checks ensureInit supplied count work runtime result supported encoded finished
  have nativePool : original.2.2.pool = (sourceResult result).2.1 :=
    (congrArg (fun value => value.2.2.pool) encodedSame).trans (outcome_pool result encoded finished)
  have lookup : (original.2.2.owners.map (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup))[address]? = some owner := by
    change (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup original).2.2.owners[address]? = some owner
    rw [encodedSame]
    exact found
  rw [List.getElem?_map] at lookup
  obtain ⟨entry, atEntry, rfl⟩ := Option.map_eq_some_iff.mp lookup
  obtain ⟨receipt, recorded, kem, _⟩ := valid.live entry (List.mem_of_getElem? atEntry)
  change ledger entry.identityIndex = some receipt at recorded
  refine ⟨receipt, valid.fixed entry.identityIndex receipt recorded, ?_, ?_, ?_⟩
  · rw [← nativePool]
    simpa only [PqxdhRegistrationJointAttemptInvariant.attempts, recorded, Option.map_some, Option.getD_some,
      PqxdhRegistrationJointGeneratedFinish.encodeEntry] using
      valid.exactHistory entry.identityIndex
  case refine_3 =>
    by_cases issued : decoded ∈ receipt.attempts
    · exact Or.inl issued
    · have unissued := PqxdhRegistrationJointAttemptOrigin.absent_unissued setup
        (original.2.2, ledger) valid entry.identityIndex receipt recorded candidate publicKey.ed25519 decoded accepted issued
      change ∃ field ∈ PqxdhJointPhase1Reports.candidateFields candidate,
        field.message ∉ messagesAt entry.identityIndex original.2.2.pool.1.transcript at unissued
      rw [nativePool] at unissued
      exact Or.inr (field_origin setup codec checks ensureInit supplied count work runtime result supported
        entry.identityIndex target generated publicKey candidate decoded key accepted fresh unissued)
  case refine_2 =>
    simpa only [nativePool, kem, PqxdhRegistrationJointGeneratedFinish.encodeEntry] using
      valid.kem entry.identityIndex receipt recorded

end BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptReports

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptReports.owner_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptReports.owner_origin
