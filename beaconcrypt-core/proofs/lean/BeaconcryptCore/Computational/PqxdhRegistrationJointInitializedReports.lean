-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointReportFreshness
import BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptOrigin

/-! The report-time signing and disclosure equalities instantiated at the actual generated-or-imported Server constructor and complete adaptive native command scheduler. The interpreted full source witness and its private attempt ledger come from that same execution. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedReports
open PqxdhJointIdentity PqxdhDynamicIdentityPool PqxdhDynamicIdentityReports
open PqxdhServerAuthExperiment
open PqxdhRegistrationJointIdentityRouting (Registry)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Result Reader Response : Type}

abbrev ReportResult (KemSK A Result : Type) (count : Nat) :=
  ((Option (PqxdhRegistrationJointOpenInitialization.Outcome KemSK Result) ×
    PqxdhRegistrationJointIdentityCompiler.Local KemSK A) × Registry) ×
    (PqxdhJointPhase1Reports.Monitor count × ReportingState count)

/-- Full source reconstruction is an analysis projection after ordinary interpretation, never an extra seed oracle for the client. -/
def sourceResult {count : Nat} (result : ReportResult KemSK A Result count) :=
  PqxdhRegistrationJointIdentityCompiler.initializedResult (result.1, result.2.2.source.2)

/-- Each actual initialized report-game outcome has a literal complete source execution with the same encoded private/native/runtime result. -/
theorem source_witness (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (result : ReportResult KemSK A Result count)
    (supported : result ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count work runtime))) :
    ∃ original, original ∈ support ((PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied work).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)) ∧
      (original.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), original.2) = sourceResult result := by
  have mapped : sourceResult result ∈ support (sourceResult <$>
      PqxdhJointPhase1Reports.run setup.joint count
        (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count work runtime)) := by
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  unfold sourceResult at mapped
  rw [PqxdhRegistrationJointReportSource.initialized_source] at mapped
  obtain ⟨original, member, same⟩ := OracleComp.mem_support_map_peel _ _ mapped
  exact ⟨original, member, same.symm⟩

/-- Actual initialized command prefixes supply the precise native signing history used at each generated target's report snapshot. -/
theorem signing_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (result : ReportResult KemSK A Result count)
    (supported : result ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count work runtime)))
    (index : Nat) (target : Fin count)
    (found : result.1.2.refs[index]? = some (.generated target.val)) :
    PqxdhRegistrationJointSigningTranscript.messagesAt index (sourceResult result).2.1.1.transcript =
      signedMessages (result.2.1.snapshot.history.histories target) := by
  exact PqxdhRegistrationJointRoutedReportSource.generated_history setup.joint count _ result supported index target found

/-- Report-time freshness in the actual initialized scheduler is exactly absence of a successful source-index seed reveal in its retained audit. -/
theorem freshness (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (result : ReportResult KemSK A Result count)
    (supported : result ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count work runtime)))
    (index : Nat) (target : Fin count)
    (found : result.1.2.refs[index]? = some (.generated target.val)) :
    target ∉ result.2.1.snapshot.history.reveals ↔
      PqxdhRegistrationJointRoutedReveals.revealedAt index (sourceResult result).2.1.1.transcript = false := by
  exact PqxdhRegistrationJointReportFreshness.fresh setup.joint count _ result supported index target found

/-- A fresh native accepted unissued field in the actual initialized execution is the existing report-time ordinary joint-use weak-EUF event. All key and history correspondence is derived; no honest selected-candidate premise is required. -/
theorem field_origin (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (result : ReportResult KemSK A Result count)
    (supported : result ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count work runtime)))
    (index : Nat) (target : Fin count)
    (found : result.1.2.refs[index]? = some (.generated target.val))
    (publicKey : PublicIdentity) (candidate : PqxdhEd25519EufCma.Phase1Candidate)
    (decoded : PqxdhEd25519EufCma.Phase1KeyTuple)
    (key : sourceKeys setup.joint (sourceResult result).2.1.1.seeds index = some publicKey)
    (accepted : PqxdhEd25519EufCma.acceptPhase1Candidate setup.joint.verify candidate = some (publicKey.ed25519, decoded))
    (fresh : PqxdhRegistrationJointRoutedReveals.revealedAt index (sourceResult result).2.1.1.transcript = false)
    (unissued : ∃ field ∈ PqxdhJointPhase1Reports.candidateFields candidate,
      field.message ∉ PqxdhRegistrationJointSigningTranscript.messagesAt index (sourceResult result).2.1.1.transcript) :
    PqxdhJointPhase1Reports.FieldOriginFailure setup.joint ⟨target.val, candidate⟩ result.2.1.snapshot := by
  exact PqxdhRegistrationJointRoutedReportSource.field_origin setup.joint count _ result supported index target found
    publicKey candidate decoded key accepted
    ((freshness setup codec checks ensureInit supplied count work runtime result supported index target found).mpr fresh) unissued

/-- A successful actual report-game outcome has the complete same-execution native source state and its derived immutable constructor/signing-attempt ledger. -/
theorem successful_witness (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (result : ReportResult KemSK A Result count)
    (supported : result ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count work runtime)))
    (encoded : PqxdhRegistrationJointInitializedSchedule.Outcome KemSK Result)
    (finished : (sourceResult result).1 = some encoded) :
    ∃ original ledger,
      (some original, (sourceResult result).2) ∈ support
        ((PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied work).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)) ∧
      PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup original = encoded ∧
      PqxdhRegistrationJointAttemptInvariant.Invariant setup (original.2.2, ledger) := by
  obtain ⟨⟨optional, after⟩, member, same⟩ := source_witness setup codec checks ensureInit supplied count work runtime result supported
  obtain ⟨original, found, encodedSame⟩ := Option.map_eq_some_iff.mp ((congrArg Prod.fst same).trans finished)
  change optional = some original at found
  have afterSame : after = (sourceResult result).2 := congrArg Prod.snd same
  have actual : (some original, (sourceResult result).2) ∈ support
      ((PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied work).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)) := by
    simpa only [found, afterSame] using member
  obtain ⟨ledger, _, valid⟩ := PqxdhRegistrationJointAttemptInitialized.source_witness setup codec checks ensureInit supplied work runtime _ original actual
  exact ⟨original, ledger, actual, encodedSame, valid⟩

/-- Successful source reconstruction installs exactly the returned private identity/KEM pool into the complete native outcome. -/
theorem outcome_pool {count : Nat} (result : ReportResult KemSK A Result count)
    (encoded : PqxdhRegistrationJointInitializedSchedule.Outcome KemSK Result)
    (finished : (sourceResult result).1 = some encoded) :
    encoded.2.2.pool = (sourceResult result).2.1 := by
  change result.1.1.1.map (PqxdhRegistrationJointOpenInitialization.attach (sourceResult result).2.1) = some encoded at finished
  obtain ⟨value, _, rfl⟩ := Option.map_eq_some_iff.mp finished
  rfl

end BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedReports

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedReports.source_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedReports.source_witness

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedReports.signing_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedReports.signing_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedReports.freshness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedReports.freshness

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedReports.field_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedReports.field_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedReports.successful_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedReports.successful_witness

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedReports.outcome_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedReports.outcome_pool
