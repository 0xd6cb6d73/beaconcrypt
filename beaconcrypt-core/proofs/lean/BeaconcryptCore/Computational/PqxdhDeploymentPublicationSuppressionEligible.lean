-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionGenerated
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityClient
import BeaconcryptCore.Computational.PqxdhRegistrationJointReportFreshness

open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionEligible
open PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhEd25519EufCma
open PqxdhDeploymentPublicationSuppressionInitialized
open PqxdhDeploymentPublicationSuppressionGenerated (ReportResult)
open PqxdhRegistrationJointSigningTranscript (messagesAt)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

/-- A literal ordinary-game client with zero private-read requests has no successful identity disclosure, at any index. -/
theorem ordinary_unrevealed {Value : Type} (joint : Primitives)
    (client : OracleComp PqxdhDynamicIdentityPool.DynamicSpec Value)
    (free : client.IsQueryBoundP (fun query => PqxdhRegistrationJointIdentityCosts.dynamicKind query = .other) 0)
    (result : Value × PqxdhDynamicIdentityPool.SourceState)
    (supported : result ∈ support ((simulateQ (PqxdhDynamicIdentityPool.lazyImpl joint) client).run
      PqxdhDynamicIdentityPool.initialState)) :
    ∀ index, PqxdhRegistrationJointRoutedReveals.revealedAt index result.2.transcript = false := by
  apply PqxdhDeploymentPublishedTuple.run_inv_of_free (PqxdhDynamicIdentityPool.lazyImpl joint)
    (fun query => PqxdhRegistrationJointIdentityCosts.dynamicKind query = .other)
    (fun state => ∀ index, PqxdhRegistrationJointRoutedReveals.revealedAt index state.transcript = false)
    ?_ client free _ (by intro index; rfl) result supported
  intro query allowed state held next member index
  have absent : PqxdhRegistrationJointRoutedReveals.revealAt index ⟨query, next.1⟩ = false := by
    rcases query with coin | request
    · rfl
    · cases request
      case reveal selected =>
        exact False.elim (allowed rfl)
      all_goals rfl
  rw [PqxdhDynamicIdentityPool.lazyImpl_transcript joint query state next member,
    PqxdhRegistrationJointRoutedReveals.append, held index]
  simp only [PqxdhRegistrationJointRoutedReveals.revealedAt, List.any_cons, List.any_nil,
    absent, Bool.false_or]

/-- The actual modified report run inherits zero successful disclosures from the syntactic ordinary-client private-read cap. -/
theorem sourceClient_fresh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (ordinal count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (free : (initialized setup codec checks ensureInit supplied ordinal program runtime).IsQueryBoundP
      (fun query => PqxdhRegistrationJointIdentityCosts.dynamicKind query = .other) 0)
    (reached : ReportResult KemSK A Result count)
    (supported : reached ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (sourceClient setup codec checks ensureInit supplied ordinal program runtime))) :
    ∀ target : Fin count, target ∉ reached.2.1.snapshot.history.reveals := by
  have ordinary : (reached.1, reached.2.2.source.2) ∈ support
      ((simulateQ (PqxdhDynamicIdentityPool.lazyImpl setup.joint)
        (initialized setup codec checks ensureInit supplied ordinal program runtime)).run
          PqxdhDynamicIdentityPool.initialState) := by
    have mapped : (reached.1, reached.2.2.source.2) ∈ support
        ((fun result => (result.1, result.2.2.source.2)) <$>
          PqxdhJointPhase1Reports.run setup.joint count
            (sourceClient setup codec checks ensureInit supplied ordinal program runtime)) := by
      rw [support_map]
      exact ⟨reached, supported, rfl⟩
    rw [PqxdhJointPhase1Reports.run,
      PqxdhRegistrationJointReportSource.program_projection, sourceClient_erase] at mapped
    exact mapped
  have noReveal := ordinary_unrevealed setup.joint _ free _ ordinary
  intro target revealed
  have recorded := (PqxdhRegistrationJointReportFreshness.snapshot setup.joint count _ reached supported target).mp revealed
  rw [noReveal target.val] at recorded
  cases recorded

set_option backward.isDefEq.respectTransparency false in
/-- An accepted original unissued field in the full modified source result is an ordinary terminal-report eligibility event. Creation-index origin and unrevealed status are derived from the actual client and its capability budget. -/
theorem sourceClient_eligible (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (ordinal count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (identityReads : budget (.inr 0) = 0) (kemReads : budget (.inr 1) = 0)
    (creationCap : 1 + budget (.inl 1) ≤ count) (transcript : Result → List PqxdhDeploymentInterface.Entry)
    (reached : ReportResult KemSK A Result count)
    (supported : reached ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (sourceClient setup codec checks ensureInit none ordinal program runtime)))
    (index : Nat) (publicKey : PublicIdentity) (candidate : Phase1Candidate) (decoded : Phase1KeyTuple)
    (member : candidate ∈ PqxdhDeploymentProvenance.acceptedCandidates codec (finalTranscript transcript reached.1))
    (key : PqxdhDynamicIdentityReports.sourceKeys setup.joint
      (initializedResult (reached.1, reached.2.2.source.2)).2.1.1.seeds index = some publicKey)
    (accepted : acceptPhase1Candidate setup.joint.verify candidate = some (publicKey.ed25519, decoded))
    (unissued : ∃ field ∈ PqxdhJointPhase1Reports.candidateFields candidate,
      field.message ∉ messagesAt index (initializedResult (reached.1, reached.2.2.source.2)).2.1.1.transcript) :
    PqxdhDeploymentPublicationSecurityClient.Eligible setup.joint codec (finalTranscript transcript) reached := by
  have hasSeed := key
  rw [PqxdhDynamicIdentityReports.sourceKeys, Option.map_eq_some_iff] at hasSeed
  obtain ⟨seed, seedFound, _⟩ := hasSeed
  change (reached.1.2.refs.map (PqxdhRegistrationJointIdentityRouting.resolve reached.2.2.source.2.seeds))[index]? = some seed at seedFound
  rw [List.getElem?_map, Option.map_eq_some_iff] at seedFound
  obtain ⟨ref, refFound, _⟩ := seedFound
  obtain ⟨target, rfl⟩ := PqxdhDeploymentPublicationSuppressionGenerated.sourceClient_generated setup codec checks
    ensureInit ordinal count program runtime reached supported ref (List.mem_of_getElem? refFound)
  have creates := PqxdhDeploymentPublicationSuppressionCosts.sourceClient_creates setup codec checks ensureInit none
    ordinal program runtime budget certified
  have countBound := PqxdhDeploymentPublicationSuppressionGenerated.generated_lt setup codec checks ensureInit ordinal count
    program runtime (creates.mono creationCap) reached supported index target refFound
  have free := PqxdhDeploymentPublicationSuppressionCosts.initialized_private setup codec checks ensureInit none ordinal
    program runtime budget certified .other (by decide)
  have zero : (initialized setup codec checks ensureInit none ordinal program runtime).IsQueryBoundP
      (fun query => PqxdhRegistrationJointIdentityCosts.dynamicKind query = .other) 0 := by
    simpa only [PqxdhRegistrationJointOpenCosts.privateTotal, identityReads, kemReads,
      reduceCtorEq, false_and, ite_false, Nat.zero_add, Nat.add_zero] using free
  refine ⟨target, candidate, member, ?_⟩
  exact PqxdhRegistrationJointRoutedReportSource.field_origin setup.joint count _ reached supported index
    ⟨target, countBound⟩ refFound publicKey candidate decoded key accepted
    (sourceClient_fresh setup codec checks ensureInit none ordinal count program runtime zero reached supported ⟨target, countBound⟩)
    unissued

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionEligible

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionEligible.ordinary_unrevealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionEligible.ordinary_unrevealed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionEligible.sourceClient_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionEligible.sourceClient_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionEligible.sourceClient_eligible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionEligible.sourceClient_eligible
