-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone
import BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptOrigin
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills

/-! The authenticated selected-KEM bound at the raw-accept ordinal (theorem T5), its query bills (theorem T5b) and the final classification. The target is the fixed public pair of the raw-accept ordinal `index` and the KEM creation index `kemIndex`. The event is read in the report-instrumented coupling `AcceptCutReports.split` of the tagged program, whose final component is the report run of the tagged program and whose source projection is the unmodified actual initialized execution: the selected raw accept returned a session, the adversary decision holds, KEM key `kemIndex` was never disclosed in the whole run, and the accept is protected at the cut (`AcceptOrigin.Protected`, read in the state reached immediately before the selected accept). Its probability is at most the KEM-ideal probability, plus one ordinary one-key ML-KEM IND-CCA advantage of the proof-carrying raw-ordinal adversary, plus one ordinary ML-KEM correctness error, plus the sum over all `count + 1` generated positions of the ordinary joint-use weak-EUF advantage. No honest-target premise is used; the inherited contracts are `shortRejects` with `setup.wiring` and `FunctionalDecapsulation`. No KDF game is formed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem
open PqxdhKemIndCca PqxdhInitializerSecrecy
open PqxdhJointIdentity PqxdhDynamicIdentityPool PqxdhServerAuthExperiment
open PqxdhDynamicIdentityReports PqxdhDynamicIdentityRouting PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhEd25519EufCma
open PqxdhRegistrationJointRevealSchedule (Spec)
open PqxdhRegistrationJointAcceptCut (Cut scan selected)
open PqxdhRegistrationJointAcceptCutTag (Tag tag tagFinish accepted)
open PqxdhRegistrationJointAcceptCutReports (split mapChoice)
open PqxdhRegistrationJointInitializedReports (ReportResult sourceResult)
open PqxdhRegistrationJointAcceptOrigin (Protected HonestTuple KeyMatchCut VerifiedSome)
open PqxdhRegistrationJointKemRawBridge (Final Decided GoodKem KeyMatchFinal)
open PqxdhRegistrationJointRawSignatures (verified)
open PqxdhRegistrationJointFinalCandidate (client)
open PqxdhRegistrationJointNativeOriginBound (reduction)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhRegistrationJointIdentityUniform (total)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Reader Response X : Type}

/-- The selected raw accept returned a session in the final source result. -/
def AcceptedFinal (final : Final KemSK A X) : Prop :=
  ∃ outcome, final.1 = some outcome ∧ accepted outcome.2.1.2 = true

/-- In the coupling, a final source outcome comes from a reached initialized outcome at the cut, and its program result is a result of the recording finish of the reached cut. -/
theorem resume_outcome (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (runtime : A)
    (pair : ReportResult KemSK A (Cut KemSK X) count × ReportResult KemSK A (X × Tag) count)
    (supported : pair ∈ support (split setup codec checks ensureInit supplied count work index runtime))
    (final : PqxdhRegistrationJointInitializedSchedule.Outcome KemSK (X × Tag))
    (finished : (sourceResult pair.2).1 = some final) :
    ∃ encoded, (sourceResult pair.1).1 = some encoded ∧ final.2.1 ∈ support (tagFinish encoded.2.1) := by
  simp only [split, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨reached, _, last, continued, rfl⟩ := supported
  dsimp only at finished ⊢
  have reduced : last.1 ∈ support (PqxdhRegistrationJointReportCompiler.reduction setup ensureInit
      (PqxdhRegistrationJointAcceptCutReports.resume setup codec checks count tagFinish reached.1.1.1) reached.1.1.2
      reached.1.2) := by
    apply support_simulateQ_run'_subset (PqxdhJointPhase1Reports.sourceImpl setup.joint count) _ reached.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ continued
  have compiled : last.1.1 ∈ support ((simulateQ (PqxdhRegistrationJointReportLift.extend
      (PqxdhRegistrationJointIdentityCompiler.impl setup ensureInit))
      (PqxdhRegistrationJointAcceptCutReports.resume setup codec checks count tagFinish reached.1.1.1)).run
        reached.1.1.2) := by
    apply support_simulateQ_run'_subset (PqxdhRegistrationJointReportLift.extend
      (PqxdhRegistrationJointIdentityRouting.route setup.joint)) _ reached.1.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ reduced
  have resumed : last.1.1.1 ∈ support
      (PqxdhRegistrationJointAcceptCutReports.resume setup codec checks count tagFinish reached.1.1.1) := by
    apply support_simulateQ_run'_subset (PqxdhRegistrationJointReportLift.extend
      (PqxdhRegistrationJointIdentityCompiler.impl setup ensureInit)) _ reached.1.1.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ compiled
  rcases equation : reached.1.1.1 with _ | outcome
  · rw [equation, PqxdhRegistrationJointAcceptCutReports.resume, mem_support_pure_iff] at resumed
    simp [sourceResult, PqxdhRegistrationJointIdentityCompiler.initializedResult,
      PqxdhRegistrationJointIdentityCompiler.projectResult, resumed] at finished
  · rw [equation, PqxdhRegistrationJointAcceptCutReports.resume, support_map] at resumed
    obtain ⟨result, reportedRun, same⟩ := resumed
    have recorded := PqxdhRegistrationJointAcceptCutMonotone.reported_result setup codec checks _ _ count _ _ result
      reportedRun
    simp only [sourceResult, PqxdhRegistrationJointIdentityCompiler.initializedResult,
      PqxdhRegistrationJointIdentityCompiler.projectResult, ← same, Option.map_some, Option.some.injEq] at finished
    subst finished
    have cutFound : (sourceResult reached).1 =
        some (PqxdhRegistrationJointOpenInitialization.attach (sourceResult reached).2.1 outcome) := by
      simp only [sourceResult, PqxdhRegistrationJointIdentityCompiler.initializedResult,
        PqxdhRegistrationJointIdentityCompiler.projectResult, equation, Option.map_some]
    exact ⟨_, cutFound, recorded⟩

/-- The final source result of the report run of the tagged program is a result of the actual initialized source client of the tagged program. -/
theorem report_client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (runtime : A) (final : ReportResult KemSK A (X × Tag) count)
    (supported : final ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count (tag work index)
        runtime))) :
    sourceResult final ∈ support ((PqxdhRegistrationJointInitializedSchedule.client setup codec checks ensureInit
      supplied (tag work index)).run ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)) := by
  rw [PqxdhRegistrationJointInitializedSchedule.initialized_source,
    ← PqxdhRegistrationJointReportSource.initialized_source setup codec checks ensureInit supplied count, support_map]
  exact Set.mem_image_of_mem _ supported

/-- A selected raw accept that returned a session in the final outcome of the coupling was pending at the cut and its attached verification succeeded: every rejection, including rejection after a successful attached verification, ends without a session. -/
theorem accepted_verified (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (runtime : A)
    (pair : ReportResult KemSK A (Cut KemSK X) count × ReportResult KemSK A (X × Tag) count)
    (supported : pair ∈ support (split setup codec checks ensureInit supplied count work index runtime))
    (session : AcceptedFinal (sourceResult pair.2)) : VerifiedSome setup codec checks pair.1 := by
  obtain ⟨final, finished, acceptedSession⟩ := session
  obtain ⟨encoded, reached, recorded⟩ := resume_outcome setup codec checks ensureInit supplied count work index runtime
    pair supported final finished
  have finalRun : pair.2 ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count (tag work index)
        runtime)) := by
    rw [← PqxdhRegistrationJointAcceptCutReports.split_snd setup codec checks ensureInit supplied count work index
      runtime, support_map]
    exact Set.mem_image_of_mem _ supported
  obtain ⟨raw', answer', value, tagged, checked⟩ := PqxdhRegistrationJointKemRawBridge.client_tag setup codec checks
    ensureInit supplied work index _ (sourceResult pair.2)
    (report_client setup codec checks ensureInit supplied count work index runtime pair.2 finalRun) final finished
    acceptedSession
  rcases cut : encoded.2.1 with result | ⟨raw, next⟩
  · rw [cut, tagFinish, mem_support_pure_iff] at recorded
    rw [recorded] at tagged
    cases tagged
  · rw [cut, tagFinish, mem_support_bind_iff] at recorded
    obtain ⟨answer, _, recorded⟩ := recorded
    rw [support_map] at recorded
    obtain ⟨output, _, recorded⟩ := recorded
    rw [← recorded] at tagged
    simp only [Option.some.injEq, Prod.mk.injEq] at tagged
    obtain ⟨rfl, -⟩ := tagged
    exact ⟨encoded, raw, next, value, reached, cut, checked⟩

/-- Final classification on the coupling (theorem T1 with the rejection class separated). Every coupled execution satisfies at least one of four cases: the selected raw accept returned no session in the final outcome, which covers constructor failure, completion before the selected accept, a rejected attached verification and every rejection after a successful attached verification and before or after encapsulation; or it returned a session, its attached verification succeeded at the cut, and the cut is attacker-owned or otherwise unprotected, or protected with an issued tuple of the witness owner whose PQ key is the native KEM key at `kemIndex`, or protected with the address-free final-report failure of the mapped selected outcome. The cases are not exclusive. -/
theorem classify_final (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (runtime : A)
    (pair : ReportResult KemSK A (Cut KemSK X) count × ReportResult KemSK A (X × Tag) count)
    (supported : pair ∈ support (split setup codec checks ensureInit supplied count work index runtime))
    (kemIndex : Fin count) (chosenOwner : Nat) (fallback : Pqxdh.Bytes) :
    ¬AcceptedFinal (sourceResult pair.2) ∨
      (AcceptedFinal (sourceResult pair.2) ∧ VerifiedSome setup codec checks pair.1 ∧
        ¬Protected setup codec checks kemIndex pair.1) ∨
      (AcceptedFinal (sourceResult pair.2) ∧ Protected setup codec checks kemIndex pair.1 ∧
        HonestTuple setup codec checks kemIndex pair.1 ∧ KeyMatchCut setup codec checks kemIndex pair.1) ∨
      (AcceptedFinal (sourceResult pair.2) ∧ Protected setup codec checks kemIndex pair.1 ∧
        PqxdhRegistrationJointFinalReportEvent.Failure setup.joint codec (mapChoice chosenOwner fallback pair.1)) := by
  by_cases session : AcceptedFinal (sourceResult pair.2)
  · have checkedCut := accepted_verified setup codec checks ensureInit supplied count work index runtime pair
      supported session
    have reachedCut : pair.1 ∈ support (PqxdhJointPhase1Reports.run setup.joint count
        (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count (scan work index)
          runtime)) := by
      simp only [split, mem_support_bind_iff, mem_support_pure_iff] at supported
      obtain ⟨reached, reachedRun, _, _, rfl⟩ := supported
      exact reachedRun
    obtain ⟨encoded, raw, next, value, finished, pending, checked⟩ := checkedCut
    rcases PqxdhRegistrationJointAcceptOrigin.classify setup codec checks shortRejects ensureInit supplied count work
        index runtime pair.1 reachedCut kemIndex chosenOwner fallback with
      complete | rejected | unprotected | honest | forged
    · rcases complete with absent | ⟨encoded', result, finished', cut⟩
      · rw [finished] at absent
        cases absent
      · rw [finished, Option.some.injEq] at finished'
        subst finished'
        rw [pending] at cut
        cases cut
    · obtain ⟨encoded', raw', next', finished', pending', unchecked⟩ := rejected
      rw [finished, Option.some.injEq] at finished'
      subst finished'
      rw [pending, PqxdhRegistrationJointAcceptCut.Cut.pending.injEq] at pending'
      obtain ⟨rfl, -⟩ := pending'
      rw [checked] at unchecked
      cases unchecked
    · exact Or.inr (Or.inl ⟨session, unprotected⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨session, honest⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨session, forged⟩))
  · exact Or.inl session

/-- Protection is not needed here: in the coupling, a verified pending cut whose PQ key is the native KEM key at `kemIndex` at the cut ends with a final outcome whose recorded raw bytes are those of the cut and whose final pool key at `kemIndex` is the same key, because the pool only grows. -/
theorem protected_to_final (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (runtime : A)
    (pair : ReportResult KemSK A (Cut KemSK X) count × ReportResult KemSK A (X × Tag) count)
    (supported : pair ∈ support (split setup codec checks ensureInit supplied count work index runtime))
    (kemIndex : Fin count) (matched : KeyMatchCut setup codec checks kemIndex pair.1) :
    KeyMatchFinal setup codec checks kemIndex (sourceResult pair.2) := by
  obtain ⟨encoded, raw, next, value, finished, pending, checked, keyed⟩ := matched
  obtain ⟨final, answer, finalFound, tagged⟩ := PqxdhRegistrationJointAcceptCutMonotone.resume_tag setup codec checks
    ensureInit supplied count work index runtime pair supported encoded raw next finished pending
  have grown := PqxdhRegistrationJointAcceptCutMonotone.resume_keys_prefix setup codec checks ensureInit supplied count
    work index runtime pair supported
  obtain ⟨pairKey, foundKey, first⟩ := Option.map_eq_some_iff.mp keyed
  refine ⟨final, raw, answer, value, finalFound, tagged, checked, ?_⟩
  rw [PqxdhRegistrationJointKemRawBridge.prefix_lookup grown foundKey, Option.map_some, first]

/-- Final-component marginal of the coupling: every final-state event has, in the coupling, exactly its probability in the actual initialized source execution of the tagged program, by `AcceptCutReports.split_snd` and `ReportSource.initialized_source`. -/
theorem final_marginal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (runtime : A) (event : Final KemSK A X → Prop) :
    letI := Classical.propDecidable
    𝒟[(fun pair => decide (event (sourceResult pair.2))) <$>
      split setup codec checks ensureInit supplied count work index runtime] {true} =
    𝒟[(fun final => decide (event final)) <$>
      ((fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), result.2)) <$>
        (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied (tag work index)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true} := by
  rw [← PqxdhRegistrationJointReportSource.initialized_source setup codec checks ensureInit supplied count
    (tag work index) runtime, Functor.map_map,
    ← PqxdhRegistrationJointAcceptCutReports.split_snd setup codec checks ensureInit supplied count work index runtime,
    Functor.map_map]
  congr

/-- Cut-component marginal of the coupling: every cut-time event has, in the coupling, exactly its probability in the report run of the raw-accept scan, by `AcceptCutReports.split_fst`. -/
theorem cut_marginal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (runtime : A)
    (event : ReportResult KemSK A (Cut KemSK X) count → Prop) :
    letI := Classical.propDecidable
    𝒟[(fun pair => decide (event pair.1)) <$>
      split setup codec checks ensureInit supplied count work index runtime] {true} =
    𝒟[(fun reached => decide (event reached)) <$> PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count (scan work index)
        runtime)] {true} := by
  classical
  exact congrArg (fun measure => measure {true}) (PqxdhRegistrationJointAcceptCutReports.split_fst setup codec checks
    ensureInit supplied count work index runtime (fun reached => decide (event reached)))

/-- Union step on the coupling: the main event implies either the final-state event with a final key match, or protection without a key match at the cut, because a key match at the cut carries over to the final outcome (`protected_to_final`). -/
theorem union_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (runtime : A) (decision : X → Bool) (kemIndex : Fin count) :
    letI := Classical.propDecidable
    𝒟[(fun pair => decide (Decided decision (sourceResult pair.2) ∧ GoodKem kemIndex (sourceResult pair.2) ∧
        Protected setup codec checks kemIndex pair.1)) <$>
      split setup codec checks ensureInit supplied count work index runtime] {true} ≤
    𝒟[(fun pair => decide (Decided decision (sourceResult pair.2) ∧ GoodKem kemIndex (sourceResult pair.2) ∧
        KeyMatchFinal setup codec checks kemIndex (sourceResult pair.2))) <$>
      split setup codec checks ensureInit supplied count work index runtime] {true} +
    𝒟[(fun pair => decide (Protected setup codec checks kemIndex pair.1 ∧
        ¬KeyMatchCut setup codec checks kemIndex pair.1)) <$>
      split setup codec checks ensureInit supplied count work index runtime] {true} := by
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true,
    ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map, prEvent_map]
  refine le_trans (prEvent_mono_of_support _ _ _ ?_) (prEvent_or_le _ _ _)
  intro pair supported event
  simp only [decide_eq_true_eq] at event ⊢
  obtain ⟨decided, good, protects⟩ := event
  by_cases matched : KeyMatchCut setup codec checks kemIndex pair.1
  · exact Or.inl ⟨decided, good, protected_to_final setup codec checks ensureInit supplied count work index runtime
      pair supported kemIndex matched⟩
  · exact Or.inr ⟨protects, matched⟩

/-- Theorem T5. For the fixed public raw-accept ordinal `index` and KEM creation index `kemIndex`, the probability in the report-instrumented coupling of the tagged program (whose final component is the report run of the tagged program and whose source projection is the unmodified actual initialized execution) that the selected raw accept returned a session, the adversary decision holds, KEM key `kemIndex` was never disclosed and the accept is protected at the cut is at most the probability that the raw-ordinal KEM-ideal branch returns `true`, plus one ordinary one-key ML-KEM IND-CCA advantage of the proof-carrying raw-ordinal adversary, plus one ordinary ML-KEM correctness error, plus the sum over all `count + 1` generated positions of the ordinary joint-use weak-EUF advantage of the native-origin reduction of the selected prefix. Protection is read at the cut and KEM freshness over the whole run. -/
theorem authenticated_selected_kem (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (runtime : A) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (capacity : (if supplied.isNone then 1 else 0) + budget (.inl 1) ≤ count + 1)
    (decision : X → Bool) (kemIndex : Fin (count + 1)) (chosenOwner : Nat) (fallback : Pqxdh.Bytes)
    (dynamicFallback : DynamicForgery) (ordinaryFallback : Forgery) :
    (letI := Classical.propDecidable; 𝒟[(fun pair => decide (Decided decision (sourceResult pair.2) ∧
        GoodKem kemIndex (sourceResult pair.2) ∧ Protected setup codec checks kemIndex pair.1)) <$>
      split setup codec checks ensureInit supplied (count + 1) work index runtime] {true}) ≤
    𝒟[PqxdhRegistrationJointKemRawGame.branch setup codec checks ensureInit supplied decision work runtime count
        kemIndex index false] {true} +
      ENNReal.ofReal ((setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit supplied decision work runtime
          count kemIndex index).toINDCCA).toReal +
        PqxdhRegistrationJointKemRawGame.correctnessError setup) +
      ∑ target : Fin (count + 1), advantage setup.joint
        (reduction setup codec checks ensureInit supplied count (selected work index chosenOwner fallback) runtime
          dynamicFallback ordinaryFallback target) := by
  refine le_trans (union_split setup codec checks ensureInit supplied (count + 1) work index runtime decision kemIndex)
    (add_le_add ?_ ?_)
  · refine le_of_eq_of_le (final_marginal setup codec checks ensureInit supplied (count + 1) work index runtime
      (fun final => Decided decision final ∧ GoodKem kemIndex final ∧ KeyMatchFinal setup codec checks kemIndex final))
      (le_trans (PqxdhRegistrationJointKemRawBridge.actual_le_real setup codec checks ensureInit supplied decision work
        runtime budget certified count kemIndex index (le_trans (Nat.le_add_left _ _) capacity)) ?_)
    exact PqxdhRegistrationJointKemRawCertified.real_le_ideal setup functional codec checks ensureInit supplied decision
      work runtime count kemIndex index
  · exact le_of_eq_of_le (cut_marginal setup codec checks ensureInit supplied (count + 1) work index runtime
      (fun reached => Protected setup codec checks kemIndex reached ∧ ¬KeyMatchCut setup codec checks kemIndex reached))
      (PqxdhRegistrationJointAcceptOrigin.protected_bound setup codec checks shortRejects ensureInit supplied count work
        runtime index budget certified capacity kemIndex chosenOwner fallback dynamicFallback ordinaryFallback)

/-- Theorem T5b. The query bills of every reduction in theorem T5, for the same program, ordinal, KEM index, decision, owner constant and fallbacks: the proof-carrying raw-ordinal KEM adversary has exactly the caps of `KemReductionBills.adversary_bound`, and every native-origin reduction of the selected prefix and its report client have the signing, converted-DH, public-report and uniform bills of `AcceptCutEuf`. It adds no bound; it collects the existing guarded bills. -/
theorem authenticated_selected_kem_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (count : Nat) (work : OracleComp (Spec KemSK) X) (runtime : A) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (decision : X → Bool) (kemIndex : Fin (count + 1)) (chosenOwner : Nat) (fallback : Pqxdh.Bytes)
    (dynamicFallback : DynamicForgery) (ordinaryFallback : Forgery) :
    (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit supplied decision work runtime
      count kemIndex index).MakesAtMostQueries
      ((qInit + if supplied.isNone then 32 else 0) +
        (caps.keygenCost * count + PqxdhRegistrationJointKemPostBills.uniformCap caps (budget (.inl 1))
          (budget (.inl 5)) (PqxdhRegistrationJointOpenUniform.total caps budget) (budget (.inl 3))))
      (caps.decapsBase * budget (.inl 5)) (budget (.inl 5))
      (PqxdhRegistrationJointKemPostBills.uniformCap caps (budget (.inl 1)) (budget (.inl 5))
        (PqxdhRegistrationJointOpenUniform.total caps budget) (budget (.inl 3)))
      (caps.decapsBase * budget (.inl 5)) (budget (.inl 5)) ∧
    (∀ (target : Fin (count + 1)) (jointPublic : PublicIdentity) (signing : Bool),
      (reduction setup codec checks ensureInit supplied count (selected work index chosenOwner fallback) runtime
        dynamicFallback ordinaryFallback target jointPublic).IsQueryBoundP
        (IsClass (if signing then .sign else .staticDh))
        (if signing then 3 * budget (.inl 2) else budget (.inl 5) + budget (.inl 3))) ∧
    (client setup codec checks ensureInit supplied (count + 1) (selected work index chosenOwner fallback)
      runtime).IsQueryBoundP PqxdhJointPhase1Reports.IsCandidateReport ((count + 1) * (budget (.inl 3) + 1)) ∧
    (client setup codec checks ensureInit supplied (count + 1) (selected work index chosenOwner fallback)
      runtime).IsQueryBoundP (PqxdhJointPhase1Reports.SourceClass (dynamicClass (IsClass .uniform)))
        (total caps qInit budget) ∧
    (∀ (target : Fin (count + 1)) (jointPublic : PublicIdentity),
      (reduction setup codec checks ensureInit supplied count (selected work index chosenOwner fallback) runtime
        dynamicFallback ordinaryFallback target jointPublic).IsQueryBoundP
        (IsClass .uniform) (32 * count + total caps qInit budget)) ∧
    (∀ target : Fin (count + 1),
      (game setup.joint (reduction setup codec checks ensureInit supplied count (selected work index chosenOwner fallback)
        runtime dynamicFallback ordinaryFallback target)).IsTotalQueryBound
          (32 * (count + 1) + total caps qInit budget)) :=
  ⟨PqxdhRegistrationJointKemRawBills.adversary_bound setup codec checks caps bounded ensureInit qInit initBound
      supplied decision work budget certified runtime count kemIndex index,
    fun target jointPublic signing => PqxdhRegistrationJointAcceptCutEuf.selected_service_bound setup codec checks
      ensureInit supplied count work runtime index chosenOwner fallback budget certified dynamicFallback ordinaryFallback
      target jointPublic signing,
    PqxdhRegistrationJointAcceptCutEuf.selected_reports_bound setup codec checks ensureInit supplied count work runtime
      index chosenOwner fallback budget certified,
    PqxdhRegistrationJointAcceptCutEuf.selected_client_uniform setup codec checks ensureInit qInit initBound caps bounded
      supplied count work runtime index chosenOwner fallback budget certified,
    fun target jointPublic => PqxdhRegistrationJointAcceptCutEuf.selected_reduction_uniform setup codec checks
      ensureInit qInit initBound caps bounded supplied count work runtime index chosenOwner fallback budget certified
      dynamicFallback ordinaryFallback target jointPublic,
    fun target => PqxdhRegistrationJointAcceptCutEuf.selected_game_uniform setup codec checks ensureInit qInit initBound
      caps bounded supplied count work runtime index chosenOwner fallback budget certified dynamicFallback
      ordinaryFallback target⟩

end BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem.resume_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem.resume_outcome

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem.report_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem.report_client

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem.accepted_verified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem.accepted_verified

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem.classify_final' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem.classify_final

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem.protected_to_final' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem.protected_to_final

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem.final_marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem.final_marginal

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem.cut_marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem.cut_marginal

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem.union_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem.union_split

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem.authenticated_selected_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem.authenticated_selected_kem

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem.authenticated_selected_kem_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem.authenticated_selected_kem_bills
