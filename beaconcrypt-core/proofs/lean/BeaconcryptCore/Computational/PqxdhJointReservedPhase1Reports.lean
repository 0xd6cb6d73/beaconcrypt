-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhJointPhase1Reports
import BeaconcryptCore.Computational.PqxdhJointIdentityEvents
import BeaconcryptCore.Computational.RegistrationRootInput
/-! A ghost Phase-1 reporter uses every internally reserved family public key and the same prefix's global signing/reveal history. It keeps the original Nat-indexed CandidateReport and selects an original unissued attached field. No created-key lookup or public Native key publication is required. Reserved keys are known to the reduction internally; this module gives the Native adversary no new query, reply, key or seed and does not identify an actual Context/Main source execution with this observer. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
namespace BeaconcryptCore.Computational.PqxdhJointReservedPhase1Reports
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhJointPhase1Reports (CandidateReport candidateFields selectUnissued)
open PqxdhJointIdentityEvents (ReportEvent)
variable {count : Nat}

/-- Translate the exact original candidate against its reserved public key and full prior signing history. Reveal freshness belongs to ReportEvent, not to source eligibility or parsing. -/
def translateReport (primitives : Primitives) (keys : Fin count → PublicIdentity)
    (report : CandidateReport) (history : GlobalState count) : Option (FamilyForgery count) :=
  if valid : report.identity < count then
    match acceptPhase1Candidate primitives.verify report.candidate with
    | none => none
    | some (candidateKey, _) =>
      if candidateKey = (keys ⟨report.identity, valid⟩).ed25519 then
        (selectUnissued (history.histories ⟨report.identity, valid⟩) report.candidate).map
          fun forgery => ⟨⟨report.identity, valid⟩, forgery⟩
      else none
  else none

/-- Reserved-family field failure at this exact prefix, independent of whether the matching key has been created or published. -/
def FieldOriginFailure (primitives : Primitives) (keys : Fin count → PublicIdentity)
    (report : CandidateReport) (history : GlobalState count) : Prop :=
  ∃ valid : report.identity < count, ∃ decoded,
    acceptPhase1Candidate primitives.verify report.candidate = some ((keys ⟨report.identity, valid⟩).ed25519, decoded) ∧
    (⟨report.identity, valid⟩ : Fin count) ∉ history.reveals ∧
    ∃ forgery ∈ candidateFields report.candidate,
      forgery.message ∉ signedMessages (history.histories ⟨report.identity, valid⟩)

/-- Every returned family report retains the original generated index. -/
theorem translated_index (primitives : Primitives) (keys : Fin count → PublicIdentity)
    (report : CandidateReport) (history : GlobalState count) (forgery : FamilyForgery count)
    (translated : translateReport primitives keys report history = some forgery) : forgery.identity.val = report.identity := by
  unfold translateReport at translated
  split at translated
  · split at translated
    · contradiction
    · split at translated
      · obtain ⟨selected, _, rfl⟩ := Option.map_eq_some_iff.mp translated
        rfl
      · contradiction
  · contradiction

/-- Translation is exactly ordinary report-time weak-EUF for an unrestricted reserved identity; no field, alias or created-key condition is lost. -/
theorem translate_event (primitives : Primitives) (keys : Fin count → PublicIdentity)
    (report : CandidateReport) (history : GlobalState count) :
    (∃ forgery, translateReport primitives keys report history = some forgery ∧ ReportEvent primitives keys forgery history) ↔
      FieldOriginFailure primitives keys report history := by
  by_cases valid : report.identity < count
  · cases accepted : acceptPhase1Candidate primitives.verify report.candidate with
    | none => simp [translateReport, FieldOriginFailure, valid, accepted]
    | some pair =>
      rcases pair with ⟨candidateKey, decoded⟩
      by_cases same : candidateKey = (keys ⟨report.identity, valid⟩).ed25519
      · subst candidateKey
        cases selected : selectUnissued (history.histories ⟨report.identity, valid⟩) report.candidate with
        | none =>
          have allSigned := (PqxdhJointPhase1Reports.selectUnissued_none_iff _ _).mp selected
          simp [translateReport, FieldOriginFailure, valid, accepted, selected]
          intro _
          exact allSigned
        | some forgery =>
          have winning := PqxdhJointPhase1Reports.selected_weak_euf primitives report.candidate
            (keys ⟨report.identity, valid⟩) decoded (history.histories ⟨report.identity, valid⟩) accepted forgery selected
          have unissued : ∃ forgery ∈ candidateFields report.candidate,
              forgery.message ∉ signedMessages (history.histories ⟨report.identity, valid⟩) :=
            ⟨forgery, (PqxdhJointPhase1Reports.selectUnissued_some _ _ _ selected).1,
              (PqxdhJointPhase1Reports.selectUnissued_some _ _ _ selected).2⟩
          simp [translateReport, FieldOriginFailure, valid, accepted, selected, ReportEvent, Fresh, winning, unissued]
      · simp [translateReport, FieldOriginFailure, valid, accepted, same]
  · simp [translateReport, FieldOriginFailure, valid]

def candidateAccepted (primitives : Primitives) (keys : Fin count → PublicIdentity)
    (report : CandidateReport) (history : GlobalState count) : Bool :=
  (translateReport primitives keys report history).any fun forgery => decide (ReportEvent primitives keys forgery history)

/-- The sticky detector can use the original unrestricted reserved-key field-origin event without changing acceptance eligibility. -/
theorem candidateAccepted_iff (primitives : Primitives) (keys : Fin count → PublicIdentity)
    (report : CandidateReport) (history : GlobalState count) :
    candidateAccepted primitives keys report history = true ↔ FieldOriginFailure primitives keys report history := by
  rw [← translate_event]
  simp [candidateAccepted, Option.any_eq_true]

/-- Enumerate every reserved alias matching the original tagged packet identity; no runtime-created roster is consulted. -/
def packetReports (keys : Fin count → PublicIdentity) (packet : registration.InitPacket) : List CandidateReport :=
  (List.ofFn fun index : Fin count => index).filterMap fun index =>
    if encodedIdentity (keys index).ed25519 = PqxdhRefinement.absBytes packet.identity_key then
      some ⟨index.val, RegistrationRootInput.candidate packet⟩
    else none

/-- Every matching reserved alias occurs in the ghost report list, including identities not yet created at this prefix. -/
theorem packet_member (keys : Fin count → PublicIdentity) (packet : registration.InitPacket) (index : Fin count)
    (matched : encodedIdentity (keys index).ed25519 = PqxdhRefinement.absBytes packet.identity_key) :
    (⟨index.val, RegistrationRootInput.candidate packet⟩ : CandidateReport) ∈ packetReports keys packet := by
  apply List.mem_filterMap.mpr
  exact ⟨index, by simp, by simp only [ite_eq_left matched]⟩

/-- Original source acceptance supplies the same tagged identity used by the reserved alias enumerator. -/
theorem packet_accepted (primitives : Primitives) (keys : Fin count → PublicIdentity)
    (packet : registration.InitPacket) (index : Fin count) (decoded : Phase1KeyTuple)
    (accepted : acceptPhase1Candidate primitives.verify (RegistrationRootInput.candidate packet) = some ((keys index).ed25519, decoded)) :
    (⟨index.val, RegistrationRootInput.candidate packet⟩ : CandidateReport) ∈ packetReports keys packet := by
  apply packet_member
  exact (acceptPhase1Candidate_some_witness primitives.verify (RegistrationRootInput.candidate packet)
    (keys index).ed25519 decoded accepted).1.symm

/-- Any fresh original field under any reserved target yields the ordinary fresh FamilyForgery in this same packet/prefix report list, without guessing an alias or field. -/
theorem packet_cover (primitives : Primitives) (keys : Fin count → PublicIdentity)
    (history : GlobalState count) (packet : registration.InitPacket) (index : Fin count) (decoded : Phase1KeyTuple)
    (accepted : acceptPhase1Candidate primitives.verify (RegistrationRootInput.candidate packet) = some ((keys index).ed25519, decoded))
    (fresh : index ∉ history.reveals)
    (unissued : ∃ forgery ∈ candidateFields (RegistrationRootInput.candidate packet),
      forgery.message ∉ signedMessages (history.histories index)) :
    ∃ report ∈ packetReports keys packet, ∃ forgery : Forgery,
      translateReport primitives keys report history = some ⟨index, forgery⟩ ∧
      ReportEvent primitives keys ⟨index, forgery⟩ history ∧
      forgery ∈ candidateFields (RegistrationRootInput.candidate packet) ∧
      forgery.message ∉ signedMessages (history.histories index) := by
  cases selected : selectUnissued (history.histories index) (RegistrationRootInput.candidate packet) with
  | none =>
    obtain ⟨forgery, member, notSigned⟩ := unissued
    exact False.elim (notSigned ((PqxdhJointPhase1Reports.selectUnissued_none_iff _ _).mp selected forgery member))
  | some forgery =>
    have selectedFields := PqxdhJointPhase1Reports.selectUnissued_some _ _ forgery selected
    refine ⟨⟨index.val, RegistrationRootInput.candidate packet⟩, packet_accepted primitives keys packet index decoded accepted,
      forgery, ?_, ?_, selectedFields.1, selectedFields.2⟩
    · simp [translateReport, index.isLt, accepted, selected]
    · exact ⟨fresh, PqxdhJointPhase1Reports.selected_weak_euf primitives (RegistrationRootInput.candidate packet)
        (keys index) decoded (history.histories index) accepted forgery selected⟩
private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl
private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let value ← work before; next value.1 value.2) := rfl

abbrev ProtocolSpec (count : Nat) := GlobalSpec count + PqxdhJointPhase1Reports.CandidateSpec

/-- A public observer forwards every actual family service/reveal and emits at most one existing family report per unchanged original candidate. It knows only reserved public keys and observed history. -/
def wrapper (primitives : Primitives) (keys : Fin count → PublicIdentity) :
    QueryImpl (ProtocolSpec count) (StateT (GlobalState count) (OracleComp (PqxdhJointIdentityEvents.ReportingSpec count))) := fun query history =>
  match query with
  | .inl request => do
    let answer ← (PqxdhJointIdentityEvents.ReportingSpec count).query (.inl request)
    pure (answer, PqxdhJointIdentityEvents.publicUpdate request answer history)
  | .inr report => do
    match translateReport primitives keys report history with
    | none => pure ()
    | some forgery => (PqxdhJointIdentityEvents.ReportingSpec count).query (.inr forgery)
    pure ((), history)

def routedClient {A : Type} (primitives : Primitives) (keys : Fin count → PublicIdentity)
    (client : OracleComp (ProtocolSpec count) A) (history : GlobalState count) :
    OracleComp (PqxdhJointIdentityEvents.ReportingSpec count) (A × GlobalState count) :=
  (simulateQ (wrapper primitives keys) client).run history

/-- The wrapper's history is the exact history of the existing family service interpreter after every service, reveal or original candidate, with no creation condition. -/
theorem wrapper_source_preserves (primitives : Primitives) (seeds : Fin count → IdentitySeed)
    (query : (ProtocolSpec count).Domain) (history : GlobalState count)
    (before : PqxdhJointIdentityEvents.ReportingState count) (same : history = before.publicState)
    (result : ((ProtocolSpec count).Range query × GlobalState count) × PqxdhJointIdentityEvents.ReportingState count)
    (supported : result ∈ support ((simulateQ (PqxdhJointIdentityEvents.reportingImpl primitives seeds)
      ((wrapper primitives (familyPublic primitives seeds) query).run history)).run before)) :
    result.1.2 = result.2.publicState := by
  cases query with
  | inl request =>
    simp only [wrapper, StateT.run, simulateQ_bind, simulateQ_spec_query,
      PqxdhJointIdentityEvents.reportingImpl, bind_apply, pure_apply, simulateQ_pure, bind_assoc, pure_bind] at supported
    rw [mem_support_bind_iff] at supported
    obtain ⟨actual, reached, returned⟩ := supported
    rw [mem_support_pure_iff] at returned
    cases returned
    simpa only [same] using (PqxdhJointIdentityEvents.sourceImpl_publicUpdate primitives seeds request before.publicState actual reached).symm
  | inr report =>
    cases translated : translateReport primitives (familyPublic primitives seeds) report history with
    | none =>
      simp only [wrapper, translated, StateT.run, simulateQ_pure, pure_apply, mem_support_pure_iff] at supported
      cases supported
      exact same
    | some forgery =>
      simp only [wrapper, translated, StateT.run, simulateQ_bind, simulateQ_spec_query,
        PqxdhJointIdentityEvents.reportingImpl, bind_apply, pure_bind, simulateQ_pure,
        pure_apply, mem_support_pure_iff] at supported
      cases supported
      exact same

/-- A genuine unrestricted reserved-key field failure sets the existing family reporting event in that same prefix; no later reveal can undo this sticky event. -/
theorem wrapper_report_marks (primitives : Primitives) (seeds : Fin count → IdentitySeed)
    (report : CandidateReport) (history : GlobalState count)
    (before : PqxdhJointIdentityEvents.ReportingState count) (same : history = before.publicState)
    (failed : FieldOriginFailure primitives (familyPublic primitives seeds) report history)
    (result : (Unit × GlobalState count) × PqxdhJointIdentityEvents.ReportingState count)
    (supported : result ∈ support ((simulateQ (PqxdhJointIdentityEvents.reportingImpl primitives seeds)
      ((wrapper primitives (familyPublic primitives seeds) (.inr report)).run history)).run before)) :
    result.2.occurred = true := by
  obtain ⟨forgery, translated, event⟩ := (translate_event primitives _ report history).mpr failed
  simp only [wrapper, translated, StateT.run, simulateQ_bind, simulateQ_spec_query,
    PqxdhJointIdentityEvents.reportingImpl, bind_apply, pure_bind, simulateQ_pure,
    pure_apply, mem_support_pure_iff] at supported
  cases supported
  have event' : ReportEvent primitives (familyPublic primitives seeds) forgery before.publicState := by
    simpa only [same] using event
  simp only [event', decide_true, Bool.or_true]

/-- Every adaptive observer continuation retains the same entire family signing/reveal history, including all later services and compromise. -/
theorem program_source_preserves {A : Type} (primitives : Primitives) (seeds : Fin count → IdentitySeed)
    (work : OracleComp (ProtocolSpec count) A) (history : GlobalState count)
    (before : PqxdhJointIdentityEvents.ReportingState count) (same : history = before.publicState)
    (result : (A × GlobalState count) × PqxdhJointIdentityEvents.ReportingState count)
    (supported : result ∈ support ((simulateQ (PqxdhJointIdentityEvents.reportingImpl primitives seeds)
      (routedClient primitives (familyPublic primitives seeds) work history)).run before)) :
    result.1.2 = result.2.publicState := by
  induction work using OracleComp.inductionOn generalizing history before result with
  | pure value =>
    simp only [routedClient, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact same
  | query_bind query next ih =>
    simp only [routedClient, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, first, last⟩ := supported
    exact ih middle.1.1 middle.1.2 middle.2 (wrapper_source_preserves primitives seeds query history before same middle first) result last
end BeaconcryptCore.Computational.PqxdhJointReservedPhase1Reports

/-- info: 'BeaconcryptCore.Computational.PqxdhJointReservedPhase1Reports.translated_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointReservedPhase1Reports.translated_index

/-- info: 'BeaconcryptCore.Computational.PqxdhJointReservedPhase1Reports.translate_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointReservedPhase1Reports.translate_event

/-- info: 'BeaconcryptCore.Computational.PqxdhJointReservedPhase1Reports.candidateAccepted_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointReservedPhase1Reports.candidateAccepted_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhJointReservedPhase1Reports.packet_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointReservedPhase1Reports.packet_member

/-- info: 'BeaconcryptCore.Computational.PqxdhJointReservedPhase1Reports.packet_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointReservedPhase1Reports.packet_accepted

/-- info: 'BeaconcryptCore.Computational.PqxdhJointReservedPhase1Reports.packet_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointReservedPhase1Reports.packet_cover

/-- info: 'BeaconcryptCore.Computational.PqxdhJointReservedPhase1Reports.wrapper_source_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointReservedPhase1Reports.wrapper_source_preserves

/-- info: 'BeaconcryptCore.Computational.PqxdhJointReservedPhase1Reports.wrapper_report_marks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointReservedPhase1Reports.wrapper_report_marks

/-- info: 'BeaconcryptCore.Computational.PqxdhJointReservedPhase1Reports.program_source_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointReservedPhase1Reports.program_source_preserves
