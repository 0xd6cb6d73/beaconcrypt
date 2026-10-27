import BeaconcryptCore.Computational.PqxdhLaterChallengePrefixInput

/-! Publication observations along the actual captured wrapper prefix. The source callbacks retain the full frontend and backend, and labels are read at the request that publishes them. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeCapturePublication
open PqxdhInitialPostContext PqxdhRecordConfidentialityChallenge PqxdhRecordConfidentialityTrace
open PqxdhFirstRecordConfidentiality (AdvSpec ConfPostSpec)
variable {ι M P I D K X Response Shared Local Result : Type} {extra : OracleSpec ι} {S B : Nat}
variable (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (impl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT Local ProbComp))
local notation "Full" => (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Bool S B) × Local
local notation "postImpl" => PqxdhLaterChallengeCutChronology.postImpl mark sender route decode impl

/-- A new marked publication is exactly the original callback's public record and the marker installed before that callback. Other callbacks keep the publication trace. -/
theorem step_publication (query : (PqxdhInitialGenericPost.Spec extra S B).Domain)
    (before : Full) (result : (PqxdhInitialGenericPost.Spec extra S B).Range query × Full)
    (supported : result ∈ support (((postImpl) query).run before))
    (publication : RawCtxPublishedRecords.Publication S B) :
    (publication, true) ∈ result.2.1.2.published ↔
      (publication, true) ∈ before.1.2.published ∨
      publication ∈ publications query result.1 ∧ before.1.2.installed publication.1 = some true := by
  simp only [PqxdhLaterChallengeCutChronology.postImpl, StateT.run, support_map] at supported
  obtain ⟨actual, reached, rfl⟩ := supported
  rcases query with (query | query) | ⟨index, raw⟩
  all_goals simp only [PqxdhInitialOriginPost.compiler, StateT.run, bind_pure_comp, simulateQ_map] at reached
  all_goals change actual ∈ support (StateT.run _ before.2) at reached
  all_goals rw [StateT.run_map, support_map] at reached
  all_goals obtain ⟨completed, _, rfl⟩ := reached
  · exact PqxdhInitialOriginPost.record_member before.1.2 query completed.1.1 publication true
  · simp only [publications, List.not_mem_nil, false_and, or_false]
  · cases tag : completed.1.2 <;> simp only [PqxdhInitialOriginPost.finish, tag,
      publications, List.not_mem_nil, false_and, or_false]

/-- After the original challenge, a clear reached wrapper prefix cannot add another target publication. Every completed source callback is retained. -/
theorem used_prefix (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (client rest : OracleComp (AdvSpec extra S B) Result) (before current : State)
    (ambient reached : Full)
    (traced : Reaches postImpl owner number bit client before ambient rest current reached)
    (used : before.pair.isSome) (clear : current.otherTarget = false) :
    ((owner, number), true) ∈ reached.1.2.published ↔
      ((owner, number), true) ∈ ambient.1.2.published := by
  induction traced with
  | here => rfl
  | later query next before ambient step rest current reached actual tail ih =>
      have kept := PqxdhLaterChallengePaths.reaches_kept postImpl owner number bit
        (next step.1.1) rest step.1.2 current step.2 reached tail
      rcases query with query | ⟨left, right⟩
      · simp only [handler, StateT.run, bind_pure_comp, simulateQ_map, simulateQ_spec_query] at actual
        change step ∈ support (StateT.run _ ambient) at actual
        rw [StateT.run_map, support_map] at actual
        obtain ⟨reply, returned, rfl⟩ := actual
        have excluded := ((observe_target owner number before query reply.1).mp (kept.2 clear)).2
        exact (ih used clear).trans (by
          simpa only [excluded, false_and, or_false] using
            step_publication mark sender route decode impl query ambient reply returned (owner, number))
      · simp only [handler, StateT.run, used, true_or, ite_true, simulateQ_pure] at actual
        change step ∈ support (pure ((none, before), ambient)) at actual
        simp only [mem_support_pure_iff] at actual
        subst step
        exact ih used clear

/-- Before the chosen challenge, a clear original wrapper prefix retains the old target-publication membership. Malformed attempts remain actual pure refusals. -/
theorem unused_prefix (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (client rest : OracleComp (AdvSpec extra S B) Result) (before current : State)
    (ambient reached : Full)
    (traced : Reaches postImpl owner number bit client before ambient rest current reached)
    (unused : current.pair = none) (clear : current.otherTarget = false) :
    ((owner, number), true) ∈ reached.1.2.published ↔
      ((owner, number), true) ∈ ambient.1.2.published := by
  induction traced with
  | here => rfl
  | later query next before ambient step rest current reached actual tail ih =>
      have kept := PqxdhLaterChallengePaths.reaches_kept postImpl owner number bit
        (next step.1.1) rest step.1.2 current step.2 reached tail
      refine (ih unused clear).trans ?_
      rcases query with query | ⟨left, right⟩
      · simp only [handler, StateT.run, bind_pure_comp, simulateQ_map, simulateQ_spec_query] at actual
        change step ∈ support (StateT.run _ ambient) at actual
        rw [StateT.run_map, support_map] at actual
        obtain ⟨reply, returned, rfl⟩ := actual
        simpa only [((observe_target owner number before query reply.1).mp (kept.2 clear)).2,
          false_and, or_false] using
          step_publication mark sender route decode impl query ambient reply returned (owner, number)
      · simp only [handler, StateT.run] at actual
        split at actual
        case isFalse =>
          simp only [bind_pure_comp, simulateQ_map] at actual
          change step ∈ support (StateT.run _ ambient) at actual
          rw [StateT.run_map, support_map] at actual
          obtain ⟨reply, _, rfl⟩ := actual
          have impossible := (kept.1 (by rfl)).1
          simp only [unused, reduceCtorEq] at impossible
        case isTrue =>
          simp only [simulateQ_pure] at actual
          change step ∈ support (pure ((none, before), ambient)) at actual
          simp only [mem_support_pure_iff] at actual
          exact actual ▸ Iff.rfl

set_option backward.isDefEq.respectTransparency false in
/-- The literal successful challenge send records the marker from its own pre-send frontend, for either direction. -/
theorem send_publication (owner : RawCtxProtocolReveals.Owner S B) (plaintext : Pqxdh.Bytes)
    (before after : Full) (record : RawCtxSourceSend.Encrypted)
    (supported : (some record, after) ∈ support ((simulateQ postImpl (send owner plaintext)).run before)) :
    ((owner, record.sequence), true) ∈ after.1.2.published ↔
      ((owner, record.sequence), true) ∈ before.1.2.published ∨ before.1.2.installed owner = some true := by
  cases owner with
  | server index peer =>
      simpa only [publications, sendRequest, RawCtxPublishedRecords.record, List.mem_singleton, true_and] using
        step_publication mark sender route decode impl (sendRequest (extra := extra) (.server index peer) plaintext)
          before (some record, after) (by simpa only [send, simulateQ_spec_query] using supported)
          (.server index peer, record.sequence)
  | beacon index =>
      simpa only [publications, sendRequest, RawCtxPublishedRecords.record, List.mem_singleton, true_and] using
        step_publication mark sender route decode impl (sendRequest (extra := extra) (.beacon index) plaintext)
          before (some record, after) (by simpa only [send, simulateQ_spec_query] using supported)
          (.beacon index, record.sequence)

/-- A marked target retained at the actual cut identifies the marker at the earlier successful challenge, using both pieces of that same original prefix. -/
theorem marked_prefix (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (client rest : OracleComp (AdvSpec extra S B) Result)
    (left right : Pqxdh.Bytes)
    (next : Option RawCtxSourceSend.Encrypted → OracleComp (AdvSpec extra S B) Result)
    (before prior current : State) (ambient requestState sentAfter reached : Full)
    (record : RawCtxSourceSend.Encrypted)
    (first : Reaches postImpl owner number bit client before ambient
      ((AdvSpec extra S B).query (.inr (left, right)) >>= next) prior requestState)
    (unused : prior.pair = none) (clean : prior.otherTarget = false)
    (sent : (some record, sentAfter) ∈ support
      ((simulateQ postImpl (send owner (if bit then right else left))).run requestState))
    (remaining : Reaches postImpl owner number bit (next (some record))
      { prior with pair := some (left, right), reply := some (some record) } sentAfter rest current reached)
    (sequence : record.sequence = number) (clear : current.otherTarget = false)
    (absent : ((owner, number), true) ∉ ambient.1.2.published)
    (published : ((owner, number), true) ∈ reached.1.2.published) :
    requestState.1.2.installed owner = some true := by
  have atSend := (used_prefix mark sender route decode impl owner number bit (next (some record)) rest
    _ current sentAfter reached remaining (by rfl) clear).mp published
  have atRequest := send_publication mark sender route decode impl owner (if bit then right else left)
    requestState sentAfter record sent
  rw [sequence] at atRequest
  exact (atRequest.mp atSend).resolve_left (fun old => absent
    ((unused_prefix mark sender route decode impl owner number bit client _ before prior ambient requestState
      first unused clean).mp old))

end BeaconcryptCore.Computational.PqxdhLaterChallengeCapturePublication

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapturePublication.step_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapturePublication.step_publication
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapturePublication.used_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapturePublication.used_prefix
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapturePublication.unused_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapturePublication.unused_prefix
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapturePublication.send_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapturePublication.send_publication
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapturePublication.marked_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapturePublication.marked_prefix
