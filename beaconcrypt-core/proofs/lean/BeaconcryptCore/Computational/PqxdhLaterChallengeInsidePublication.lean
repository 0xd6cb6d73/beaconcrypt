import BeaconcryptCore.Computational.PqxdhLaterChallengeRemainderPublication
import BeaconcryptCore.Computational.PqxdhLaterChallengeInsideFirst

/-! Origin and stored-reply bookkeeping of the same inside callback and complete original outside wrapper, retaining the literal source schedule. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeInsidePublication
open PqxdhInitialPostContext PqxdhRecordConfidentialityChallenge PqxdhFirstRecordConfidentiality
variable {ι M P I D K X Response Shared : Type} {extra : OracleSpec ι} {S B : Nat}
variable (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
local notation "Snapshot" => NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Bool S B
local notation "sourceImpl" => PqxdhInitialOriginPost.compiler (extra := extra) (X := X) (Response := Response) mark sender route decode

private theorem used_target (before after : State) (kept : Kept before after)
    (used : before.pair.isSome) (number : U64) (target : Target number after) : Target number before := by
  exact ⟨used, (kept.1 used).2 ▸ target.2.1, kept.2 target.2.2⟩

/-- The complete accepted outside wrapper retains the inside callback's target reply and exactly its marked target-publication membership. -/
theorem outside_target (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (client : OracleComp (AdvSpec extra S B) Bool) (before : State) (ambient : Snapshot)
    (result : Bool × Snapshot)
    (supported : result ∈ support ((simulateQ sourceImpl
      (PqxdhLaterChallengeCapture.wrapped owner number bit client before)).run ambient))
    (used : before.pair.isSome) (accepted : result.1 = true) :
    Target number before ∧
      (((owner, number), true) ∈ result.2.2.published ↔ ((owner, number), true) ∈ ambient.2.published) := by
  have publication := PqxdhLaterChallengeRemainderPublication.wrapped_publication
    mark sender route decode owner number bit client before ambient result supported used accepted
  simp only [PqxdhLaterChallengeCapture.wrapped, simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨final, actual, rfl⟩ := supported
  have kept : Kept before final.1.2 := by
    apply run_kept owner number bit client before final.1
    apply support_simulateQ_run'_subset sourceImpl _ ambient
    simpa only [StateT.run'_eq, support_map, Set.mem_image] using
      (show ∃ value ∈ support ((simulateQ sourceImpl
        ((simulateQ (handler owner number bit) client).run before)).run ambient),
          value.1 = final.1 from ⟨final, actual, rfl⟩)
  have target : Target number final.1.2 := by
    classical
    exact (show final.1.1 = true ∧ Target number final.1.2 from
      by simpa only [output, Bool.and_eq_true, decide_eq_true_eq] using accepted).2
  exact ⟨used_target before final.1.2 kept used number target, publication⟩

private theorem send_origin (owner : RawCtxProtocolReveals.Owner S B) (plaintext : Pqxdh.Bytes)
    (before : Snapshot) (result : Option RawCtxSourceSend.Encrypted × Snapshot)
    (supported : result ∈ support ((simulateQ sourceImpl (send (extra := extra) owner plaintext)).run before))
    (number : U64) (absent : ((owner, number), true) ∉ before.2.published)
    (published : ((owner, number), true) ∈ result.2.2.published) :
    before.2.installed owner = some true := by
  cases owner with
  | server index peer =>
      exact ((PqxdhLaterChallengeRemainderPublication.step_publication (X := X) (Response := Response) mark sender route decode
        (sendRequest (extra := extra) (.server index peer) plaintext) before result
        (by simpa only [send, sendRequest, simulateQ_spec_query] using supported)
        (.server index peer, number)).mp published |>.resolve_left absent).2
  | beacon index =>
      exact ((PqxdhLaterChallengeRemainderPublication.step_publication (X := X) (Response := Response) mark sender route decode
        (sendRequest (extra := extra) (.beacon index) plaintext) before result
        (by simpa only [send, sendRequest, simulateQ_spec_query] using supported)
        (.beacon index, number)).mp published |>.resolve_left absent).2

private theorem challenge_facts (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (left right : Pqxdh.Bytes) (equal : left.length = right.length) (current : State) (unused : current.pair = none)
    (before : Snapshot) (result : (Option RawCtxSourceSend.Encrypted × State) × Snapshot)
    (supported : result ∈ support ((simulateQ sourceImpl
      ((handler (extra := extra) owner number bit (.inr (left, right))).run current)).run before))
    (absent : ((owner, number), true) ∉ before.2.published) :
    result.1.2.pair.isSome ∧
      (((owner, number), true) ∈ result.2.2.published → before.2.installed owner = some true) := by
  rw [challenge_step owner number bit left right equal current unused,
    simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨actual, reached, rfl⟩ := supported
  exact ⟨rfl, fun published => send_origin mark sender route decode owner (if bit then right else left)
    before actual reached number absent published⟩

/-- An actual admitted inside callback chooses its wrapper pair, and any newly marked target publication reads the marker installed at that same pre-request frontend. -/
theorem inside_facts (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Bool S B)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .inside)
    (before : Snapshot)
    (result : ((AdvSpec extra S B).Range details.request.query × State) × Snapshot)
    (supported : result ∈ support ((simulateQ sourceImpl
      ((handler owner number bit details.request.query).run details.request.before)).run before))
    (absent : ((owner, number), true) ∉ before.2.published) :
    result.1.2.pair.isSome ∧
      (((owner, number), true) ∈ result.2.2.published → before.2.installed owner = some true) := by
  rcases details with ⟨⟨query, current, next⟩, context⟩
  cases used : current.pair with
  | some pair => simp only [PqxdhLaterChallengeSavedClassification.phase, used, reduceCtorEq] at classified
  | none =>
      rcases query with request | ⟨left, right⟩
      · simp only [PqxdhLaterChallengeSavedClassification.phase, used, reduceCtorEq] at classified
      · by_cases equal : left.length = right.length
        · exact challenge_facts mark sender route decode owner number bit left right equal current used
            before result supported absent
        · simp only [PqxdhLaterChallengeSavedClassification.phase, used, equal, ite_false, reduceCtorEq] at classified

/-- A complete accepted original inside remainder identifies the same actual callback result, its target reply and its pre-send marked installation. Only the earlier-publication absence remains a source-cache premise. -/
theorem inside_finish {Local Other : Type}
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Bool S B)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .inside)
    (selected : (Base extra RatchetChain I D K X Response Shared S B).Domain → Local → Bool)
    (selection : ∀ query state, selected query state = true → PqxdhInitialOriginForwardPost.selected query = true)
    (impl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT Local ProbComp))
    (ambient : Snapshot) (state reached : Local)
    (cut : RawCtxForwardScan.Cut.pending details.callback reached ∈ support
      (RawCtxForwardScan.scan PqxdhInitialOriginForwardPost.selected selected selection impl
        (PqxdhInitialOriginForwardPost.program mark sender route decode
          ((handler owner number bit details.request.query).run details.request.before) ambient.1 ambient.2)
        (PqxdhInitialOriginForwardPost.program_covered mark sender route decode
          ((handler owner number bit details.request.query).run details.request.before) ambient.1 ambient.2) state))
    (afterImpl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT Other ProbComp))
    (before : Other)
    (reply : (Base extra RatchetChain I D K X Response Shared S B).Range
      (PqxdhInitialOriginContext.frame mark sender route decode details.callback).1)
    (result : (Bool × Snapshot) × Other)
    (completed : result ∈ support ((simulateQ afterImpl
      ((PqxdhInitialOriginContext.frame mark sender route decode details.callback).2 reply >>=
        PqxdhLaterChallengeCapture.resumeOutside mark sender route decode
          (fun reply => PqxdhLaterChallengeCapture.wrapped owner number bit (details.request.next reply.1) reply.2))).run before))
    (absent : ((owner, number), true) ∉ ambient.2.published)
    (accepted : result.1.1 = true) (published : ((owner, number), true) ∈ result.1.2.2.published) :
    ∃ middle : (((AdvSpec extra S B).Range details.request.query × State) × Snapshot) × Other,
      middle ∈ support ((simulateQ afterImpl
        ((PqxdhInitialOriginContext.frame mark sender route decode details.callback).2 reply)).run before) ∧
      Target number middle.1.1.2 ∧ ambient.2.installed owner = some true := by
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at completed
  obtain ⟨middle, callback, outside⟩ := completed
  have source := PqxdhLaterChallengeRemainderSupport.source_support mark sender route decode selected selection impl
    ((handler owner number bit details.request.query).run details.request.before) ambient.1 ambient.2
    state reached details.callback cut afterImpl before reply middle callback
  have facts := inside_facts mark sender route decode owner number bit details classified ambient middle.1 source absent
  have later : result.1 ∈ support ((simulateQ sourceImpl
      (PqxdhLaterChallengeCapture.wrapped owner number bit (details.request.next middle.1.1.1) middle.1.1.2)).run middle.1.2) := by
    apply support_simulateQ_run'_subset afterImpl _ middle.2
    simpa only [PqxdhLaterChallengeCapture.resumeOutside, StateT.run'_eq, support_map, Set.mem_image] using
      (show ∃ value ∈ support ((simulateQ afterImpl
        (PqxdhLaterChallengeCapture.resumeOutside mark sender route decode
          (fun reply => PqxdhLaterChallengeCapture.wrapped owner number bit (details.request.next reply.1) reply.2)
          middle.1)).run middle.2), value.1 = result.1 from ⟨result, outside, rfl⟩)
  have event := outside_target mark sender route decode owner number bit (details.request.next middle.1.1.1)
    middle.1.1.2 middle.1.2 result.1 later facts.1 accepted
  exact ⟨middle, callback, event.1, facts.2 (event.2.mp published)⟩

end BeaconcryptCore.Computational.PqxdhLaterChallengeInsidePublication

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInsidePublication.outside_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInsidePublication.outside_target

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInsidePublication.inside_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInsidePublication.inside_facts

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInsidePublication.inside_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInsidePublication.inside_finish
