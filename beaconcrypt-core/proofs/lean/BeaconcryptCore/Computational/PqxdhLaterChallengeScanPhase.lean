import BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged
import BeaconcryptCore.Computational.PqxdhLaterChallengeCutChronology
import BeaconcryptCore.Computational.PqxdhLaterChallengeSavedClassification

/-! Classify complete actual scan outcomes after the challenge is selected, retaining both returned states for the later full-pair prefix coupling. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeScanPhase
open PqxdhRecordConfidentialityChallenge PqxdhFirstRecordConfidentiality
variable {ι M P I D K X Response Shared Origin Local Result : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Every actual adaptive source prefix retains an already selected challenge pair and reply, with its full original source state left in the reachability statement. -/
theorem reaches_kept
    (impl : QueryImpl (ConfPostSpec extra S B) (StateT Local ProbComp))
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (work rest : OracleComp (AdvSpec extra S B) Result) (before current : State) (ambient reached : Local)
    (actual : PqxdhRecordConfidentialityTrace.Reaches impl owner number bit work before ambient rest current reached) :
    Kept before current := by
  induction actual with
  | here => exact ⟨fun _ => ⟨rfl, rfl⟩, id⟩
  | later query next before ambient step rest current reached supported tail ih =>
      exact (PqxdhRecordConfidentialityTrace.interpreted_kept impl owner number bit query before ambient step supported).trans ih

open PqxdhInitialPostContext PqxdhInitialOriginForwardPost RawCtxForwardScan
variable (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (impl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT Local ProbComp))

/-- A pending cut after an already selected challenge retains that used phase. The actual frontend, origin trace, private state and callback all come from this same scan. -/
theorem used_pending
    (chosen : (Base extra RatchetChain I D K X Response Shared S B).Domain → Local → Bool)
    (selection : ∀ query state, chosen query state = true → PqxdhInitialForwardPost.selected query = true)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (work : OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool)
    (current : PqxdhRecordConfidentialityChallenge.State)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (state reached : Local)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Bool Origin S B)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Origin S B)
    (supported : Cut.pending (context, details) reached ∈ support
      (scan PqxdhInitialForwardPost.selected chosen selection impl
        (PqxdhLaterChallengeCapture.captured mark sender route read owner number bit work current before trace)
        (PqxdhLaterChallengeCapture.captured_covered mark sender route read owner number bit work current before trace) state))
    (used : current.pair.isSome) :
    PqxdhLaterChallengeSavedClassification.phase (some details) = .used := by
  obtain ⟨front, history, ambient, reachedRequest, cut⟩ :=
    PqxdhLaterChallengeCutChronology.captured_reaches mark sender route read impl chosen selection owner number bit work
      current before trace state reached context details supported
  have kept := reaches_kept _ owner number bit _ _ current details.request.before _ _ reachedRequest
  exact (PqxdhLaterChallengeSavedClassification.phase_used details).mpr (by simpa only [(kept.1 used).1] using used)

/-- Every original source reply to the admitted challenge selects its pair, even when the send itself returns no record. -/
theorem admitted_used (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (left right : Pqxdh.Bytes) (equal : left.length = right.length) (current : State) (unused : current.pair = none)
    (result : Option RawCtxSourceSend.Encrypted × State)
    (supported : result ∈ support ((handler (extra := extra) owner number bit (.inr (left, right))).run current)) :
    result.2.pair.isSome := by
  rw [challenge_step owner number bit left right equal current unused, support_map] at supported
  obtain ⟨reply, _, rfl⟩ := supported
  rfl

/-- The admitted challenge's actual captured scan can only cut inside that callback or after its pair has been selected. Every complete native state remains in the original supported result. -/
theorem admitted_pending
    (chosen : (Base extra RatchetChain I D K X Response Shared S B).Domain → Local → Bool)
    (selection : ∀ query state, chosen query state = true → PqxdhInitialForwardPost.selected query = true)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (left right : Pqxdh.Bytes) (equal : left.length = right.length)
    (next : Option RawCtxSourceSend.Encrypted → OracleComp (AdvSpec extra S B) Bool)
    (current : PqxdhRecordConfidentialityChallenge.State)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (state reached : Local)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Bool Origin S B)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Origin S B)
    (supported : Cut.pending (context, details) reached ∈ support
      (scan PqxdhInitialForwardPost.selected chosen selection impl
        (PqxdhLaterChallengeCapture.captured mark sender route read owner number bit (((AdvSpec extra S B).query (.inr (left, right)) : OracleComp (AdvSpec extra S B) _) >>= next) current before trace)
        (PqxdhLaterChallengeCapture.captured_covered mark sender route read owner number bit (((AdvSpec extra S B).query (.inr (left, right)) : OracleComp (AdvSpec extra S B) _) >>= next) current before trace) state))
    (unused : current.pair = none) :
    PqxdhLaterChallengeSavedClassification.phase (some details) = .inside ∨
      PqxdhLaterChallengeSavedClassification.phase (some details) = .used := by
  let query : (AdvSpec extra S B).Domain := .inr (left, right)
  let liftTag := fun callback : PqxdhInitialOriginContext.Context extra M P I D K
      ((AdvSpec extra S B).Range query × State) Origin S B =>
    (PqxdhLaterChallengeCapture.append
      (fun reply => PqxdhLaterChallengeCapture.wrapped owner number bit (next reply.1) reply.2) callback,
      (⟨⟨query, current, next⟩, callback⟩ : PqxdhLaterChallengeCapture.Details extra M P I D K Origin S B))
  have headCovered := (PqxdhLaterChallengeCapture.covered_tags liftTag PqxdhInitialForwardPost.selected
    (program (X := X) (Response := Response) mark sender route read
      ((handler owner number bit query).run current) before trace)).mpr
    (program_covered mark sender route read ((handler owner number bit query).run current) before trace)
  rcases PqxdhLaterChallengeCutChronology.native_pending_cases PqxdhInitialForwardPost.selected chosen selection impl _ _ headCovered
    (fun value => PqxdhLaterChallengeCapture.captured_covered mark sender route read owner number bit
      (next value.1.1) value.1.2 value.2.1 value.2.2)
    (PqxdhLaterChallengeCapture.captured_covered mark sender route read owner number bit
      (((AdvSpec extra S B).query query : OracleComp (AdvSpec extra S B) _) >>= next) current before trace)
    state reached (context, details) supported with inside | later
  case inr =>
    obtain ⟨value, backend, actual, remaining⟩ := later
    rw [RawCtxForwardAnnotation.erase_mapTags, program_erase] at actual
    have logical := PqxdhFirstRecordStopTagged.support_state_simulation _ _ _ value
      (PqxdhFirstRecordStopTagged.support_state_simulation impl _ state (value, backend) actual)
    exact Or.inr (used_pending mark sender route read impl chosen selection owner number bit (next value.1.1)
      value.1.2 value.2.1 value.2.2 backend reached context details remaining
      (admitted_used owner number bit left right equal current unused value.1 logical))
  case inl =>
    obtain ⟨callback, same, pending⟩ := PqxdhLaterChallengeCutChronology.native_pending_map liftTag PqxdhInitialForwardPost.selected chosen selection impl
      (program mark sender route read ((handler owner number bit query).run current) before trace)
      (program_covered mark sender route read ((handler owner number bit query).run current) before trace)
      state reached (context, details) inside
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact Or.inl (by simp only [PqxdhLaterChallengeSavedClassification.phase, unused, query, equal, ite_true])

/-- A scan that has already reached the admitted challenge may finish or retain an inside/used cut. This predicate keeps the original complete result and native state as arguments. -/
def Late : Cut (PqxdhLaterChallengeCapture.Capture extra M P I D K Origin S B) Result Local → Prop
  | .complete _ _ => True
  | .pending (_, details) _ =>
      PqxdhLaterChallengeSavedClassification.phase (some details) = .inside ∨
        PqxdhLaterChallengeSavedClassification.phase (some details) = .used

/-- Ordinary requests and unequal-length challenge requests precede admission when the pair is still unused. -/
def Before : (AdvSpec extra S B).Domain → Prop
  | .inl _ => True
  | .inr (left, right) => left.length ≠ right.length

/-- Every pre-admission handler is literally independent of the hidden bit, including its full returned wrapper state. -/
theorem before_handler (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (first second : Bool)
    (query : (AdvSpec extra S B).Domain) (before : Before query) (current : State) :
    (handler owner number first query).run current = (handler owner number second query).run current := by
  rcases query with request | ⟨left, right⟩
  · rfl
  · simp only [handler, StateT.run, ite_eq_left (Or.inr before : current.pair.isSome ∨ left.length ≠ right.length)]

/-- Every all-reply result of a pre-admission request retains the unused pair. -/
theorem before_unused (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (query : (AdvSpec extra S B).Domain) (before : Before query) (current : State) (unused : current.pair = none)
    (result : (AdvSpec extra S B).Range query × State)
    (supported : result ∈ support ((handler owner number bit query).run current)) :
    result.2.pair = none := by
  rcases query with request | ⟨left, right⟩
  · simp only [handler, StateT.run, bind_pure_comp, support_map] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    exact unused
  · simp only [handler, StateT.run, ite_eq_left (Or.inr before : current.pair.isSome ∨ left.length ≠ right.length), mem_support_pure_iff] at supported
    cases supported
    exact unused

/-- The exact shared callback metadata of a pre-admission request is in the before phase. -/
theorem before_phase (query : (AdvSpec extra S B).Domain) (before : Before query)
    (current : State) (unused : current.pair = none)
    (next : (AdvSpec extra S B).Range query → OracleComp (AdvSpec extra S B) Bool)
    (callback : PqxdhInitialOriginContext.Context extra M P I D K
      ((AdvSpec extra S B).Range query × State) Origin S B) :
    PqxdhLaterChallengeSavedClassification.phase (some ⟨⟨query, current, next⟩, callback⟩) = .before := by
  rcases query with request | ⟨left, right⟩
  · simp only [PqxdhLaterChallengeSavedClassification.phase, unused]
  · simp only [PqxdhLaterChallengeSavedClassification.phase, unused, ite_eq_right before]

end BeaconcryptCore.Computational.PqxdhLaterChallengeScanPhase

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeScanPhase.reaches_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeScanPhase.reaches_kept

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeScanPhase.used_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeScanPhase.used_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeScanPhase.admitted_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeScanPhase.admitted_used

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeScanPhase.admitted_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeScanPhase.admitted_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeScanPhase.before_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeScanPhase.before_handler

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeScanPhase.before_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeScanPhase.before_unused

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeScanPhase.before_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeScanPhase.before_phase
