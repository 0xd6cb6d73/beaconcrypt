import BeaconcryptCore.Computational.PqxdhLaterChallengeScanPhase

/-! Couple the complete actual source scans through their shared pre-challenge prefix. Post-admission outcomes keep their full values and states in an explicit residual branch. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeScanCoupling
open PqxdhRecordConfidentialityChallenge PqxdhFirstRecordConfidentiality
open PqxdhInitialPostContext PqxdhInitialOriginForwardPost RawCtxForwardScan
open PqxdhLaterChallengeCapture PqxdhLaterChallengeScanPhase
variable {ι M P I D K X Response Shared Origin Local : Type} {extra : OracleSpec ι} {S B : Nat}

abbrev Outcome := Cut (Capture extra M P I D K Origin S B)
  (Bool × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) Local

/-- Restore each world's exact outside wrapper around the one shared callback; every other carried field is literal. -/
noncomputable def tagged (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (details : Details extra M P I D K Origin S B) : Capture extra M P I D K Origin S B :=
  (append (fun reply => wrapped owner number bit (details.request.next reply.1) reply.2) details.callback, details)

/-- Either both scans retain the same pre-admission callback and complete native state, or both retain a completed or post-admission outcome. No outcome is removed or renormalized. -/
noncomputable def Related (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (first second : Bool)
    (left right : Outcome (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (Origin := Origin) (Local := Local) (S := S) (B := B)) : Prop :=
  (∃ details state, PqxdhLaterChallengeSavedClassification.phase (some details) = .before ∧
    left = .pending (tagged owner number first details) state ∧
    right = .pending (tagged owner number second details) state) ∨ (Late left ∧ Late right)

variable (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (impl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT Local ProbComp))
    (chosen : (Base extra RatchetChain I D K X Response Shared S B).Domain → Local → Bool)
    (selection : ∀ query state, chosen query state = true → PqxdhInitialForwardPost.selected query = true)

/-- The existing captured scan, including its complete native result or concrete saved callback. -/
noncomputable def run (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (work : OracleComp (AdvSpec extra S B) Bool) (current : State)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) (state : Local) :
    ProbComp (Outcome (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (Origin := Origin) (Local := Local) (S := S) (B := B)) :=
  scan PqxdhInitialForwardPost.selected chosen selection impl
    (captured mark sender route read owner number bit work current before trace)
    (captured_covered mark sender route read owner number bit work current before trace) state

/-- Split only at the actual complete callback boundary. A cut retains that callback and appends its own world's original outside continuation. -/
theorem run_query (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (query : (AdvSpec extra S B).Domain)
    (next : (AdvSpec extra S B).Range query → OracleComp (AdvSpec extra S B) Bool) (current : State)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) (state : Local) :
    run mark sender route read impl chosen selection owner number bit (((AdvSpec extra S B).query query : OracleComp (AdvSpec extra S B) _) >>= next) current before trace state =
      (scan PqxdhInitialForwardPost.selected chosen selection impl
        (program mark sender route read ((handler owner number bit query).run current) before trace)
        (program_covered mark sender route read ((handler owner number bit query).run current) before trace) state >>= fun cut =>
          match cut with
          | .complete reply ambient => run mark sender route read impl chosen selection owner number bit (next reply.1.1) reply.1.2 reply.2.1 reply.2.2 ambient
          | .pending callback ambient => pure (.pending (tagged owner number bit ⟨⟨query, current, next⟩, callback⟩) ambient)) := by
  let liftTag := fun callback : PqxdhInitialOriginContext.Context extra M P I D K
      ((AdvSpec extra S B).Range query × State) Origin S B =>
    tagged owner number bit (⟨⟨query, current, next⟩, callback⟩ : Details extra M P I D K Origin S B)
  have headCovered := (covered_tags liftTag PqxdhInitialForwardPost.selected
    (program (X := X) (Response := Response) mark sender route read
      ((handler owner number bit query).run current) before trace)).mpr
    (program_covered mark sender route read ((handler owner number bit query).run current) before trace)
  unfold run
  change scan _ _ _ _ (RawCtxForwardAnnotation.mapTags liftTag
    (program mark sender route read ((handler owner number bit query).run current) before trace) >>=
    fun reply => captured mark sender route read owner number bit (next reply.1.1) reply.1.2 reply.2.1 reply.2.2) _ state = _
  rw [PqxdhLaterChallengeCutChronology.native_bind PqxdhInitialForwardPost.selected chosen selection impl _ _ headCovered
    (fun reply => captured_covered mark sender route read owner number bit (next reply.1.1) reply.1.2 reply.2.1 reply.2.2)
    (captured_covered mark sender route read owner number bit (((AdvSpec extra S B).query query : OracleComp (AdvSpec extra S B) _) >>= next) current before trace) state]
  rw [← native_scan_tags liftTag PqxdhInitialForwardPost.selected chosen selection impl _
    (program_covered mark sender route read ((handler owner number bit query).run current) before trace) state, bind_map_left]
  exact bind_congr fun cut => by cases cut <;> rfl

/-- Every full scan outcome after this admitted request is retained in the explicit completed/inside/used branch. -/
theorem admitted_late (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (left right : Pqxdh.Bytes) (equal : left.length = right.length)
    (next : Option RawCtxSourceSend.Encrypted → OracleComp (AdvSpec extra S B) Bool) (current : State)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) (state : Local)
    (unused : current.pair = none) :
    ∀ result ∈ support (run mark sender route read impl chosen selection owner number bit
      (((AdvSpec extra S B).query (.inr (left, right)) : OracleComp (AdvSpec extra S B) _) >>= next) current before trace state), Late result := by
  intro result supported
  cases result with
  | complete value ambient => trivial
  | pending tag ambient =>
      exact admitted_pending mark sender route read impl chosen selection owner number bit
        left right equal next current before trace state ambient tag.1 tag.2 supported unused

/-- The two complete evaluated captured scans share each pre-admission callback and its full native state. Once admission occurs, both complete actual outcomes remain in the explicit residual branch; no equality of individual post-admission values or states is asserted. -/
theorem coupled (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (first second : Bool)
    (work : OracleComp (AdvSpec extra S B) Bool) (current : State)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) (state : Local)
    (unused : current.pair = none) :
    RelTriple (run mark sender route read impl chosen selection owner number first work current before trace state)
      (run mark sender route read impl chosen selection owner number second work current before trace state)
      (Related owner number first second) := by
  induction work using OracleComp.inductionOn generalizing current before trace state with
  | pure value => exact relTriple_pure_pure (Or.inr ⟨trivial, trivial⟩)
  | query_bind query next ih =>
      by_cases beforeQuery : Before query
      · rw [run_query, run_query]
        simp only [← before_handler owner number first second query beforeQuery current]
        let common := scan PqxdhInitialForwardPost.selected chosen selection impl
          (program mark sender route read ((handler owner number first query).run current) before trace)
          (program_covered mark sender route read ((handler owner number first query).run current) before trace) state
        refine relTriple_bind (relTriple_refl_of_mem_support common
          (R := fun left right => left = right ∧ left ∈ support common) (fun _ supported => ⟨rfl, supported⟩)) ?_
        rintro cut _ ⟨rfl, actual⟩
        cases cut with
        | complete reply ambient =>
            have whole := PqxdhLaterChallengeCutChronology.native_complete PqxdhInitialForwardPost.selected chosen selection impl
              (program mark sender route read ((handler owner number first query).run current) before trace)
              (program_covered mark sender route read ((handler owner number first query).run current) before trace) state ambient reply actual
            rw [program_erase] at whole
            have logical := PqxdhFirstRecordStopTagged.support_state_simulation _ _ _ reply
              (PqxdhFirstRecordStopTagged.support_state_simulation impl _ state (reply, ambient) whole)
            exact ih reply.1.1 reply.1.2 reply.2.1 reply.2.2 ambient
              (before_unused owner number first query beforeQuery current unused reply.1 logical)
        | pending callback ambient =>
            exact relTriple_pure_pure (Or.inl ⟨_, ambient, before_phase query beforeQuery current unused next callback, rfl, rfl⟩)
      · rcases query with request | ⟨left, right⟩
        · exact False.elim (beforeQuery trivial)
        · have equal : left.length = right.length := Classical.byContradiction beforeQuery
          exact relTriple_post_mono (PqxdhFirstRecordStopTagged.product_coupling
            (admitted_late mark sender route read impl chosen selection owner number first left right equal next current before trace state unused)
            (admitted_late mark sender route read impl chosen selection owner number second left right equal next current before trace state unused))
            (fun _ _ late => Or.inr late)

end BeaconcryptCore.Computational.PqxdhLaterChallengeScanCoupling

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeScanCoupling.run_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeScanCoupling.run_query

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeScanCoupling.admitted_late' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeScanCoupling.admitted_late

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeScanCoupling.coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeScanCoupling.coupled
