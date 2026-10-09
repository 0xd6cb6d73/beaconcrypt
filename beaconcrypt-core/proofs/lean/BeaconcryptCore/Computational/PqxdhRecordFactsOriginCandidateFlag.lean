-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawGuess
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPreserve
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive

/-! Every selected muted replay flag is covered by an actual raw candidate in the complete adaptive trace. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateFlag
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftProtocol (Private Service ServiceSpec)
open PqxdhRecordFactsOriginMuteServices (IsTargetSealing interpreter)
open PqxdhRecordFactsOriginMuteAdaptive (marked)
open PqxdhRecordFactsOriginCandidateTrace (traced)
open PqxdhRecordFactsOriginRawGuess (serviceCandidate)
variable {n : Nat} {X : Type}

/-- The complete actual muted continuation preserves the invariant that a raised flag has an original raw-input candidate in its retained list. -/
theorem flag_in_trace (target : Label n) (modes : Label n → KeyMode)
    (read : RawCtxReceive.FrameDecoder) (crypto : Pqxdh.Crypto)
    (base : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (work : OracleComp (ServiceSpec n) X) (noSeal : work.IsQueryBoundP (IsTargetSealing target) 0)
    (state : CtxPrivate n) (past : List CtxDigest) (flag : Bool) (digest : CtxDigest)
    (fixed : ∀ entry ∈ (state.keys target).1.successfulSeals, entry.record.commit = digest)
    (initial : flag = true → digest ∈ past)
    (result : (X × List CtxDigest) × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ
      (marked target (RawCtxUniversalDecoder.decoder read)
        (interpreter target modes (RawCtxUniversalDecoder.decoder read) crypto base writer replace))
      (traced (serviceCandidate read) work past)).run (state, flag))) :
    result.2.2 = true → digest ∈ result.1.2 := by
  induction work using OracleComp.inductionOn generalizing state past flag with
  | pure value =>
      simp only [PqxdhRecordFactsOriginCandidateTrace.traced_pure, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at supported
      exact supported ▸ initial
  | query_bind query next ih =>
      simp only [isQueryBoundP_query_bind_iff, Nat.lt_irrefl, or_false, Nat.zero_sub, ite_self] at noSeal
      simp only [PqxdhRecordFactsOriginCandidateTrace.traced_query_bind, simulateQ_bind,
        simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨inner, reached, finished⟩ := supported
      simp only [marked, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at reached
      obtain ⟨step, stepSupported, rfl⟩ := reached
      have retained := PqxdhRecordFactsOriginOrdinalPreserve.muted_service target modes
        (RawCtxUniversalDecoder.decoder read) crypto base writer replace query noSeal.1 state step stepSupported
      apply ih step.1 (noSeal.2 step.1) step.2 _ _ (retained ▸ fixed) ?_ finished
      simp only [Bool.or_eq_true, List.mem_append]
      rintro (old | hit)
      · exact Or.inl (initial old)
      · simp only [PqxdhRecordFactsOriginRawGuess.service_bad_guess target read query state digest fixed hit,
          Option.toList_some, List.mem_singleton, or_true]

/-- Starting without prior candidates or a raised flag, every final selected replay flag is covered by the actual adaptive raw-input trace. -/
theorem initialized_flag (target : Label n) (modes : Label n → KeyMode)
    (read : RawCtxReceive.FrameDecoder) (crypto : Pqxdh.Crypto)
    (base : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (work : OracleComp (ServiceSpec n) X) (noSeal : work.IsQueryBoundP (IsTargetSealing target) 0)
    (state : CtxPrivate n) (digest : CtxDigest)
    (fixed : ∀ entry ∈ (state.keys target).1.successfulSeals, entry.record.commit = digest)
    (result : (X × List CtxDigest) × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ
      (marked target (RawCtxUniversalDecoder.decoder read)
        (interpreter target modes (RawCtxUniversalDecoder.decoder read) crypto base writer replace))
      (traced (serviceCandidate read) work [])).run (state, false))) :
    result.2.2 = true → digest ∈ result.1.2 :=
  flag_in_trace target modes read crypto base writer replace work noSeal state [] false digest
    fixed (fun contradiction => (Bool.false_ne_true contradiction).elim) result supported

/-- Every final selected replay flag is covered by one of the explicitly counted raw-request indices, using only commitments extracted from original inputs. -/
theorem flag_finite (target : Label n) (modes : Label n → KeyMode)
    (read : RawCtxReceive.FrameDecoder) (crypto : Pqxdh.Crypto)
    (base : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (work : OracleComp (ServiceSpec n) X) (noSeal : work.IsQueryBoundP (IsTargetSealing target) 0)
    (cap : Nat) (rawBound : work.IsQueryBoundP
      (fun query => PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query = 1) cap)
    (state : CtxPrivate n) (digest : CtxDigest)
    (fixed : ∀ entry ∈ (state.keys target).1.successfulSeals, entry.record.commit = digest)
    (result : (X × List CtxDigest) × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ
      (marked target (RawCtxUniversalDecoder.decoder read)
        (interpreter target modes (RawCtxUniversalDecoder.decoder read) crypto base writer replace))
      (traced (serviceCandidate read) work [])).run (state, false)))
    (bad : result.2.2 = true) :
    ∃ index : Fin cap, PqxdhRecordFactsOriginCandidateTrace.guess cap index result.1 = some digest := by
  apply PqxdhRecordFactsOriginCandidateTrace.source_guess_complete (serviceCandidate read)
    (fun query => PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query = 1)
    (PqxdhRecordFactsOriginRawGuess.service_candidate_counted read) work cap rawBound result.1
  · exact PqxdhRecordLiftFlat.support_run_fst _ _ _ result supported
  · exact initialized_flag target modes read crypto base writer replace work noSeal state digest fixed result supported bad

/-- Removing only the candidate list and Boolean marker recovers the entire original source result and private poststate, with no restriction on the source continuation. -/
theorem erase_instrumentation (target : Label n) (read : RawCtxReceive.FrameDecoder)
    (impl : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n)
    (past : List CtxDigest) (flag : Bool) :
    (fun result => (result.1.1, result.2.1)) <$>
      (simulateQ (marked target (RawCtxUniversalDecoder.decoder read) impl)
        (traced (serviceCandidate read) work past)).run (state, flag) =
      (simulateQ impl work).run state := by
  have erased := congrArg (fun program => Prod.map id Prod.fst <$> program)
    (PqxdhRecordFactsOriginCandidateTrace.interpreted_erase (serviceCandidate read)
      (marked target (RawCtxUniversalDecoder.decoder read) impl) work past (state, flag))
  simpa only [Functor.map_map, PqxdhRecordFactsOriginMuteAdaptive.complete_erase,
    Function.comp_def, Prod.map, id_eq] using erased

local instance {Y : Type} : MeasurableSpace (Y × CtxPrivate n × Bool) := ⊤
local instance {Y : Type} : DiscreteMeasurableSpace (Y × CtxPrivate n × Bool) := ⟨fun _ => trivial⟩
local instance {Y : Type} : MeasurableSpace (Y × CtxPrivate n) := ⊤
local instance {Y : Type} : DiscreteMeasurableSpace (Y × CtxPrivate n) := ⟨fun _ => trivial⟩

/-- The actual marked-muted bad probability is at most the unmarked continuation's public candidate membership probability, with coefficient one. -/
theorem flag_probability (target : Label n) (modes : Label n → KeyMode)
    (read : RawCtxReceive.FrameDecoder) (crypto : Pqxdh.Crypto)
    (base : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (work : OracleComp (ServiceSpec n) X) (noSeal : work.IsQueryBoundP (IsTargetSealing target) 0)
    (state : CtxPrivate n) (digest : CtxDigest)
    (fixed : ∀ entry ∈ (state.keys target).1.successfulSeals, entry.record.commit = digest) :
    𝒟[(simulateQ (marked target (RawCtxUniversalDecoder.decoder read)
      (interpreter target modes (RawCtxUniversalDecoder.decoder read) crypto base writer replace))
      work).run (state, false)] {result | result.2.2 = true} ≤
    𝒟[(simulateQ (interpreter target modes (RawCtxUniversalDecoder.decoder read) crypto base writer replace)
      (traced (serviceCandidate read) work [])).run state] {result | digest ∈ result.1.2} := by
  simp only [evalDist_apply_setOf]
  conv_lhs => rw [← PqxdhRecordFactsOriginCandidateTrace.interpreted_erase (serviceCandidate read)
    (marked target (RawCtxUniversalDecoder.decoder read)
      (interpreter target modes (RawCtxUniversalDecoder.decoder read) crypto base writer replace)) work [] (state, false)]
  conv_rhs => rw [← PqxdhRecordFactsOriginMuteAdaptive.complete_erase target (RawCtxUniversalDecoder.decoder read)
    (interpreter target modes (RawCtxUniversalDecoder.decoder read) crypto base writer replace)
    (traced (serviceCandidate read) work []) (state, false)]
  simp only [probEvent_map]
  exact probEvent_mono (fun result supported hit =>
    initialized_flag target modes read crypto base writer replace work noSeal state digest fixed result supported hit)

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateFlag

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateFlag.flag_in_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateFlag.flag_in_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateFlag.initialized_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateFlag.initialized_flag

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateFlag.flag_finite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateFlag.flag_finite

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateFlag.erase_instrumentation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateFlag.erase_instrumentation

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateFlag.flag_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateFlag.flag_probability
