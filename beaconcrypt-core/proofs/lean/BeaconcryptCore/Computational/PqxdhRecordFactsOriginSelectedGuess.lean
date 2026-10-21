-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedGuess
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawGuess
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive

/-! Actual public candidate lists after an unconditioned selected failed writer. -/
open OracleComp OracleSpec ENNReal MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedGuess
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordFactsOriginSelectedSeal (hiddenResult)
open PqxdhRecordFactsOriginRawGuess (serviceCandidate)
open PqxdhRecordFactsOriginCandidateTrace (traced)
local instance (α : Type) : MeasurableSpace α := ⊤
local instance (α : Type) : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}
local instance : MeasurableSpace (CtxDigest × Option ((X × List CtxDigest) × CtxPrivate n)) := ⊤
local instance : DiscreteMeasurableSpace (CtxDigest × Option ((X × List CtxDigest) × CtxPrivate n)) := ⟨fun _ => trivial⟩

/-- The literal selected seal installs this digest as its only dictionary commitment when the source prefix has no previous entry. -/
theorem hidden_dictionary (writer : RawCtxMixedShared.Writer)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length = 16) (digest : CtxDigest) (state : CtxPrivate n)
    (empty : (state.keys pending.material).1.successfulSeals = []) :
    ((hiddenResult writer pending input body tag width digest state).2.keys pending.material).1.successfulSeals =
      [⟨input, ⟨body, tag, width, digest⟩⟩] := by
  simp only [hiddenResult, PqxdhRecordFactsOriginSelectedSeal.keyedResult,
    PqxdhRecordFactsPrivateCacheFresh.sealResult, Function.update_self, empty]


/-- Every literal projected continuation reply is a possible reply of the unchanged source service syntax. -/
theorem continuation_support (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length = 16) (state : CtxPrivate n)
    (client : OracleComp (ServiceSpec n) X) (digest : CtxDigest) (result : X × CtxPrivate n)
    (supported : result ∈ support (PqxdhRecordFactsOriginFailedGuess.continuation
      modes setup codec replace pending input body tag width state client digest)) :
    result.1 ∈ support client := by
  simp only [PqxdhRecordFactsOriginFailedGuess.continuation, support_map] at supported
  obtain ⟨reply, reached, rfl⟩ := supported
  exact support_simulateQ_run'_subset
    (PqxdhRecordFactsOriginMuteAdaptive.muted pending.material modes replace setup codec) client
    (hiddenResult codec.frameWrite pending input body tag width digest state).2 (by
    rw [StateT.run'_eq, support_map]
    exact ⟨reply, reached, rfl⟩)


/-- Successful completion of the failed-writer branch retains a supported reply of the unchanged source syntax. -/
theorem experiment_support (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length = 16) (state : CtxPrivate n)
    (client : OracleComp (ServiceSpec n) X) (digest : CtxDigest) (result : X × CtxPrivate n)
    (supported : (digest, some result) ∈ support (PqxdhRecordFactsOriginFailedGuess.experiment
      modes setup codec replace pending input body tag width state client)) :
    result.1 ∈ support client := by
  simp only [PqxdhRecordFactsOriginFailedGuess.experiment, mem_support_bind_iff] at supported
  obtain ⟨sampled, _, branch⟩ := supported
  split at branch
  · simp only [mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at branch
    obtain ⟨reply, reached, rfl, rfl⟩ := branch
    exact continuation_support modes setup codec replace pending input body tag width state client _ _ reached
  · simp only [mem_support_pure_iff, Prod.mk.injEq, Option.some_ne_none, and_false] at branch


/-- The existing raw-service category marks each literal hidden opening, independently of all parser and optional reply results. -/
def Counted (query : PqxdhRecordLiftProtocol.Service n) : Prop :=
  PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query = 1

instance : DecidablePred (Counted (n := n)) := fun _ => inferInstanceAs (Decidable (_ = (1 : Nat)))

/-- The actual public raw candidate trace after a failed selected writer costs at most twice its original raw-query cap per uniform digest. -/
theorem failed_trace_bound (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length = 16) (state : CtxPrivate n)
    (client : OracleComp (ServiceSpec n) X)
    (noSeal : client.IsQueryBoundP (PqxdhRecordFactsOriginMuteServices.IsTargetSealing pending.material) 0)
    (cap : Nat) (bound : client.IsQueryBoundP Counted cap) :
    𝒟[PqxdhRecordFactsOriginFailedGuess.experiment modes setup codec replace pending input body tag width state
      (traced (serviceCandidate codec.frameRead) client [])]
      {result | ∃ value, result.2 = some value ∧ result.1 ∈ value.1.2} ≤
        2 * cap * ((2 ^ 512 : Nat) : ℝ≥0∞)⁻¹ := by
  refine le_trans ?_ (PqxdhRecordFactsOriginFailedGuess.failed_guesses_bound modes setup codec replace
    pending input body tag width state (traced (serviceCandidate codec.frameRead) client [])
    (PqxdhRecordFactsOriginCandidateTrace.traced_queries _ client [] _ 0 noSeal) cap
    (fun index result => PqxdhRecordFactsOriginCandidateTrace.guess cap index result.1))
  apply measure_mono_ae
  apply OracleComp.ae_evalDist_of_forall_mem_support
  rintro ⟨digest, value⟩ supported ⟨result, same, present⟩
  cases same
  exact PqxdhRecordFactsOriginCandidateTrace.source_guess_complete (serviceCandidate codec.frameRead) Counted
    (PqxdhRecordFactsOriginRawGuess.service_candidate_counted codec.frameRead) client cap bound result.1
    (experiment_support modes setup codec replace pending input body tag width state _ digest result supported) digest present

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedGuess

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedGuess.hidden_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedGuess.hidden_dictionary
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedGuess.continuation_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedGuess.continuation_support
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedGuess.experiment_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedGuess.experiment_support
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedGuess.failed_trace_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedGuess.failed_trace_bound
