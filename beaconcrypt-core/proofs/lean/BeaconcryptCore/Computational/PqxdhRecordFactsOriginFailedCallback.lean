-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedResume
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginEmpty

/-! Complete actual selected callback probability, including body/tag generation and rejection. -/
open OracleComp OracleSpec ENNReal MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedCallback
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordFactsOriginOrdinalCut (Cut resume)
open PqxdhRecordFactsOriginMuteAdaptive (marked)
open PqxdhRecordFactsOriginSelectedGuess (Counted)
open PqxdhRecordFactsOriginFailedResume (resumeMarked)
local instance (α : Type) : MeasurableSpace α := ⊤
local instance (α : Type) : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}
local instance : MeasurableSpace (X × CtxPrivate n) := ⊤
local instance : DiscreteMeasurableSpace (X × CtxPrivate n) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace ((X × CtxPrivate n) × Bool) := ⊤
local instance : DiscreteMeasurableSpace ((X × CtxPrivate n) × Bool) := ⟨fun _ => trivial⟩

/-- A probability-only selected-target experiment: the literal source seal executes, failure follows its actual marked continuation, success returns false. -/
noncomputable def callback (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (state : CtxPrivate n)
    (client : OracleComp (ServiceSpec n) X) : ProbComp Bool := do
  let reply ← (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.sealing pending)).run state
  if reply.1.isNone then
    let result ← (simulateQ (marked pending.material (RawCtxUniversalDecoder.decoder codec.frameRead)
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)) client).run (reply.2, false)
    pure result.2.2
  else pure false

/-- The complete original marked resumption and the stopped selected-target experiment have the same flag probability; no source program or query-cost equality is asserted. -/
theorem resume_probability (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (cut : Cut n X) :
    𝒟[resumeMarked modes setup codec replace cut] {result | result.2 = true} =
      𝒟[callback modes setup codec replace cut.pending cut.state (cut.next none)] {flag | flag = true} := by
  simp only [resumeMarked, callback]
  rw [← prEvent_eq_evalDist_of_discrete, ← prEvent_eq_evalDist_of_discrete, OracleComp.prEvent_bind_eq_tsum,
    OracleComp.prEvent_bind_eq_tsum]
  refine tsum_congr fun reply => congrArg _ ?_
  rcases reply with ⟨_ | encrypted, state⟩
  · simp only [Option.isNone_none, Bool.true_and, ↓reduceIte, bind_assoc, pure_bind]
  · simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    rw [prEvent_pure]
    simp only [bind_assoc, pure_bind, Bool.false_and, Bool.false_eq_true]
    rw [prEvent_false]
    simp

/-- The literal fresh hidden callback, including the source-ordered random body and tag draws and all rejection branches, has the same two-guess bound. -/
theorem callback_bound (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (state : CtxPrivate n)
    (ideal : modes pending.material ≠ .real)
    (fresh : PqxdhRecordFactsPrivateCacheSource.FreshPoint state (.sealing pending))
    (empty : (state.keys pending.material).1.successfulSeals = [])
    (client : OracleComp (ServiceSpec n) X)
    (noSeal : client.IsQueryBoundP (PqxdhRecordFactsOriginMuteServices.IsTargetSealing pending.material) 0)
    (cap : Nat) (bound : client.IsQueryBoundP Counted cap) :
    𝒟[callback modes setup codec replace pending state client] {flag | flag = true} ≤
      2 * cap * ((2 ^ 512 : Nat) : ℝ≥0∞)⁻¹ := by
  simp only [callback, PqxdhRecordFactsOriginSelectedSeal.source_sampler modes replace setup codec pending state ideal fresh,
    PqxdhRecordFactsOriginSelectedSeal.hiddenSampler]
  split
  · split
    · simp only [bind_assoc, pure_bind]
      rw [← prEvent_eq_evalDist_of_discrete]
      refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun body _ =>
        prEvent_bind_le_of_forall_le_of_support _ _ _ fun tag _ => ?_
      rw [prEvent_eq_evalDist_of_discrete]
      simpa only [PqxdhRecordFactsOriginFailedFlag.sampledErased] using
        PqxdhRecordFactsOriginFailedFlag.sampled_erased_bound modes setup codec replace pending _
          body.toList tag.toList tag.toList_length state empty client noSeal cap bound
    · simpa only [PqxdhRecordFactsOriginFailedFlag.sampledErased, bind_assoc, pure_bind] using
        PqxdhRecordFactsOriginFailedFlag.sampled_erased_bound modes setup codec replace pending _
          _ _ (setup.source.crypto.aeadSeal_tag_length _ _ _ _) state empty client noSeal cap bound
  · simp only [pure_bind, Option.isNone_none, ↓reduceIte, bind_pure_comp]
    rw [← prEvent_eq_evalDist_of_discrete, prEvent_map]
    have zero := PqxdhRecordFactsOriginEmpty.erased_probability pending.material modes setup codec replace client noSeal
      state empty
    rw [← @prEvent_eq_evalDist_of_discrete _ _ _ _ _ _
      PqxdhRecordFactsOriginEmpty.instMeasurableSpaceProdCtxPrivateBool
      PqxdhRecordFactsOriginEmpty.instDiscreteMeasurableSpaceProdCtxPrivateBool] at zero
    exact (le_of_eq zero).trans zero_le

/-- The complete original selected resumption satisfies the bound; the successful-publication continuation is still executed in this statement. -/
theorem marked_bound (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (cut : Cut n X) (ideal : modes cut.pending.material ≠ .real)
    (fresh : PqxdhRecordFactsPrivateCacheSource.FreshPoint cut.state (.sealing cut.pending))
    (empty : (cut.state.keys cut.pending.material).1.successfulSeals = [])
    (noSeal : (cut.next none).IsQueryBoundP (PqxdhRecordFactsOriginMuteServices.IsTargetSealing cut.pending.material) 0)
    (cap : Nat) (bound : (cut.next none).IsQueryBoundP Counted cap) :
    𝒟[resumeMarked modes setup codec replace cut] {result | result.2 = true} ≤
      2 * cap * ((2 ^ 512 : Nat) : ℝ≥0∞)⁻¹ := by
  exact (le_of_eq (resume_probability modes setup codec replace cut)).trans
    (callback_bound modes setup codec replace cut.pending cut.state ideal fresh empty (cut.next none) noSeal cap bound)

/-- A concrete event on the literal full source resumption inherits the bound from its same-execution failed-writer marker implication. -/
theorem event_bound (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (cut : Cut n X) (ideal : modes cut.pending.material ≠ .real)
    (fresh : PqxdhRecordFactsPrivateCacheSource.FreshPoint cut.state (.sealing cut.pending))
    (empty : (cut.state.keys cut.pending.material).1.successfulSeals = [])
    (noSeal : (cut.next none).IsQueryBoundP (PqxdhRecordFactsOriginMuteServices.IsTargetSealing cut.pending.material) 0)
    (cap : Nat) (bound : (cut.next none).IsQueryBoundP Counted cap)
    (event : X × CtxPrivate n → Prop)
    (covered : ∀ result ∈ support (resumeMarked modes setup codec replace cut), event result.1 → result.2 = true) :
    𝒟[resume (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) (.inr cut)] {result | event result} ≤
      2 * cap * ((2 ^ 512 : Nat) : ℝ≥0∞)⁻¹ := by
  exact (PqxdhRecordFactsOriginFailedResume.event_le_flag modes setup codec replace cut event covered).trans
    (marked_bound modes setup codec replace cut ideal fresh empty noSeal cap bound)

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedCallback

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedCallback.resume_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedCallback.resume_probability

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedCallback.callback_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedCallback.callback_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedCallback.marked_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedCallback.marked_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedCallback.event_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedCallback.event_bound
