-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateFlag

/-! No selected replay flag can arise before a selected dictionary entry exists. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginEmpty
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftProtocol (Service ServiceSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordFactsOriginMuteAdaptive (marked)
open PqxdhRecordFactsOriginMuteServices (IsTargetSealing)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}
local instance : MeasurableSpace (X × CtxPrivate n × Bool) := ⊤
local instance : DiscreteMeasurableSpace (X × CtxPrivate n × Bool) := ⟨fun _ => trivial⟩

/-- An empty selected dictionary makes every actual service's selected replay-match test false. -/
theorem service_false (target : Label n) (read : RawCtxReceive.FrameDecoder)
    (query : Service n) (state : CtxPrivate n) (empty : (state.keys target).1.successfulSeals = []) :
    PqxdhRecordFactsOriginMuteUntilBad.serviceBad target (RawCtxUniversalDecoder.decoder read) query state = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hit
  obtain ⟨entry, member, _⟩ := PqxdhRecordFactsOriginRawGuess.service_bad target read query state hit
  simp only [empty, List.not_mem_nil] at member


/-- The actual marked erased source retains a false selected flag through every supported continuation with no selected seal. -/
theorem erased_flag (target : Label n) (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (client : OracleComp (ServiceSpec n) X) (noSeal : client.IsQueryBoundP (IsTargetSealing target) 0)
    (state : CtxPrivate n) (empty : (state.keys target).1.successfulSeals = [])
    (result : X × CtxPrivate n × Bool)
    (supported : result ∈ support ((simulateQ (marked target (RawCtxUniversalDecoder.decoder codec.frameRead)
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)) client).run (state, false))) :
    result.2.2 = false := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      exact supported ▸ rfl
  | query_bind query next ih =>
      simp only [isQueryBoundP_query_bind_iff, Nat.lt_irrefl, or_false, Nat.zero_sub, ite_self] at noSeal
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, answered, continued⟩ := supported
      simp only [marked, StateT.run, service_false target codec.frameRead query state empty, Bool.false_or,
        mem_support_bind_iff, mem_support_pure_iff] at answered
      obtain ⟨actual, stepped, rfl⟩ := answered
      have retained := PqxdhRecordFactsOriginOrdinalPreserve.erased_service target modes
        (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace query noSeal.1 state actual stepped
      exact ih actual.1 (noSeal.2 actual.1) actual.2 (retained.trans empty) result continued


/-- A rejected selected seal that inserts no entry leaves zero probability of any later selected replay match. -/
theorem erased_probability (target : Label n) (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (client : OracleComp (ServiceSpec n) X) (noSeal : client.IsQueryBoundP (IsTargetSealing target) 0)
    (state : CtxPrivate n) (empty : (state.keys target).1.successfulSeals = []) :
    𝒟[(simulateQ (marked target (RawCtxUniversalDecoder.decoder codec.frameRead)
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)) client).run (state, false)]
      {result | result.2.2 = true} = 0 := by
  rw [evalDist_apply_setOf, probEvent_eq_zero_iff]
  intro result supported hit
  have absent := erased_flag target modes setup codec replace client noSeal state empty result supported
  exact Bool.false_ne_true (absent.symm.trans hit)

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginEmpty

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginEmpty.service_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginEmpty.service_false
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginEmpty.erased_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginEmpty.erased_flag
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginEmpty.erased_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginEmpty.erased_probability
