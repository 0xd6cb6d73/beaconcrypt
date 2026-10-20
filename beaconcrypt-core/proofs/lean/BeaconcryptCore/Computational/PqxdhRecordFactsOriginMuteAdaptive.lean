-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteUntilBad
import BeaconcryptCore.Computational.StatefulGoodEvent

/-! Adaptive source comparison with an analysis-only selected replay flag. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftProtocol (Private Service ServiceSpec)
open PqxdhRecordFactsOriginMuteUntilBad (serviceBad)
variable {n : Nat}

local instance {X : Type} : MeasurableSpace (X × CtxPrivate n × Bool) := ⊤
local instance {X : Type} : DiscreteMeasurableSpace (X × CtxPrivate n × Bool) := ⟨fun _ => trivial⟩

/-- Execute the literal service and record whether the exact pre-step selected replay flag has ever been raised. -/
noncomputable def marked (target : Label n) (decode : RawDecoder)
    (impl : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp)) :
    QueryImpl (ServiceSpec n) (StateT (CtxPrivate n × Bool) ProbComp) := fun query state => do
  let result ← (impl query).run state.1
  pure (result.1, (result.2, state.2 || serviceBad target decode query state.1))

/-- Erasing the ghost flag returns the same reply and complete source state after one step. -/
theorem marked_erase (target : Label n) (decode : RawDecoder)
    (impl : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (query : Service n) (state : CtxPrivate n × Bool) :
    Prod.map id Prod.fst <$> (marked target decode impl query).run state = (impl query).run state.1 := by
  simp [marked, StateT.run]

/-- Every supported step sets exactly the sticky flag determined before that step; the actual source reply is retained. -/
theorem marked_flag (target : Label n) (decode : RawDecoder)
    (impl : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (query : Service n) (state : CtxPrivate n × Bool)
    (result : (ServiceSpec n).Range query × (CtxPrivate n × Bool))
    (supported : result ∈ support ((marked target decode impl query).run state)) :
    result.2.2 = (state.2 || serviceBad target decode query state.1) := by
  simp only [marked, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
  rcases supported with ⟨reply, _, rfl⟩
  rfl

/-- Once raised, the analysis flag stays raised through every source reply. -/
theorem marked_sticky (target : Label n) (decode : RawDecoder)
    (impl : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (query : Service n) (state : CtxPrivate n × Bool) (bad : state.2 = true)
    (result : (ServiceSpec n).Range query × (CtxPrivate n × Bool))
    (supported : result ∈ support ((marked target decode impl query).run state)) :
    result.2.2 = true := by
  simpa only [bad, Bool.true_or] using marked_flag target decode impl query state result supported

/-- A selected replay match marks every output of that step, before any subsequent adaptive decision. -/
theorem hit_marked (target : Label n) (decode : RawDecoder)
    (impl : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (query : Service n) (state : CtxPrivate n × Bool)
    (hit : serviceBad target decode query state.1 = true)
    (result : (ServiceSpec n).Range query × (CtxPrivate n × Bool))
    (supported : result ∈ support ((marked target decode impl query).run state)) :
    result.2.2 = true := by
  simpa only [hit, Bool.or_true] using marked_flag target decode impl query state result supported

/-- Complete good-output transition probabilities agree whenever the underlying source steps agree before a match. -/
theorem agree_good (target : Label n) (decode : RawDecoder)
    (left right : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (agree : ∀ query state, serviceBad target decode query state = false →
      (left query).run state = (right query).run state)
    (query : Service n) (state : CtxPrivate n) (reply : (ServiceSpec n).Range query) (next : CtxPrivate n) :
    𝒟[(marked target decode left query).run (state, false)] {(reply, (next, false))} =
      𝒟[(marked target decode right query).run (state, false)] {(reply, (next, false))} := by
  by_cases hit : serviceBad target decode query state = true
  · have zero (impl : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp)) :
        𝒟[(marked target decode impl query).run (state, false)] {(reply, (next, false))} = 0 := by
      rw [evalDist_apply_singleton]
      exact probOutput_eq_zero_of_not_mem_support (fun supported =>
        Bool.false_ne_true (hit_marked target decode impl query (state, false) hit (reply, (next, false)) supported))
    rw [zero, zero]
  · have same : left query state = right query state := agree query state (Bool.eq_false_of_not_eq_true hit)
    simp only [marked, StateT.run, same]

/-- Removing only the flag from an arbitrary adaptive run returns its actual original result and complete private state. -/
theorem complete_erase {X : Type} (target : Label n) (decode : RawDecoder)
    (impl : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n × Bool) :
    Prod.map id Prod.fst <$> (simulateQ (marked target decode impl) work).run state =
      (simulateQ impl work).run state.1 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst (marked_erase target decode impl) work state

/-- The ghost flag adds no underlying finite query; each all-reply source cap is retained. -/
theorem marked_queries (target : Label n) (decode : RawDecoder)
    (impl : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (query : Service n) (state : CtxPrivate n × Bool)
    (selected : unifSpec.Domain → Prop) [DecidablePred selected] (cap : Nat)
    (bound : ((impl query).run state.1).IsQueryBoundP selected cap) :
    ((marked target decode impl query).run state).IsQueryBoundP selected cap := by
  simpa only [marked, StateT.run, bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using bound

/-- Both adaptive experiments raise the same flag with exactly the same probability, without conditioning on any reply. -/
theorem bad_probability {X : Type} (target : Label n) (decode : RawDecoder)
    (left right : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (agree : ∀ query state, serviceBad target decode query state = false →
      (left query).run state = (right query).run state)
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) :
    𝒟[(simulateQ (marked target decode left) work).run (state, false)] {result | result.2.2 = true} =
      𝒟[(simulateQ (marked target decode right) work).run (state, false)] {result | result.2.2 = true} := by
  simpa only [evalDist_apply_setOf] using
    OracleComp.ProgramLogic.Relational.probEvent_output_bad_eq'
      (marked target decode left) (marked target decode right)
      (fun query current reply next => by
        simpa only [evalDist_apply_singleton] using (agree_good target decode left right agree query current reply next))
      (marked_sticky target decode left) (marked_sticky target decode right) work state

/-- Every event on the complete result and state agrees jointly with the unraised flag; this is unconditioned event equality. -/
theorem event_good {X : Type} (target : Label n) (decode : RawDecoder)
    (left right : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (agree : ∀ query state, serviceBad target decode query state = false →
      (left query).run state = (right query).run state)
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n × Bool)
    (event : X × CtxPrivate n × Bool → Prop) :
    𝒟[(simulateQ (marked target decode left) work).run state] {result | event result ∧ result.2.2 = false} =
      𝒟[(simulateQ (marked target decode right) work).run state] {result | event result ∧ result.2.2 = false} := by
  simpa only [evalDist_apply_setOf] using
    StatefulGoodEvent.event_good_vcvioLegacy (marked target decode left) (marked target decode right)
      (fun query current reply next => by
        simpa only [evalDist_apply_singleton] using (agree_good target decode left right agree query current reply next))
      (marked_sticky target decode left) (marked_sticky target decode right) work state event

/-- Full adaptive joint output-state distance costs only one copy of the exact selected-match probability. -/
theorem marked_distance {X : Type} (target : Label n) (decode : RawDecoder)
    (left right : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (agree : ∀ query state, serviceBad target decode query state = false →
      (left query).run state = (right query).run state)
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) :
    tvDist ((simulateQ (marked target decode left) work).run (state, false))
      ((simulateQ (marked target decode right) work).run (state, false)) ≤
      (𝒟[(simulateQ (marked target decode left) work).run (state, false)] {result | result.2.2 = true}).toReal := by
  simpa only [evalDist_apply_setOf] using
    OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad
      (marked target decode left) (marked target decode right) work state
      (fun query current reply next => by
        simpa only [evalDist_apply_singleton] using (agree_good target decode left right agree query current reply next))
      (marked_sticky target decode left) (marked_sticky target decode right)

/-- Erasing the ghost flag retains the same bound on complete unmodified adaptive source executions. -/
theorem complete_distance {X : Type} (target : Label n) (decode : RawDecoder)
    (left right : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (agree : ∀ query state, serviceBad target decode query state = false →
      (left query).run state = (right query).run state)
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) :
    tvDist ((simulateQ left work).run state) ((simulateQ right work).run state) ≤
      (𝒟[(simulateQ (marked target decode left) work).run (state, false)] {result | result.2.2 = true}).toReal := by
  simpa only [complete_erase] using
    (tvDist_map_le (Prod.map id Prod.fst)
      ((simulateQ (marked target decode left) work).run (state, false))
      ((simulateQ (marked target decode right) work).run (state, false))).trans
        (marked_distance target decode left right agree work state)

open PqxdhServerAuthExperiment (Setup Codec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The existing selected muted handler instantiated with the same actual source decoder, crypto, base interpreter and writer. -/
noncomputable abbrev muted (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :=
  PqxdhRecordFactsOriginMuteServices.interpreter target modes
    (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
    (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace

/-- The actual erased and muted source executions have the same selected-match probability for every adaptive service client. -/
theorem source_bad_probability {X : Type} (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) :
    𝒟[(simulateQ (marked target (RawCtxUniversalDecoder.decoder codec.frameRead)
      (muted target modes replace setup codec)) work).run (state, false)] {result | result.2.2 = true} =
    𝒟[(simulateQ (marked target (RawCtxUniversalDecoder.decoder codec.frameRead)
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)) work).run (state, false)]
      {result | result.2.2 = true} :=
  bad_probability target (RawCtxUniversalDecoder.decoder codec.frameRead)
    (muted target modes replace setup codec) (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
    (PqxdhRecordFactsOriginMuteUntilBad.erased_agrees target modes replace setup codec) work state

/-- Exact good-event equality for the actual source handlers, with no assumed protocol step agreement. -/
theorem source_event_good {X : Type} (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n × Bool)
    (event : X × CtxPrivate n × Bool → Prop) :
    𝒟[(simulateQ (marked target (RawCtxUniversalDecoder.decoder codec.frameRead)
      (muted target modes replace setup codec)) work).run state] {result | event result ∧ result.2.2 = false} =
    𝒟[(simulateQ (marked target (RawCtxUniversalDecoder.decoder codec.frameRead)
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)) work).run state]
      {result | event result ∧ result.2.2 = false} :=
  event_good target (RawCtxUniversalDecoder.decoder codec.frameRead)
    (muted target modes replace setup codec) (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
    (PqxdhRecordFactsOriginMuteUntilBad.erased_agrees target modes replace setup codec) work state event

/-- The actual complete erased source and muted continuation differ by at most the selected replay-match probability in the muted run, with coefficient one. -/
theorem source_distance {X : Type} (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) :
    tvDist ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) work).run state)
      ((simulateQ (muted target modes replace setup codec) work).run state) ≤
    (𝒟[(simulateQ (marked target (RawCtxUniversalDecoder.decoder codec.frameRead)
      (muted target modes replace setup codec)) work).run (state, false)] {result | result.2.2 = true}).toReal := by
  rw [tvDist_comm]
  exact complete_distance target (RawCtxUniversalDecoder.decoder codec.frameRead)
    (muted target modes replace setup codec) (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
    (PqxdhRecordFactsOriginMuteUntilBad.erased_agrees target modes replace setup codec) work state

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.marked_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.marked_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.marked_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.marked_flag
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.marked_sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.marked_sticky
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.hit_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.hit_marked
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.agree_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.agree_good
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.complete_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.complete_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.marked_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.marked_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.bad_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.bad_probability
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.event_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.event_good
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.marked_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.marked_distance
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.complete_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.complete_distance
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.source_bad_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.source_bad_probability
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.source_event_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.source_event_good
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.source_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive.source_distance
