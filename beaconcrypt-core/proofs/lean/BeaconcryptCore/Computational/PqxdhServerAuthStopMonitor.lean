import BeaconcryptCore.Computational.PqxdhServerAuthStopSource

section MonitorSection

open OracleComp OracleSpec ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxStop
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor

/-- Post-accept control uses only the actual allocated index and returned marks. Its None is an outer stop, distinct from the native reply's own optional failure. -/
def checkpoint (query : ServerAuthSpec.Domain) (index : Nat) (marks : Marks)
    (first : Option Nat) (reply : ServerAuthSpec.Range query) : Option (ServerAuthSpec.Range query) × Option Nat :=
  match query with
  | .inr (.accept _) =>
      if marks index then
        match first with
        | none => (some reply, some index)
        | some previous => (none, some previous)
      else (some reply, first)
  | _ => (some reply, first)

/-- An existing component refusal propagates unchanged. Otherwise the checkpoint observes the exact completed source transition. -/
def observe {State : Type} (counter : State → Nat) (marks : State → Marks)
    (query : ServerAuthSpec.Domain) (before : State × Option Nat)
    (result : Option (ServerAuthSpec.Range query) × State) :
    Option (ServerAuthSpec.Range query) × (State × Option Nat) :=
  match result.1 with
  | none => (none, result.2, before.2)
  | some reply =>
      let after := checkpoint query (counter before.1) (marks result.2) before.2 reply
      (after.1, result.2, after.2)

/-- Generic executable wrapper for the same complete optional handler. All prefix and derive effects occur before a newly detected second-session stop; the exact poststate is retained on every stop. -/
def stopped {State : Type} {m : Type → Type} [Monad m]
    (counter : State → Nat) (marks : State → Marks)
    (handler : QueryImpl ServerAuthSpec (OptionT (StateT State m))) :
    QueryImpl ServerAuthSpec (OptionT (StateT (State × Option Nat) m)) :=
  fun query => OptionT.mk fun before => do
    let result ← (handler query).run before.1
    pure (observe counter marks query before result)

/-- The stopped interface preserves the entire original poststate, including the work that caused refusal. -/
theorem observe_state {State : Type} (counter : State → Nat) (marks : State → Marks)
    (query : ServerAuthSpec.Domain) (before : State × Option Nat)
    (result : Option (ServerAuthSpec.Range query) × State) :
    (observe counter marks query before result).2.1 = result.2 := by
  cases reply : result.1 <;> simp only [observe, reply]

/-- A component refusal is not interpreted as a normal optional source reply. -/
theorem observe_refused {State : Type} (counter : State → Nat) (marks : State → Marks)
    (query : ServerAuthSpec.Domain) (before : State × Option Nat) (after : State) :
    observe counter marks query before (none, after) = (none, after, before.2) := rfl

/-- The recorded index is exactly the set of marked attempts before refusal. -/
structure Tracked (marks : Marks) (first : Option Nat) : Prop where
  unique : ∀ index, marks index = true → first = some index
  present : ∀ index, first = some index → marks index = true

/-- Two different actual Server attempts have been marked; the complete continuing source retains this evidence. -/
def DoubleMarked (marks : Marks) : Prop :=
  ∃ first second, first ≠ second ∧ marks first = true ∧ marks second = true

/-- The post-accept checkpoint either retains an exact single-index monitor or witnesses two distinct actual source marks. -/
theorem checkpoint_control {KemSK τ : Type} (query : ServerAuthSpec.Domain)
    (before after : FlatState KemSK τ) (first : Option Nat)
    (tracked : Tracked before.2.1 first) (fresh : before.2.1 before.1.sessions = false)
    (step : MarkStep query before after) (reply : ServerAuthSpec.Range query) :
    match (checkpoint query before.1.sessions after.2.1 first reply).1 with
    | none => DoubleMarked after.2.1
    | some _ => Tracked after.2.1 (checkpoint query before.1.sessions after.2.1 first reply).2 := by
  have unchanged (same : after.2.1 = before.2.1) : Tracked after.2.1 first := same ▸ tracked
  cases query with
  | inl coin => exact unchanged step
  | inr query =>
      cases query with
      | accept raw =>
          simp only [checkpoint]
          split_ifs with marked
          · cases recorded : first with
            | none =>
                have updated : after.2.1 = Function.update before.2.1 before.1.sessions true := by
                  rcases step with same | changed
                  · have impossible := same ▸ marked
                    rw [fresh] at impossible
                    cases impossible
                  · exact changed
                refine ⟨?_, ?_⟩
                · intro index selected
                  by_cases same : index = before.1.sessions
                  · exact congrArg some same.symm
                  · have old : before.2.1 index = true := by simpa only [updated, Function.update_of_ne same] using selected
                    have impossible := tracked.unique index old
                    rw [recorded] at impossible
                    cases impossible
                · intro index same
                  have equal := Option.some.inj same
                  exact equal ▸ marked
            | some previous =>
                have old := tracked.present previous recorded
                have different : previous ≠ before.1.sessions := by
                  intro same
                  rw [same, fresh] at old
                  cases old
                exact ⟨previous, before.1.sessions, different, MarkStep.monotone _ before after step previous old, marked⟩
          · have same : after.2.1 = before.2.1 := by
              rcases step with same | changed
              · exact same
              · have impossible : after.2.1 before.1.sessions = true := by simp [changed]
                exact (marked impossible).elim
            exact unchanged same
      | build _ _ | finish _ | hmac _ _ | hash _ | reveal _ => exact unchanged step

/-- A continuing checkpoint returns exactly the original reply, including native optional failure. -/
theorem checkpoint_reply (query : ServerAuthSpec.Domain) (index : Nat) (marks : Marks)
    (first : Option Nat) (reply answer : ServerAuthSpec.Range query)
    (continues : (checkpoint query index marks first reply).1 = some answer) : answer = reply := by
  cases query with
  | inl coin => exact Option.some.inj continues.symm
  | inr query =>
      cases query with
      | accept raw =>
          simp only [checkpoint] at continues
          split_ifs at continues
          · cases first <;> simp_all
          · exact Option.some.inj continues.symm
      | build _ _ | finish _ | hmac _ _ | hash _ | reveal _ => exact Option.some.inj continues.symm

/-- The generic monitor is a pure image of the full underlying optional transition, so it adds no query and retains work already performed before refusal. -/
theorem stopped_step {State : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (counter : State → Nat) (marks : State → Marks)
    (handler : QueryImpl ServerAuthSpec (OptionT (StateT State m)))
    (query : ServerAuthSpec.Domain) (before : State × Option Nat) :
    (stopped counter marks handler query).run before =
      observe counter marks query before <$> (handler query).run before.1 := by
  simp only [stopped, OptionT.run_mk, map_eq_bind_pure_comp, Function.comp_def]

end BeaconcryptCore.Computational.PqxdhServerAuthCtxStop

end MonitorSection

section SourceSection

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxStop
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Embed normal source replies under a separate outer refusal layer. Native optional failures remain ordinary replies. -/
def optionalSource {State : Type} {m : Type → Type} [Monad m]
    (handler : QueryImpl ServerAuthSpec (StateT State m)) :
    QueryImpl ServerAuthSpec (OptionT (StateT State m)) :=
  fun query => OptionT.mk fun state => do
    let result ← handler query state
    pure (some result.1, result.2)

/-- The concrete source observer runs the complete existing handler before examining actual allocation and mark fields. -/
noncomputable def sourceStopped (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1))
    (tails : Services Response HiddenTable) :
    QueryImpl ServerAuthSpec (OptionT (StateT (HiddenState KemSK × Option Nat) ProbComp)) :=
  stopped (fun state => state.1.1.sessions) (fun state => state.1.2.1)
    (optionalSource (hiddenHandler setup codec checks context Q j (tableServices setup context tails)))

/-- Actual source chronology makes the next allocation coordinate unmarked, without an adversary freshness premise. -/
theorem TraceInvariant.fresh (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (state : HiddenState KemSK)
    (invariant : TraceInvariant setup context Q j state) : state.1.2.1 state.1.1.sessions = false := by
  apply Bool.eq_false_of_not_eq_true
  intro marked
  exact Nat.lt_irrefl _ (invariant.below setup context Q j state _ marked)

/-- One complete source transition either supplies a normal tracked reply or actual distinct source marks. Every source effect is retained before the checkpoint. -/
theorem source_checkpoint (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1))
    (tails : Services Response HiddenTable) (query : ServerAuthSpec.Domain)
    (state : HiddenState KemSK) (first : Option Nat)
    (invariant : TraceInvariant setup context Q j state) (tracked : Tracked state.1.2.1 first)
    (result : ServerAuthSpec.Range query × HiddenState KemSK)
    (supported : result ∈ support ((hiddenHandler setup codec checks context Q j
      (tableServices setup context tails) query).run state)) :
    TraceInvariant setup context Q j result.2 ∧
      match (checkpoint query state.1.1.sessions result.2.1.2.1 first result.1).1 with
      | none => DoubleMarked result.2.1.2.1
      | some _ => Tracked result.2.1.2.1 (checkpoint query state.1.1.sessions result.2.1.2.1 first result.1).2 := by
  exact ⟨hidden_trace setup codec checks context Q j tails query state invariant result supported,
    checkpoint_control query state.1 result.2.1 first tracked
      (invariant.fresh setup context Q j state)
      (hidden_marks setup codec checks context Q j (tableServices setup context tails) query state result supported) result.1⟩

/-- The source wrapper is exactly a deterministic checkpoint after the original complete transition. -/
theorem sourceStopped_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1))
    (tails : Services Response HiddenTable) (query : ServerAuthSpec.Domain)
    (state : HiddenState KemSK) (first : Option Nat) :
    (sourceStopped setup codec checks context Q j tails query).run (state, first) =
      (fun result =>
        let answer := checkpoint query state.1.1.sessions result.2.1.2.1 first result.1
        (answer.1, result.2, answer.2)) <$>
      ((hiddenHandler setup codec checks context Q j (tableServices setup context tails) query).run state) := by
  simp only [sourceStopped, stopped, optionalSource, OptionT.run_mk, StateT.run, bind_assoc,
    pure_bind, observe, map_eq_bind_pure_comp, Function.comp_def]

end BeaconcryptCore.Computational.PqxdhServerAuthCtxStop

end SourceSection

section CouplingSection

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxStop
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Final coupling keeps exact full source replies/state while continuing, and actual two-mark evidence in the original source on refusal. -/
def SourceRelation (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) {Result : Type}
    (left : Result × HiddenState KemSK)
    (right : Option Result × (HiddenState KemSK × Option Nat)) : Prop :=
  TraceInvariant setup context Q j left.2 ∧
    ((right.1 = some left.1 ∧ right.2.1 = left.2 ∧ Tracked left.2.1.2.1 right.2.2) ∨
      (right.1 = none ∧ DoubleMarked left.2.1.2.1))

/-- The unchanged complete adaptive source and its optional stopped interpreter couple through every original reply-dependent continuation. -/
theorem source_client_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1))
    (tails : Services Response HiddenTable) {Result : Type} (client : OracleComp ServerAuthSpec Result)
    (state : HiddenState KemSK) (first : Option Nat)
    (invariant : TraceInvariant setup context Q j state) (tracked : Tracked state.1.2.1 first) :
    RelTriple
      ((simulateQ (hiddenHandler setup codec checks context Q j (tableServices setup context tails)) client).run state)
      (((simulateQ (sourceStopped setup codec checks context Q j tails) client).run).run (state, first))
      (SourceRelation setup context Q j) := by
  induction client using OracleComp.inductionOn generalizing state first with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, OptionT.run_pure]
      exact relTriple_pure_pure ⟨invariant, Or.inl ⟨rfl, rfl, tracked⟩⟩
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, OptionT.run_bind, Option.elimM]
      simp only [StateT.run]
      rw [sourceStopped_step]
      simp only [bind_map_left]
      refine relTriple_bind (R := fun a b => a = b ∧ a ∈ support
        ((hiddenHandler setup codec checks context Q j (tableServices setup context tails) query).run state))
        (relTriple_refl_of_mem_support _ fun value member => ⟨rfl, member⟩) ?_
      rintro step other ⟨rfl, supported⟩
      have control := source_checkpoint setup codec checks context Q j tails query state first invariant tracked step supported
      cases response : (checkpoint query state.1.1.sessions step.2.1.2.1 first step.1).1 with
      | none =>
          simp only [response] at control
          refine relTriple_post_mono (relTriple_support _ _
            (fun result => TraceInvariant setup context Q j result.2 ∧ DoubleMarked result.2.1.2.1)
            (fun result => result.1 = none) ?_ ?_) ?_
          · intro final finalSupported
            refine ⟨client_trace setup codec checks context Q j tails (next step.1) step.2 control.1 final finalSupported, ?_⟩
            obtain ⟨one, two, different, markedOne, markedTwo⟩ := control.2
            exact ⟨one, two, different,
              client_marks setup codec checks context Q j (tableServices setup context tails) (next step.1) step.2 one markedOne final finalSupported,
              client_marks setup codec checks context Q j (tableServices setup context tails) (next step.1) step.2 two markedTwo final finalSupported⟩
          · intro final finalSupported
            change final ∈ support (pure (none, step.2, (checkpoint query state.1.1.sessions step.2.1.2.1 first step.1).2)) at finalSupported
            simp only [support_pure, Set.mem_singleton_iff] at finalSupported
            subst finalSupported
            rfl
          · intro left right post
            exact ⟨post.1.1, Or.inr ⟨post.2, post.1.2⟩⟩
      | some answer =>
          have same := checkpoint_reply query state.1.1.sessions step.2.1.2.1 first step.1 answer response
          subst answer
          simp only [response] at control
          exact ih step.1 step.2 _ control.1 control.2

end BeaconcryptCore.Computational.PqxdhServerAuthCtxStop

end CouplingSection

section EventSection

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxStop
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Actual source provenance makes every two-mark state lose the unchanged original per-entry decision. -/
theorem TraceInvariant.double_reject (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (state : HiddenState KemSK)
    (invariant : TraceInvariant setup context Q j state) (doubled : DoubleMarked state.1.2.1) :
    hiddenDecision setup context Q j state = false := by
  apply Bool.eq_false_of_not_eq_true
  intro winning
  simp only [hiddenDecision, decide_eq_true_eq] at winning
  obtain ⟨first, second, different, one, two⟩ := doubled
  exact different (marked_unique setup context Q j state invariant.shape.once invariant.selected invariant.marked winning.2 first second one two)

/-- The original event is observed only after a normal client return. An outer component or monitor refusal is not interpreted as a native response. -/
noncomputable def stoppedDecision (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) {Result : Type}
    (result : Option Result × (HiddenState KemSK × Option Nat)) : Bool :=
  match result.1 with
  | none => false
  | some _ => hiddenDecision setup context Q j result.2.1

/-- Complete coupled outputs have exactly the same original authentication decision; the stopped case is excluded by proved source chronology and the event itself. -/
theorem SourceRelation.decision (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) {Result : Type} (left : Result × HiddenState KemSK)
    (right : Option Result × (HiddenState KemSK × Option Nat))
    (related : SourceRelation setup context Q j left right) :
    hiddenDecision setup context Q j left.2 = stoppedDecision setup context Q j right := by
  rcases related with ⟨invariant, (⟨reply, state, _⟩ | ⟨refused, doubled⟩)⟩
  · simp only [stoppedDecision, reply, state]
  · simpa only [stoppedDecision, refused] using invariant.double_reject setup context Q j left.2 doubled

/-- Stopping the actual complete adaptive source preserves its original decision distribution with zero statistical loss. -/
theorem client_event (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1))
    (tails : Services Response HiddenTable) {Result : Type} (client : OracleComp ServerAuthSpec Result)
    (state : HiddenState KemSK) (first : Option Nat)
    (invariant : TraceInvariant setup context Q j state) (tracked : Tracked state.1.2.1 first) :
    𝒟[(fun result => hiddenDecision setup context Q j result.2) <$>
      ((simulateQ (hiddenHandler setup codec checks context Q j (tableServices setup context tails)) client).run state)] =
    𝒟[stoppedDecision setup context Q j <$>
      (((simulateQ (sourceStopped setup codec checks context Q j tails) client).run).run (state, first))] := by
  apply EvalDistEq.evalDist_eq
  refine (VCVioLegacy.evalSPMF_eq_iff_evalDistEq _ _).1 ?_
  apply evalSPMF_map_eq_of_relTriple
  exact relTriple_post_mono (source_client_coupling setup codec checks context Q j tails client state first invariant tracked)
    (fun left right related => SourceRelation.decision setup context Q j left right related)

/-- The stopped entry continuation keeps the original private context and supplied joint output, with an initially empty monitor. -/
noncomputable def stoppedEntryDistinguisher (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) : ProbComp Bool :=
  stoppedDecision setup context Q j <$>
    (((simulateQ (sourceStopped setup codec checks context Q j (factorServices setup codec checks context value))
      (adversary (contextInput setup revealSeed context))).run).run
      (((contextState setup context, fun _ => false, ⟨∅, none, false⟩), false), none))

/-- Actual empty instrumentation supplies the stopped-event equality for every concrete joint output and complete adversary. -/
theorem entry_event (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) :
    𝒟[entryDistinguisher setup codec checks adversary revealSeed Q j context value] =
      𝒟[stoppedEntryDistinguisher setup codec checks adversary revealSeed Q j context value] := by
  have equality := client_event setup codec checks context Q j (factorServices setup codec checks context value)
    (adversary (contextInput setup revealSeed context)) _ none (TraceInvariant.initial setup context Q j)
    ⟨(by intro index marked; cases marked), (by intro index recorded; cases recorded)⟩
  have services : tableServices setup context (factorServices setup codec checks context value) =
      factorServices setup codec checks context value := rfl
  rw [services] at equality
  simpa only [entryDistinguisher, hiddenRun, Functor.map_map, Function.comp_def, stoppedEntryDistinguisher] using equality

/-- The actual uniform-factor game with the same original context-first sampling order and stopped continuation. -/
noncomputable def stoppedEntryGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1)) : ProbComp Bool := do
  let context ← contextSample setup codec
  let value ← $ᵗ PqxdhServerAuthKeySchedule.Output
  stoppedEntryDistinguisher setup codec checks adversary revealSeed Q j context value

/-- The complete B8b uniform entry experiment equals the stopped experiment, with no new assumption, selection factor or loss. -/
theorem uniform_entry_event (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1)) :
    𝒟[uniformEntryGame setup codec checks adversary revealSeed Q j] =
      𝒟[stoppedEntryGame setup codec checks adversary revealSeed Q j] := by
  apply EvalDistEq.evalDist_eq
  unfold uniformEntryGame stoppedEntryGame
  apply evalSPMF_bind_congr_support
  intro context _
  apply evalSPMF_bind_congr_support
  intro value _
  exact EvalDistEq.of_evalDist_eq (entry_event setup codec checks adversary revealSeed Q j context value)

end BeaconcryptCore.Computational.PqxdhServerAuthCtxStop

end EventSection

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.observe_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.observe_state
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.observe_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.observe_refused
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.checkpoint_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.checkpoint_control
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.checkpoint_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.checkpoint_reply
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.stopped_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.stopped_step
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.TraceInvariant.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.TraceInvariant.fresh
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.source_checkpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.source_checkpoint
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.sourceStopped_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.sourceStopped_step
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.source_client_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.source_client_coupling
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.TraceInvariant.double_reject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.TraceInvariant.double_reject
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.SourceRelation.decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.SourceRelation.decision
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.client_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.client_event
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.entry_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.entry_event
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.uniform_entry_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.uniform_entry_event
