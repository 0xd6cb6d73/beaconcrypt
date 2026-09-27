import BeaconcryptCore.Computational.RawCtxSelectedFamilyLiveCompiler
import VCVio.ProgramLogic.Relational.SimulateQ
import BeaconcryptCore.Computational.PqxdhSelectedStateInterpreter

/-!
The selected CTX compiler's nonce refusal is compared against the original source with an explicit analysis ledger. The executable requires no selected-key argument; arbitrary input histories and known-byte aliases remain allowed by these operational statements. The mathematical source/interpreter takes the selected key explicitly. Source projection retains the original optional outputs and all private state; nonce stopping is an event in the same adaptive run, never a freshness premise.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling

abbrev Optional {ι : Type} (spec : OracleSpec ι) : OracleSpec spec.Domain := fun query => Option (spec.Range query)

def optionalRequests {ι : Type} (spec : OracleSpec ι) : QueryImpl spec (OptionT (OracleComp (Optional spec))) :=
  fun query => OptionT.mk ((Optional spec).query query)

noncomputable def optionalClient {ι Result : Type} {spec : OracleSpec ι} (client : OracleComp spec Result) :
    OracleComp (Optional spec) (Option Result) := (simulateQ (optionalRequests spec) client).run

/-- Internal optional replies stop the translated client at the same point as the original OptionT interpreter; no stop value is disclosed to a continuing adversary. -/
theorem optional_client {ι Result σ : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]
    (handler : QueryImpl spec (OptionT (StateT σ m))) (client : OracleComp spec Result) :
    simulateQ ((fun query => (handler query).run) : QueryImpl (Optional spec) (StateT σ m)) (optionalClient client) = (simulateQ handler client).run := by
  induction client using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query continuation ih =>
    simp only [optionalClient, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
      optionalRequests, OptionT.run_mk, simulateQ_spec_query]
    congr 1
    funext reply
    cases reply with
    | none => rfl
    | some value => exact ih value

open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
open RawCtxSelectedFamilyLiveCompiler (Front)
variable {A M P I D K Result : Type} {S B : Nat}
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Full (M P I D K A : Type) (S B : Nat) := Front M P I D K S B × RawCtxSelectedReceiveCompiler.State A
abbrev SourceFull (M P I D K A : Type) (S B : Nat) := Front M P I D K S B × RawCtxSharedPrimitive.SharedState A

def project (state : Full M P I D K A S B) : SourceFull M P I D K A S B :=
  (state.1, RawCtxSelectedReceiveCompiler.project state.2)

/-- Only the analysis bookkeeping is retained when an original source step supplies the actual next state and cache. -/
def extend (before : Full M P I D K A S B) (after : SourceFull M P I D K A S B) : Full M P I D K A S B :=
  (after.1, (after.2.1, { before.2.2 with cache := after.2.2 }))

noncomputable def compiled (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) :
    QueryImpl (Optional (RawCtxProtocolReveals.SourceSpec S B)) (StateT (Full M P I D K A S B) ProbComp) :=
  fun query state => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (RawCtxSelectedReceiveCompiler.evaluated source key read
      (((RawCtxSelectedFamilyLiveCompiler.impl source writer prior parent target nonce next sender route read query).run).run state.1)).run state.2

noncomputable def original (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) :
    QueryImpl (Optional (RawCtxProtocolReveals.SourceSpec S B)) (StateT (SourceFull M P I D K A S B) ProbComp) :=
  fun query => (RawCtxSelectedMessageStopping.stopping
    (RawCtxSelectedMessageStopping.sourceRecord source writer prior parent key target nonce next sender route read) query).run

/-- This is original source instrumentation. Before a nonce refusal it uses the checked complete joint compiler transition; at a refusal it executes the original source callback and retains its actual cache. -/
noncomputable def augmented (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) :
    QueryImpl (Optional (RawCtxProtocolReveals.SourceSpec S B)) (StateT (Full M P I D K A S B) ProbComp) :=
  fun query state =>
    if RawCtxSelectedFamilyLiveCompiler.Stops prior parent target nonce next sender query state.1 state.2.2 then
      Prod.map id (extend state) <$> (original source writer prior parent key target nonce next sender route read query).run (project state)
    else (compiled source writer prior parent key target nonce next sender route read query).run state

/-- The augmented callback projects to the original full source step for every state, including the exact nonce-refusal branch. No source simulation premise remains. -/
theorem augmented_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (Optional (RawCtxProtocolReveals.SourceSpec S B)).Domain) (state : Full M P I D K A S B) :
    Prod.map id project <$> (augmented source writer prior parent key target nonce next sender route read query).run state =
      (original source writer prior parent key target nonce next sender route read query).run (project state) := by
  by_cases stopped : RawCtxSelectedFamilyLiveCompiler.Stops prior parent target nonce next sender query state.1 state.2.2
  · simp only [augmented, StateT.run, stopped, ite_true, Functor.map_map, Prod.map_def, id_eq, project, extend,
      RawCtxSelectedReceiveCompiler.project]
    exact id_map _
  · have same := RawCtxSelectedFamilyLiveCompiler.step_source source writer prior parent key target nonce next sender route read query state.1 state.2
    simp only [stopped, ite_false] at same
    simp only [augmented, StateT.run, stopped, ite_false, compiled, Functor.map_map, Prod.map_def, id_eq,
      project, original] at same ⊢
    convert same using 1
    rfl

/-- The entire arbitrary adaptive source client is preserved by the analysis ledger, including terminal optional output, private roles, retained reveal history, ambient state and the shared cache. -/
theorem augmented_client (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : Full M P I D K A S B) :
    Prod.map id project <$>
      (simulateQ (augmented source writer prior parent key target nonce next sender route read) (optionalClient client)).run state =
      ((simulateQ (RawCtxSelectedMessageStopping.stopping
        (RawCtxSelectedMessageStopping.sourceRecord source writer prior parent key target nonce next sender route read)) client).run).run (project state) := by
  have same := map_run_simulateQ_eq_of_query_map_eq
    (augmented source writer prior parent key target nonce next sender route read)
    (original source writer prior parent key target nonce next sender route read) project
    (augmented_step source writer prior parent key target nonce next sender route read) (optionalClient client) state
  unfold original at same
  rw [optional_client] at same
  exact same

/-- Before the first nonce refusal the full joint transition, including the entire selected ledger, is literally the executable compiler's interpreted transition. -/
theorem augmented_nonstop (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (Optional (RawCtxProtocolReveals.SourceSpec S B)).Domain) (state : Full M P I D K A S B)
    (clear : ¬ RawCtxSelectedFamilyLiveCompiler.Stops prior parent target nonce next sender query state.1 state.2.2) :
    (augmented source writer prior parent key target nonce next sender route read query).run state =
      (compiled source writer prior parent key target nonce next sender route read query).run state := by
  simp only [augmented, StateT.run, clear, ite_false]

/-- A sticky analysis flag records whether the exact entry-state nonce-refusal predicate has ever held. The actual callback still runs. -/
noncomputable def marked {ι σ : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT σ ProbComp)) (bad : spec.Domain → σ → Prop) :
    QueryImpl spec (StateT (σ × Bool) ProbComp) := fun query state => do
  let result ← (handler query).run state.1
  pure (result.1, (result.2, state.2 || decide (bad query state.1)))

/-- Marking changes no original result or ledger state. -/
theorem marked_step {ι σ : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT σ ProbComp)) (bad : spec.Domain → σ → Prop)
    (query : spec.Domain) (state : σ × Bool) :
    Prod.map id Prod.fst <$> (marked handler bad query).run state = (handler query).run state.1 := by
  simp [marked, StateT.run]

/-- Every subsequent callback retains a previously recorded refusal. -/
theorem marked_sticky {ι σ : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT σ ProbComp)) (bad : spec.Domain → σ → Prop)
    (query : spec.Domain) (state : σ × Bool) (flagged : state.2 = true)
    (result : spec.Range query × (σ × Bool)) (supported : result ∈ support ((marked handler bad query).run state)) :
    result.2.2 = true := by
  simp only [marked, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
  rcases supported with ⟨reply, _, rfl⟩
  simp only [flagged, Bool.true_or]

/-- The first refusing query is marked independently of its optional reply or later continuation. -/
theorem marked_hit {ι σ : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT σ ProbComp)) (bad : spec.Domain → σ → Prop)
    (query : spec.Domain) (state : σ × Bool) (hit : bad query state.1)
    (result : spec.Range query × (σ × Bool)) (supported : result ∈ support ((marked handler bad query).run state)) :
    result.2.2 = true := by
  simp only [marked, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
  rcases supported with ⟨reply, _, rfl⟩
  simp only [hit, decide_true, Bool.or_true]

local instance (X : Type) : MeasurableSpace X := ⊤

/-- Before a marked refusal the full joint output distributions agree; after a refusal neither side has an unmarked output. -/
theorem marked_agree {ι σ : Type} {spec : OracleSpec ι}
    (left right : QueryImpl spec (StateT σ ProbComp)) (bad : spec.Domain → σ → Prop)
    (agree : ∀ query state, ¬ bad query state → (left query).run state = (right query).run state)
    (query : spec.Domain) (state : σ) (reply : spec.Range query) (nextState : σ) :
    𝒟[(marked left bad query).run (state, false)] {(reply, (nextState, false))} =
      𝒟[(marked right bad query).run (state, false)] {(reply, (nextState, false))} := by
  by_cases hit : bad query state
  · have zero (handler : QueryImpl spec (StateT σ ProbComp)) :
        𝒟[(marked handler bad query).run (state, false)] {(reply, (nextState, false))} = 0 := by
      rw [evalDist_apply_singleton]
      apply probOutput_eq_zero_of_not_mem_support
      intro supported
      exact Bool.false_ne_true (marked_hit handler bad query (state, false) hit (reply, (nextState, false)) supported)
    rw [zero, zero]
  · have equal := agree query state hit
    change left query state = right query state at equal
    simp only [marked, StateT.run, equal]

/-- The probability is measured in the same augmented source run, with coefficient one and arbitrary adaptive stopping and final output. -/
theorem marked_distance {ι σ X : Type} {spec : OracleSpec ι}
    (left right : QueryImpl spec (StateT σ ProbComp)) (bad : spec.Domain → σ → Prop)
    (agree : ∀ query state, ¬ bad query state → (left query).run state = (right query).run state)
    (client : OracleComp spec X) (state : σ) :
    tvDist ((simulateQ (marked left bad) client).run (state, false))
      ((simulateQ (marked right bad) client).run (state, false)) ≤
      (𝒟[(fun result => result.2.2) <$> (simulateQ (marked left bad) client).run (state, false)] {true}).toReal := by
  rw [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map]
  exact OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad
      _ _ client state
      (fun query before reply after => by simpa only [evalDist_apply_singleton] using marked_agree left right bad agree query before reply after)
      (marked_sticky left bad) (marked_sticky right bad)

/-- Erasing the sticky flag preserves every adaptive reply and the complete original ledger. -/
theorem marked_client {ι σ X : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT σ ProbComp)) (bad : spec.Domain → σ → Prop)
    (client : OracleComp spec X) (state : σ × Bool) :
    Prod.map id Prod.fst <$> (simulateQ (marked handler bad) client).run state =
      (simulateQ handler client).run state.1 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst (marked_step handler bad) client state

/-- Removing only the flag gives the same coefficient-one bound on the full terminal output and state. -/
theorem unmarked_distance {ι σ X : Type} {spec : OracleSpec ι}
    (left right : QueryImpl spec (StateT σ ProbComp)) (bad : spec.Domain → σ → Prop)
    (agree : ∀ query state, ¬ bad query state → (left query).run state = (right query).run state)
    (client : OracleComp spec X) (state : σ) :
    tvDist ((simulateQ left client).run state) ((simulateQ right client).run state) ≤
      (𝒟[(fun result => result.2.2) <$> (simulateQ (marked left bad) client).run (state, false)] {true}).toReal := by
  have bound := (tvDist_map_le (Prod.map id Prod.fst)
    ((simulateQ (marked left bad) client).run (state, false))
    ((simulateQ (marked right bad) client).run (state, false))).trans
      (marked_distance left right bad agree client state)
  simpa only [marked_client] using bound

/-- The actual nonce-refusal event is computed from the reached original role and the same run's complete selected ledger. -/
noncomputable def nonceBad (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (query : (Optional (RawCtxProtocolReveals.SourceSpec S B)).Domain) (state : Full M P I D K A S B) : Prop :=
  RawCtxSelectedFamilyLiveCompiler.Stops prior parent target nonce next sender query state.1 state.2.2

/-- The whole adaptive original hidden-read-stopped source differs from the projected selected CTX compiler by at most the probability of an actual nonce refusal, with coefficient one. All complete source outputs are compared before choosing a secrecy/authentication event. -/
theorem source_distance (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : Full M P I D K A S B) :
    tvDist
      (((simulateQ (RawCtxSelectedMessageStopping.stopping
        (RawCtxSelectedMessageStopping.sourceRecord source writer prior parent key target nonce next sender route read)) client).run).run (project state))
      (Prod.map id project <$> (simulateQ (compiled source writer prior parent key target nonce next sender route read) (optionalClient client)).run state) ≤
      (𝒟[(fun result => result.2.2) <$>
        (simulateQ (marked (augmented source writer prior parent key target nonce next sender route read)
          (nonceBad prior parent target nonce next sender)) (optionalClient client)).run (state, false)] {true}).toReal := by
  have bound := (tvDist_map_le (Prod.map id project)
    ((simulateQ (augmented source writer prior parent key target nonce next sender route read) (optionalClient client)).run state)
    ((simulateQ (compiled source writer prior parent key target nonce next sender route read) (optionalClient client)).run state)).trans
      (unmarked_distance _ _ (nonceBad prior parent target nonce next sender)
        (augmented_nonstop source writer prior parent key target nonce next sender route read) (optionalClient client) state)
  simpa only [augmented_client] using bound

noncomputable def component (source : FixedHkdfSha512NoSaltSource) (key : RootOutput) (read : RawCtxReceive.FrameDecoder) :
    QueryImpl AdaptiveCtxDynamicKnownKeys.Spec (StateT (RawCtxSelectedReceiveCompiler.State A) ProbComp) :=
  fun query => RawCtxSelectedReceiveCompiler.evaluated source key read ((QueryImpl.id' AdaptiveCtxDynamicKnownKeys.Spec) query)

private theorem component_program {X : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec X) :
    simulateQ (component (A := A) source key read) work = RawCtxSelectedReceiveCompiler.evaluated source key read work := by
  unfold component
  have same := RawCtxSelectedReceiveCompiler.evaluated_program (A := A) source key read (QueryImpl.id' AdaptiveCtxDynamicKnownKeys.Spec) work
  simpa only [simulateQ_id'] using same

/-- The complete callback simulation is the interpretation of one executable adaptive CTX program with no explicit selected-key argument. All challenger replies flow through the original continuation before the final state reassociation. -/
theorem compiled_client (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : Full M P I D K A S B) :
    (simulateQ (compiled source writer prior parent key target nonce next sender route read) (optionalClient client)).run state =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (RawCtxSelectedReceiveCompiler.evaluated source key read
          (RawCtxSelectedFamilyLiveCompiler.client source writer prior parent target nonce next sender route read client state.1)).run state.2 := by
  have callbacks : (fun query => PqxdhSelectedStateInterpreter.evaluate (component (A := A) source key read)
        ((RawCtxSelectedFamilyLiveCompiler.impl (P := P) (I := I) (D := D) (K := K) (S := S) (B := B)
          source writer prior parent target nonce next sender route read query).run)) =
      compiled source writer prior parent key target nonce next sender route read := by
    funext query before
    simp only [PqxdhSelectedStateInterpreter.evaluate, component_program]
    rfl
  have same := PqxdhSelectedStateInterpreter.program (component (A := A) source key read)
    ((fun query => (RawCtxSelectedFamilyLiveCompiler.impl (P := P) (I := I) (D := D) (K := K)
      source writer prior parent target nonce next sender route read query).run) :
      QueryImpl (Optional (RawCtxProtocolReveals.SourceSpec S B)) (StateT (Front M P I D K S B) RawCtxSelectedOwnerCompiler.Base)) (optionalClient client)
  rw [optional_client, callbacks] at same
  have applied := congrArg (fun work => work.run state) same.symm
  unfold PqxdhSelectedStateInterpreter.evaluate at applied
  simp only [component_program] at applied
  convert applied using 1
  rfl

/-- The complete original source distribution is within the exact nonce-refusal probability of the single executable CTX reduction. The executable has the concrete adaptive query/candidate bounds proved in FamilyLiveCompiler. -/
theorem executable_distance (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : Full M P I D K A S B) :
    tvDist
      (((simulateQ (RawCtxSelectedMessageStopping.stopping
        (RawCtxSelectedMessageStopping.sourceRecord source writer prior parent key target nonce next sender route read)) client).run).run (project state))
      (RawCtxSelectedFamilyLiveCompiler.output <$>
        (RawCtxSelectedReceiveCompiler.evaluated source key read
          (RawCtxSelectedFamilyLiveCompiler.client source writer prior parent target nonce next sender route read client state.1)).run state.2) ≤
      (𝒟[(fun result => result.2.2) <$>
        (simulateQ (marked (augmented source writer prior parent key target nonce next sender route read)
          (nonceBad prior parent target nonce next sender)) (optionalClient client)).run (state, false)] {true}).toReal := by
  have bound := source_distance source writer prior parent key target nonce next sender route read client state
  rw [compiled_client] at bound
  simp only [Functor.map_map, Prod.map_def, id_eq, project] at bound
  convert bound using 1
  rfl

end BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.optional_client' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.optional_client
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.augmented_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.augmented_step
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.augmented_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.augmented_client
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.augmented_nonstop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.augmented_nonstop
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.marked_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.marked_step
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.marked_sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.marked_sticky
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.marked_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.marked_hit
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.marked_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.marked_agree
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.marked_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.marked_distance
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.marked_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.marked_client
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.unmarked_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.unmarked_distance
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.source_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.source_distance
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.compiled_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.compiled_client
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.executable_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.executable_distance
