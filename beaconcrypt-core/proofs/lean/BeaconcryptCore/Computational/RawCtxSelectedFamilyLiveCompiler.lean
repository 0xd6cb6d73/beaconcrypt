import BeaconcryptCore.Computational.RawCtxSelectedFamilyCompiler
import BeaconcryptCore.Computational.RawCtxSelectedMessageStopBounds

/-!
The actual adaptive record/reveal client uses the checked key-free finite-family compiler. Every reveal appends the original observation before hidden-material stopping, and every record/public attempt advances the original history position. Nonce stopping retains the entire entry role family and accumulated component state. The source comparison uses the exact preexisting hidden-read stopping experiment, whose original byte freshness theorem applies to arbitrary final decisions.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedFamilyLiveCompiler
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
open RawCtxSelectedReceiveCompiler (State project evaluated)
open RawCtxSelectedOwnerCompiler (Kernel Base)
open RawCtxSelectedMessageFreshness RawCtxSelectedMessageReveals RawCtxSelectedMessageFamily
variable {A M P I D K Result : Type} {S B : Nat}
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Front (M P I D K : Type) (S B : Nat) := RawCtxSelectedMessageReveals.State M P I D K S B

def publish {X : Type} (before : Front M P I D K S B)
    (reply : Option (X × Roles M P I D K S B)) : Option X × Front M P I D K S B :=
  match reply with
  | none => (none, (before.1, tick before.2))
  | some (value, roles) => (some value, (roles, tick before.2))

noncomputable def impl (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) :
    QueryImpl (RawCtxProtocolReveals.SourceSpec S B) (OptionT (StateT (Front M P I D K S B) Base)) :=
  fun query => OptionT.mk fun before => match query with
  | .inl request => publish before <$> RawCtxSelectedFamilyCompiler.family source writer prior parent target nonce next sender route read request before.1
  | .inr request =>
      let observed := RawCtxSelectedMessageReveals.step request before
      pure (emit request observed.1, observed.2)

noncomputable def client (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (before : Front M P I D K S B) : Base (Option Result × Front M P I D K S B) :=
  ((simulateQ (impl source writer prior parent target nonce next sender route read) original).run).run before

noncomputable def Stops (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (before : Front M P I D K S B)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) : Prop :=
  match query with
  | .inl request => RawCtxSelectedFamilyCompiler.Stops prior parent target nonce next sender request before.1 state
  | .inr _ => False

def output {X : Type} (result : (Option X × Front M P I D K S B) × RawCtxSelectedReceiveCompiler.State A) :=
  (result.1.1, (result.1.2, project result.2))

/-- The original reveal is installed before hidden-slot stopping. No component call is made, and no unavailable selected bytes are returned. -/
theorem read_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (request : RawCtxProtocolReveals.Request S B) (before : Front M P I D K S B) :
    ((impl source writer prior parent target nonce next sender route read (.inr request)).run).run before =
      pure (emit request (RawCtxSelectedMessageReveals.step request before).1, (RawCtxSelectedMessageReveals.step request before).2) := rfl

/-- The withheld original read itself falsifies the original byte-based freshness predicate, independently of the final adversarial decision. -/
theorem read_not_fresh (key : RootOutput) (remaining disclosed : List RatchetChain)
    (request : RawCtxProtocolReveals.Request S B) (before : Front M P I D K S B)
    (stopped : emit request (RawCtxSelectedMessageReveals.step request before).1 = none) :
    ¬ RawCtxLiveLineage.Fresh (RawCtxFreshChainCut.concreteChain key :: remaining) disclosed
      (interpretHistory key (RawCtxSelectedMessageReveals.step request before).2.2) :=
  source_stopped key request before remaining disclosed stopped

/-- One actual adaptive live step is exactly the original source experiment stopped only at hidden disclosure, except for its separately charged selected nonce stop. Every original private role, history observation, API result and cache is retained. -/
theorem step_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (before : Front M P I D K S B) (state : RawCtxSelectedReceiveCompiler.State A) :
    output <$> (evaluated source key read (((impl source writer prior parent target nonce next sender route read query).run).run before)).run state =
      if Stops prior parent target nonce next sender query before state.2 then pure (none, ((before.1, tick before.2), project state))
      else ((RawCtxSelectedMessageStopping.stopping
        (RawCtxSelectedMessageStopping.sourceRecord source writer prior parent key target nonce next sender route read) query).run).run (before, project state) := by
  cases query with
  | inr request =>
    have clear : ¬ Stops prior parent target nonce next sender (.inr request) before state.2 := by simp only [Stops, not_false_eq_true]
    rw [ite_eq_right (fun h => (clear h).elim), read_step]
    rfl
  | inl request =>
    change output <$> (evaluated source key read (publish before <$>
      RawCtxSelectedFamilyCompiler.family source writer prior parent target nonce next sender route read request before.1)).run state = _
    rw [RawCtxSelectedReceiveCompiler.evaluated_map, StateT.run_map]
    have mapped := congrArg (fun work => (fun result => ((publish before result.1).1, ((publish before result.1).2, result.2))) <$> work)
      (RawCtxSelectedFamilyCompiler.family_source source writer prior parent key target nonce next sender route read request before.1 state)
    simp only [Functor.map_map, Prod.map_def, id_eq, output, apply_ite, map_pure, publish] at mapped ⊢
    simp only [Stops, RawCtxSelectedMessageStopping.stopping, RawCtxSelectedMessageStopping.sourceRecord,
      QueryImpl.flattenStateT, StateT.run, OptionT.run_mk,
      RawCtxSelectedFamilyCompiler.originalFrontend, RawCtxSelectedFamilyCompiler.originalPublic,
      RawCtxSelectedOwnerCompiler.originalCalls, frontend] at mapped ⊢
    dsimp only [StateT.mk]
    simpa only [Functor.map_map] using mapped

/-- Every concrete live request pays at most one dynamic record/public call, while reveals cost zero component calls. -/
theorem step_queries (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (before : Front M P I D K S B) :
    (((impl source writer prior parent target nonce next sender route read query).run).run before).IsTotalQueryBound
      (RawCtxRevealBudgets.weight (fun _ => 1) 0 query) := by
  cases query with
  | inl request =>
    simpa only [impl, OptionT.run_mk, StateT.run, RawCtxRevealBudgets.weight, IsTotalQueryBound, isQueryBound_map_iff] using
      RawCtxSelectedFamilyCompiler.family_queries source writer prior parent target nonce next sender route read request before.1
  | inr request => trivial

/-- The complete adaptive schedule is billed from all six source budget coordinates. The bound counts every attempted component call, including rejected records and a stopping seal. -/
theorem client_queries (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (budget : RawCtxRevealBudgets.Budget)
    (bounded : RawCtxRevealBudgets.Bounded original budget) (before : Front M P I D K S B) :
    (client source writer prior parent target nonce next sender route read original before).IsTotalQueryBound
      (RawCtxRevealBudgets.bill (fun _ => 1) 0 budget) := by
  unfold client
  induction original using OracleComp.inductionOn generalizing budget before with
  | pure value => trivial
  | query_bind query continuation ih =>
    change RawCtxRevealBudgets.permitted query budget ∧
      ∀ value, RawCtxRevealBudgets.Bounded (continuation value) (RawCtxRevealBudgets.remaining query budget) at bounded
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
    have head := step_queries source writer prior parent target nonce next sender route read query before
    have rest : ∀ reply : Option ((RawCtxProtocolReveals.SourceSpec S B).Range query) × Front M P I D K S B,
        ((reply.1.elim (pure none) (fun value => (simulateQ (impl source writer prior parent target nonce next sender route read) (continuation value)).run)).run reply.2).IsTotalQueryBound
          (RawCtxRevealBudgets.bill (fun _ => 1) 0 (RawCtxRevealBudgets.remaining query budget)) := by
      rintro ⟨none | value, nextState⟩
      · trivial
      · exact ih value _ (bounded.2 value) nextState
    have bound := isTotalQueryBound_bind head rest
    simpa only [RawCtxRevealBudgets.bill_step (fun _ => 1) 0 query budget bounded.1] using bound

/-- Every actual read adds at most one known candidate; both nonce stopping and original record publication retain the complete prior observation history. -/
theorem step_candidates (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (disclosed : List RatchetChain)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (before : Front M P I D K S B)
    (result : Option ((RawCtxProtocolReveals.SourceSpec S B).Range query) × Front M P I D K S B)
    (supported : result ∈ support (((impl source writer prior parent target nonce next sender route read query).run).run before)) :
    (keys disclosed result.2.2).length ≤ (keys disclosed before.2).length + (if query.isRight then 1 else 0) := by
  cases query with
  | inl request =>
    simp only [impl, OptionT.run_mk, StateT.run] at supported
    rcases mem_support_map_peel _ _ supported with ⟨child, _, rfl⟩
    cases child with
    | none => exact Nat.le_refl _
    | some value => exact Nat.le_refl _
  | inr request =>
    simp only [read_step] at supported
    subst result
    exact step_probe_bound disclosed request before

/-- Every possible challenger reply continuation obeys the actual source reveal budget before any component game is chosen. -/
theorem client_candidates (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (disclosed : List RatchetChain)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (qReveal : Nat)
    (bounded : original.IsQueryBoundP (fun query => query.isRight = true) qReveal)
    (state : Front M P I D K S B) (result : Option Result × Front M P I D K S B)
    (supported : result ∈ support (client source writer prior parent target nonce next sender route read original state)) :
    (keys disclosed result.2.2).length ≤ (keys disclosed state.2).length + qReveal := by
  induction original using OracleComp.inductionOn generalizing qReveal state with
  | pure value =>
    simp only [client, simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query continuation ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    simp only [client, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind, mem_support_bind_iff] at supported
    rcases supported with ⟨reply, head, tail⟩
    have step := step_candidates source writer prior parent target nonce next disclosed sender route read query state reply head
    rcases reply with ⟨none | value, nextState⟩
    · simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff] at tail
      subst result
      dsimp only at step ⊢
      by_cases selected : query.isRight = true <;> simp_all only [Bool.false_eq_true, not_true_eq_false, not_false_eq_true, false_or, ↓reduceIte]
      all_goals omega
    · simp only [Option.elim_some] at tail
      have rest := ih value _ (bounded.2 value) nextState tail
      dsimp only at step
      by_cases selected : query.isRight = true <;> simp_all only [Bool.false_eq_true, not_true_eq_false, not_false_eq_true, false_or, ↓reduceIte]
      all_goals omega

end BeaconcryptCore.Computational.RawCtxSelectedFamilyLiveCompiler

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyLiveCompiler.read_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyLiveCompiler.read_step
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyLiveCompiler.read_not_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyLiveCompiler.read_not_fresh
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyLiveCompiler.step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyLiveCompiler.step_source
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyLiveCompiler.step_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyLiveCompiler.step_queries
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyLiveCompiler.client_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyLiveCompiler.client_queries
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyLiveCompiler.step_candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyLiveCompiler.step_candidates
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyLiveCompiler.client_candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyLiveCompiler.client_candidates
