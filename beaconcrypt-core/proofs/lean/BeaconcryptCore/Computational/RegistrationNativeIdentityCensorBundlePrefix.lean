-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedMain
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixJournal
import BeaconcryptCore.Computational.RegistrationNativeObservedStageTrace
/-! A cut immediately before one fixed public all-attempt bundle ordinal retains the original owner index and query continuation. It factors the complete unmodified source program without inspecting ownership or private freshness. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundlePrefix
open RegistrationNativeRawAdapter (TypedSpec)
variable {A S : Type}

inductive Cut (A : Type) where
  | returned : A → Cut A
  | bundle : (index : Nat) → (TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec A) → Cut A

def stop (bundle : Nat) (work : OracleComp TypedSpec A) : Nat → OracleComp TypedSpec (Cut A) :=
  OracleComp.construct (C := fun _ => Nat → OracleComp TypedSpec (Cut A))
    (fun value _cursor => pure (.returned value))
    (fun query next continued cursor => match query with
      | .inr (.bundle index) =>
          if cursor = bundle then pure (.bundle index next)
          else do let reply ← TypedSpec.query (.inr (.bundle index)); continued reply (cursor+1)
      | query => do let reply ← TypedSpec.query query; continued reply cursor) work

def resume : Cut A → OracleComp TypedSpec A
  | .returned value => pure value
  | .bundle index next => TypedSpec.query (.inr (.bundle index)) >>= next

private theorem stop_pure (bundle cursor : Nat) (value : A) :
    stop bundle (pure value) cursor = pure (.returned value) := rfl

private theorem stop_step (bundle cursor : Nat) (query : TypedSpec.Domain)
    (next : TypedSpec.Range query → OracleComp TypedSpec A) :
    stop bundle (TypedSpec.query query >>= next) cursor =
      (match query with
      | .inr (.bundle value) =>
          if cursor = bundle then pure (.bundle value next)
          else do let reply ← TypedSpec.query (.inr (.bundle value)); stop bundle (next reply) (cursor+1)
      | query => do let reply ← TypedSpec.query query; stop bundle (next reply) cursor) := by
  cases query with
  | inl coin => rfl
  | inr command => cases command <;> rfl

/-- Resuming the selected public query and every original later callback recovers the literal original AST. -/
theorem factor (bundle cursor : Nat) (work : OracleComp TypedSpec A) :
    (stop bundle work cursor >>= resume) = work := by
  induction work using OracleComp.inductionOn generalizing cursor with
  | pure value => rw [stop_pure,pure_bind]; rfl
  | query_bind query next ih =>
      rw [stop_step]
      cases query with
      | inl coin => simp only [bind_assoc,ih]
      | inr command =>
          cases command
          case bundle value =>
            by_cases chosen : cursor = bundle
            · simp only [chosen,ite_true,pure_bind,resume]
            · simp only [chosen,ite_false,bind_assoc,ih]
          all_goals simp only [bind_assoc,ih]

/-- Every stateful private source interpretation factors at the same public bundle attempt, keeping all state and its literal original suffix. -/
theorem execution {m : Type → Type} [Monad m] [LawfulMonad m]
    (bundle cursor : Nat) (handler : QueryImpl TypedSpec (StateT S m))
    (work : OracleComp TypedSpec A) (before : S) :
    (simulateQ handler work).run before = (do
      let cut ← (simulateQ handler (stop bundle work cursor)).run before
      (simulateQ handler (resume cut.1)).run cut.2) := by
  have law := congrArg (fun code => (simulateQ handler code).run before) (factor bundle cursor work)
  simpa only [simulateQ_bind,StateT.run_bind] using law.symm

/-- The public cut preserves every original typed query-class allowance, charging every earlier failed callback and adding no query. -/
theorem query_bound (bundle cursor : Nat) (predicate : TypedSpec.Domain → Prop) [DecidablePred predicate]
    (cap : Nat) (work : OracleComp TypedSpec A) (bounded : work.IsQueryBoundP predicate cap) :
    (stop bundle work cursor).IsQueryBoundP predicate cap := by
  induction work using OracleComp.inductionOn generalizing cursor cap with
  | pure value => exact isQueryBoundP_pure predicate _ _
  | query_bind query next ih =>
      obtain ⟨first,later⟩ := (isQueryBoundP_query_bind_iff predicate _ _ _).mp bounded
      rw [stop_step]
      cases query with
      | inl coin =>
          exact (isQueryBoundP_query_bind_iff predicate _ _ _).mpr ⟨first,fun reply => ih reply cursor _ (later reply)⟩
      | inr command =>
          cases command
          case bundle value =>
            by_cases chosen : cursor = bundle
            · simp only [chosen,ite_true]
              exact isQueryBoundP_pure predicate _ _
            · simp only [chosen,ite_false]
              exact (isQueryBoundP_query_bind_iff predicate _ _ _).mpr ⟨first,fun reply => ih reply (cursor+1) _ (later reply)⟩
          all_goals exact (isQueryBoundP_query_bind_iff predicate _ _ _).mpr ⟨first,fun reply => ih reply cursor _ (later reply)⟩


section SourcePrefix
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {KemSK Platform : Type} {mlSource : RegistrationNativeMldsa.Source}
local notation "FullState" => Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource

noncomputable def marked (joint : PqxdhJointIdentity.Primitives) (selected bundle : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (frontend : QueryImpl TypedSpec Main) : QueryImpl TypedSpec (StateT FullState ProbComp) :=
  RegistrationNativeIdentityCensorPublicSource.callback
    (if masked then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)
    (RegistrationNativeIdentityCensorPublicClient.callback selected bundle placeholder frontend)

noncomputable def original (joint : PqxdhJointIdentity.Primitives) (frontend : QueryImpl TypedSpec Main) :=
  fun query => RegistrationNativePlatformIdentityCtxMain.interpret joint (frontend query)

private theorem entered_unarmed (bundle : Nat) (query : TypedSpec.Domain) (before : FullState)
    (missing : before.1.2.target = none)
    (different : ∀ index, query = .inr (.bundle index) → before.1.2.bundles ≠ bundle) :
    RegistrationNativeIdentityCensorPrefix.Unarmed (RegistrationNativeIdentityCensorCompiler.enter bundle query before.1.2) :=
  RegistrationNativeIdentityCensorUnarmedMain.enter bundle query before.1.2 missing different

private theorem handler_source (joint : PqxdhJointIdentity.Primitives) (selected bundle : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (frontend : QueryImpl TypedSpec Main) (query : TypedSpec.Domain) (before : FullState)
    (missing : before.1.2.target = none)
    (different : ∀ index, query = .inr (.bundle index) → before.1.2.bundles ≠ bundle) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (marked joint selected bundle placeholder masked frontend query).run before =
      (original joint frontend query).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  rw [marked, RegistrationNativeIdentityCensorPublicSource.current]
  exact RegistrationNativeIdentityCensorUnarmedMain.source joint selected placeholder masked (frontend query)
    ((before.1.1, RegistrationNativeIdentityCensorCompiler.enter bundle query before.1.2), before.2)
    (entered_unarmed bundle query before missing different)

private theorem handler_control (joint : PqxdhJointIdentity.Primitives) (selected bundle : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (frontend : QueryImpl TypedSpec Main) (query : TypedSpec.Domain) (before : FullState)
    (missing : before.1.2.target = none)
    (different : ∀ index, query = .inr (.bundle index) → before.1.2.bundles ≠ bundle)
    (result : TypedSpec.Range query × FullState)
    (reached : result ∈ support ((marked joint selected bundle placeholder masked frontend query).run before)) :
    result.2.1.2.bundles = before.1.2.bundles + (if RegistrationNativePlatformIdentityCtxSigningTrace.IsBundle query then 1 else 0) ∧
      result.2.1.2.target = none := by
  rw [marked, RegistrationNativeIdentityCensorPublicSource.current] at reached
  have kept := RegistrationNativeIdentityCensorUnarmedFrame.main joint selected placeholder masked (frontend query)
    ((before.1.1, RegistrationNativeIdentityCensorCompiler.enter bundle query before.1.2), before.2)
    (entered_unarmed bundle query before missing different) result reached
  have count := congrArg (fun value => value.1.bundles) kept.1
  change result.2.1.2.bundles = (RegistrationNativeIdentityCensorCompiler.enter bundle query before.1.2).bundles at count
  refine ⟨?_, kept.2.2.1⟩
  rw [count]
  cases query with
  | inl coin => rfl
  | inr command => cases command <;> rfl


/-- Every actual callback before the fixed bundle ordinal advances only its public all-attempt counter and retains the missing target, through arbitrary source and writer failures. -/
theorem unarmed_step (joint : PqxdhJointIdentity.Primitives) (selected bundle : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (frontend : QueryImpl TypedSpec Main) (query : TypedSpec.Domain) (before : FullState)
    (missing : before.1.2.target = none)
    (different : ∀ index, query = .inr (.bundle index) → before.1.2.bundles ≠ bundle)
    (result : TypedSpec.Range query × FullState)
    (reached : result ∈ support ((marked joint selected bundle placeholder masked frontend query).run before)) :
    result.2.1.2.bundles = before.1.2.bundles + (if RegistrationNativePlatformIdentityCtxSigningTrace.IsBundle query then 1 else 0) ∧
      result.2.1.2.target = none ∧ result.2.1.2.active = false := by
  have control := handler_control joint selected bundle placeholder masked frontend query before missing different result reached
  rw [marked, RegistrationNativeIdentityCensorPublicSource.current] at reached
  have kept := RegistrationNativeIdentityCensorUnarmedFrame.main joint selected placeholder masked (frontend query)
    ((before.1.1, RegistrationNativeIdentityCensorCompiler.enter bundle query before.1.2), before.2)
    (entered_unarmed bundle query before missing different) result reached
  exact ⟨control.1,control.2,kept.2.2.2⟩


private theorem step_source {X : Type} (joint : PqxdhJointIdentity.Primitives) (selected bundle : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (frontend : QueryImpl TypedSpec Main) (query : TypedSpec.Domain)
    (next : TypedSpec.Range query → OracleComp TypedSpec X) (before : FullState)
    (missing : before.1.2.target = none)
    (different : ∀ index, query = .inr (.bundle index) → before.1.2.bundles ≠ bundle)
    (continued : ∀ result ∈ support ((marked joint selected bundle placeholder masked frontend query).run before),
      Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
        (simulateQ (marked joint selected bundle placeholder masked frontend) (next result.1)).run result.2 =
        (simulateQ (original joint frontend) (next result.1)).run (RegistrationNativeIdentityCensorActualHashSource.project result.2)) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (simulateQ (marked joint selected bundle placeholder masked frontend) (TypedSpec.query query >>= next)).run before =
      (simulateQ (original joint frontend) (TypedSpec.query query >>= next)).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
  rw [← handler_source joint selected bundle placeholder masked frontend query before missing different, bind_map_left]
  apply bind_congr_of_forall_mem_support
  intro result reached
  exact continued result reached

private theorem stop_other (position cursor : Nat) (query : TypedSpec.Domain)
    (next : TypedSpec.Range query → OracleComp TypedSpec A)
    (other : ¬ ∃ index, query = .inr (.bundle index)) :
    stop position (TypedSpec.query query >>= next) cursor =
      ((TypedSpec.query query : OracleComp TypedSpec (TypedSpec.Range query)) >>= fun reply => stop position (next reply) cursor) := by
  cases query with
  | inl coin => rfl
  | inr command =>
    cases command <;> try rfl
    rename_i index
    exact False.elim (other ⟨index, rfl⟩)

private theorem other_charge (query : TypedSpec.Domain) (other : ¬ ∃ index, query = .inr (.bundle index)) :
    ¬ RegistrationNativePlatformIdentityCtxSigningTrace.IsBundle query := by
  cases query with
  | inl coin => exact id
  | inr command =>
    cases command <;> try exact id
    rename_i index
    exact False.elim (other ⟨index, rfl⟩)

/-- The entire literal source prefix before the fixed public bundle has the original full Main/P/pool/cache/journal marginal. Only the public Mode and private censor metadata are erased; every earlier failure remains in that same prefix. -/
theorem source (joint : PqxdhJointIdentity.Primitives) (selected position : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (frontend : QueryImpl TypedSpec Main) (work : OracleComp TypedSpec A)
    (cursor : Nat) (before : FullState) (room : cursor ≤ position)
    (count : before.1.2.bundles = cursor) (missing : before.1.2.target = none) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (simulateQ (marked joint selected position placeholder masked frontend) (stop position work cursor)).run before =
      (simulateQ (original joint frontend) (stop position work cursor)).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  induction work using OracleComp.inductionOn generalizing before cursor with
  | pure value =>
    simp only [stop_pure, simulateQ_pure, StateT.run_pure, map_pure]
    rfl
  | query_bind query next ih =>
    by_cases bundled : ∃ index, query = .inr (.bundle index)
    · obtain ⟨index, rfl⟩ := bundled
      rw [stop_step]
      by_cases chosen : cursor = position
      · simp only [chosen, ite_true, simulateQ_pure, StateT.run_pure, map_pure]
        rfl
      · simp only [chosen, ite_false]
        have different : ∀ owner, (.inr (.bundle index) : TypedSpec.Domain) = .inr (.bundle owner) → before.1.2.bundles ≠ position := by
          intro _owner _same
          exact count ▸ chosen
        apply step_source joint selected position placeholder masked frontend (.inr (.bundle index)) _ before missing different
        intro result reached
        have control := handler_control joint selected position placeholder masked frontend (.inr (.bundle index)) before missing different result reached
        apply ih result.1 (cursor + 1) result.2 (by omega)
        · simpa only [RegistrationNativePlatformIdentityCtxSigningTrace.IsBundle, ite_true, count] using control.1
        · exact control.2
    · rw [stop_other position cursor query next bundled]
      have different : ∀ owner, query = .inr (.bundle owner) → before.1.2.bundles ≠ position := by
        intro owner same
        exact False.elim (bundled ⟨owner, same⟩)
      apply step_source joint selected position placeholder masked frontend query _ before missing different
      intro result reached
      have control := handler_control joint selected position placeholder masked frontend query before missing different result reached
      apply ih result.1 cursor result.2 room
      · simpa only [other_charge query bundled, ite_false, Nat.add_zero, count] using control.1
      · exact control.2


private theorem handler_journal (joint : PqxdhJointIdentity.Primitives) (selected bundle : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (frontend : QueryImpl TypedSpec Main) (query : TypedSpec.Domain) (before : FullState)
    (missing : before.1.2.target = none)
    (different : ∀ index, query = .inr (.bundle index) → before.1.2.bundles ≠ bundle)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned before.1.2 before.2)
    (result : TypedSpec.Range query × FullState)
    (reached : result ∈ support ((marked joint selected bundle placeholder masked frontend query).run before)) :
    RegistrationNativeIdentityCensorPrefixJournal.Aligned result.2.1.2 result.2.2 := by
  rw [marked, RegistrationNativeIdentityCensorPublicSource.current] at reached
  have prior := entered_unarmed bundle query before missing different
  have enteredJournal : RegistrationNativeIdentityCensorPrefixJournal.Aligned
      (RegistrationNativeIdentityCensorCompiler.enter bundle query before.1.2) before.2 := by
    cases query with
    | inl coin => exact journal
    | inr command => cases command <;> exact journal
  cases masked with
  | false =>
    rw [RegistrationNativeIdentityCensorUnarmedMain.paired joint selected placeholder (frontend query) _ prior] at reached
    exact RegistrationNativeIdentityCensorPrefixJournal.main joint selected placeholder (frontend query) _ enteredJournal prior result reached
  | true =>
    exact RegistrationNativeIdentityCensorPrefixJournal.main joint selected placeholder (frontend query) _ enteredJournal prior result reached

def Status (position : Nat) : Cut A → Nat → Prop
  | .returned _, cursor => cursor ≤ position
  | .bundle _ _, cursor => cursor = position

/-- The actual public cut has its exact bundle ordinal and absent target, together with the complete warm physical-input journal. Every earlier failure is counted and retained. -/
theorem status (joint : PqxdhJointIdentity.Primitives) (selected position : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (frontend : QueryImpl TypedSpec Main) (work : OracleComp TypedSpec A)
    (cursor : Nat) (before : FullState) (room : cursor ≤ position)
    (count : before.1.2.bundles = cursor) (missing : before.1.2.target = none)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned before.1.2 before.2)
    (result : Cut A × FullState)
    (reached : result ∈ support ((simulateQ (marked joint selected position placeholder masked frontend) (stop position work cursor)).run before)) :
    Status position result.1 result.2.1.2.bundles ∧ result.2.1.2.target = none ∧
      RegistrationNativeIdentityCensorPrefixJournal.Aligned result.2.1.2 result.2.2 := by
  induction work using OracleComp.inductionOn generalizing before cursor result with
  | pure value =>
    simp only [stop_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
    cases reached
    exact ⟨count ▸ room, missing, journal⟩
  | query_bind query next ih =>
    have forward (bump : Nat) (charged : (if RegistrationNativePlatformIdentityCtxSigningTrace.IsBundle query then 1 else 0) = bump)
        (space : cursor + bump ≤ position)
        (different : ∀ index, query = .inr (.bundle index) → before.1.2.bundles ≠ position)
        (called : result ∈ support ((simulateQ (marked joint selected position placeholder masked frontend)
          ((TypedSpec.query query : OracleComp TypedSpec _) >>= fun reply => stop position (next reply) (cursor+bump))).run before)) :
        Status position result.1 result.2.1.2.bundles ∧ result.2.1.2.target = none ∧
          RegistrationNativeIdentityCensorPrefixJournal.Aligned result.2.1.2 result.2.2 := by
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at called
      obtain ⟨middle, first, later⟩ := called
      have control := handler_control joint selected position placeholder masked frontend query before missing different middle first
      have kept := handler_journal joint selected position placeholder masked frontend query before missing different journal middle first
      apply ih middle.1 (cursor+bump) middle.2 space _ control.2 kept result later
      simpa only [count, charged] using control.1
    rw [stop_step] at reached
    cases query with
    | inl coin => exact forward 0 rfl (by omega) (by intro index same; cases same) reached
    | inr command =>
      cases command
      case bundle index =>
        by_cases chosen : cursor = position
        · simp only [chosen, ite_true, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
          cases reached
          exact ⟨count.trans chosen, missing, journal⟩
        · simp only [chosen, ite_false] at reached
          exact forward 1 rfl (by omega) (by intro owner _same; exact count ▸ chosen) reached
      all_goals exact forward 0 rfl (by omega) (by intro index same; cases same) reached

local notation "PlainState" => RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform mlSource
local notation "project" => RegistrationNativeIdentityCensorActualHashSource.project
local notation "Call" => RegistrationNativeStageTrace.Call TypedSpec PlainState

private theorem observed_handler_source (joint : PqxdhJointIdentity.Primitives) (selected bundle : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (frontend : QueryImpl TypedSpec Main) (query : TypedSpec.Domain) (before : FullState)
    (leading : List Call) (missing : before.1.2.target=none)
    (different : ∀ index,query=.inr (.bundle index)→before.1.2.bundles≠bundle) :
    Prod.map id (Prod.map project id) <$>
      (RegistrationNativeObservedStageTrace.handler project (marked joint selected bundle placeholder masked frontend) query).run (before,leading) =
      (RegistrationNativeStageTrace.handler (original joint frontend) query).run (project before,leading) := by
  have equation := congrArg (Functor.map (fun result => (result.1,(result.2,
      leading++[⟨query,project before,result.1,result.2⟩]))))
    (handler_source joint selected bundle placeholder masked frontend query before missing different)
  simpa only [RegistrationNativeObservedStageTrace.handler,RegistrationNativeStageTrace.handler,StateT.run,
    Functor.map_map,Prod.map_def,id_eq] using equation

private theorem observed_step_source {X : Type} (joint : PqxdhJointIdentity.Primitives) (selected bundle : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (frontend : QueryImpl TypedSpec Main) (query : TypedSpec.Domain)
    (next : TypedSpec.Range query → OracleComp TypedSpec X) (before : FullState) (leading : List Call)
    (missing : before.1.2.target=none) (different : ∀ index,query=.inr (.bundle index)→before.1.2.bundles≠bundle)
    (continued : ∀ result∈support ((RegistrationNativeObservedStageTrace.handler project (marked joint selected bundle placeholder masked frontend) query).run (before,leading)),
      Prod.map id (Prod.map project id) <$>
        (simulateQ (RegistrationNativeObservedStageTrace.handler project (marked joint selected bundle placeholder masked frontend)) (next result.1)).run result.2 =
      (simulateQ (RegistrationNativeStageTrace.handler (original joint frontend)) (next result.1)).run (project result.2.1,result.2.2)) :
    Prod.map id (Prod.map project id) <$>
      (simulateQ (RegistrationNativeObservedStageTrace.handler project (marked joint selected bundle placeholder masked frontend))
        ((TypedSpec.query query : OracleComp TypedSpec _) >>=next)).run (before,leading) =
      (simulateQ (RegistrationNativeStageTrace.handler (original joint frontend))
        ((TypedSpec.query query : OracleComp TypedSpec _) >>=next)).run (project before,leading) := by
  simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
  rw [←observed_handler_source joint selected bundle placeholder masked frontend query before leading missing different,bind_map_left]
  apply bind_congr_of_forall_mem_support
  intro result reached
  exact continued result reached

/-- The SAME full before-b source marginal retains every projected chronological callback snapshot, not only its current state. The observer is private proof state and includes failed attempts. -/
theorem observed_source (joint : PqxdhJointIdentity.Primitives) (selected position : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (frontend : QueryImpl TypedSpec Main) (work : OracleComp TypedSpec A)
    (cursor : Nat) (before : FullState) (leading : List Call) (room : cursor≤position)
    (count : before.1.2.bundles=cursor) (missing : before.1.2.target=none) :
    Prod.map id (Prod.map project id) <$>
      (simulateQ (RegistrationNativeObservedStageTrace.handler project (marked joint selected position placeholder masked frontend))
        (stop position work cursor)).run (before,leading) =
      (simulateQ (RegistrationNativeStageTrace.handler (original joint frontend))
        (stop position work cursor)).run (project before,leading) := by
  induction work using OracleComp.inductionOn generalizing before leading cursor with
  | pure value =>
    simp only [stop_pure,simulateQ_pure,StateT.run_pure,map_pure]
    rfl
  | query_bind query next ih =>
    have forward (bump : Nat) (charged : (if RegistrationNativePlatformIdentityCtxSigningTrace.IsBundle query then 1 else 0)=bump)
        (space : cursor+bump≤position)
        (different : ∀ index,query=.inr (.bundle index)→before.1.2.bundles≠position) :
        Prod.map id (Prod.map project id) <$>
          (simulateQ (RegistrationNativeObservedStageTrace.handler project (marked joint selected position placeholder masked frontend))
            ((TypedSpec.query query : OracleComp TypedSpec _) >>=fun reply=>stop position (next reply) (cursor+bump))).run (before,leading) =
          (simulateQ (RegistrationNativeStageTrace.handler (original joint frontend))
            ((TypedSpec.query query : OracleComp TypedSpec _) >>=fun reply=>stop position (next reply) (cursor+bump))).run (project before,leading) := by
      apply observed_step_source joint selected position placeholder masked frontend query _ before leading missing different
      intro result reached
      simp only [RegistrationNativeObservedStageTrace.handler,StateT.run,support_map] at reached
      obtain ⟨inner,called,rfl⟩ := reached
      have control := handler_control joint selected position placeholder masked frontend query before missing different inner called
      apply ih inner.1 (cursor+bump) inner.2 _ space _ control.2
      simpa only [count,charged] using control.1
    by_cases bundled : ∃ index,query=.inr (.bundle index)
    · obtain ⟨index,rfl⟩ := bundled
      rw [stop_step]
      by_cases chosen : cursor=position
      · simp only [chosen,ite_true,simulateQ_pure,StateT.run_pure,map_pure]
        rfl
      · simp only [chosen,ite_false]
        exact forward 1 rfl (by omega) (by intro _ _;exact count ▸ chosen)
    · rw [stop_other position cursor query next bundled]
      exact forward 0 (by simp only [other_charge query bundled,ite_false]) room
        (by intro index same;exact False.elim (bundled ⟨index,same⟩))

end SourcePrefix

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundlePrefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundlePrefix.factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundlePrefix.factor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundlePrefix.execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundlePrefix.execution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundlePrefix.query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundlePrefix.query_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundlePrefix.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundlePrefix.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundlePrefix.status' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundlePrefix.status

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundlePrefix.observed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundlePrefix.observed_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundlePrefix.unarmed_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundlePrefix.unarmed_step
