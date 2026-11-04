-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPacketClient
/-! A cut immediately before one fixed public parsed-accept ordinal retains the original query continuation. It factors the complete unmodified source program without inspecting ownership or private freshness. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut
open RegistrationNativeRawAdapter (TypedSpec)
variable {A S : Type}
abbrev Packet := beaconcrypt_core.registration.InitPacket

inductive Cut (A : Type) where
  | returned : A → Cut A
  | accept : (packet : Packet) → (TypedSpec.Range (.inr (.accept packet)) → OracleComp TypedSpec A) → Cut A

def stop (accept : Nat) (work : OracleComp TypedSpec A) : Nat → OracleComp TypedSpec (Cut A) :=
  OracleComp.construct (C := fun _ => Nat → OracleComp TypedSpec (Cut A))
    (fun value _cursor => pure (.returned value))
    (fun query next continued cursor => match query with
      | .inr (.accept packet) =>
          if cursor = accept then pure (.accept packet next)
          else do let reply ← TypedSpec.query (.inr (.accept packet)); continued reply (cursor+1)
      | query => do let reply ← TypedSpec.query query; continued reply cursor) work

def resume : Cut A → OracleComp TypedSpec A
  | .returned value => pure value
  | .accept packet next => TypedSpec.query (.inr (.accept packet)) >>= next

def packet : Cut A → Option Packet
  | .returned _ => none
  | .accept value _ => some value

private theorem stop_pure (accept cursor : Nat) (value : A) :
    stop accept (pure value) cursor = pure (.returned value) := rfl

private theorem stop_step (accept cursor : Nat) (query : TypedSpec.Domain)
    (next : TypedSpec.Range query → OracleComp TypedSpec A) :
    stop accept (TypedSpec.query query >>= next) cursor =
      (match query with
      | .inr (.accept value) =>
          if cursor = accept then pure (.accept value next)
          else do let reply ← TypedSpec.query (.inr (.accept value)); stop accept (next reply) (cursor+1)
      | query => do let reply ← TypedSpec.query query; stop accept (next reply) cursor) := by
  cases query with
  | inl coin => rfl
  | inr command => cases command <;> rfl

/-- Resuming the selected public query and every original later callback recovers the literal original AST. -/
theorem factor (accept cursor : Nat) (work : OracleComp TypedSpec A) :
    (stop accept work cursor >>= resume) = work := by
  induction work using OracleComp.inductionOn generalizing cursor with
  | pure value => rw [stop_pure,pure_bind]; rfl
  | query_bind query next ih =>
      rw [stop_step]
      cases query with
      | inl coin => simp only [bind_assoc,ih]
      | inr command =>
          cases command
          case accept value =>
            by_cases chosen : cursor = accept
            · simp only [chosen,ite_true,pure_bind,resume]
            · simp only [chosen,ite_false,bind_assoc,ih]
          all_goals simp only [bind_assoc,ih]

abbrev Source := RegistrationNativePlatformIdentityCtxCompiler.Spec
private theorem visit_step (accept cursor : Nat) (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (query : TypedSpec.Domain) (next : TypedSpec.Range query → OracleComp TypedSpec A) (before : S) :
    RegistrationNativeIdentityUnissuedPacketClient.visit accept frontend (TypedSpec.query query >>= next) before cursor =
      (match query with
      | .inr (.accept packet) =>
          if cursor = accept then pure (some packet) else do
            let reached ← (frontend (.inr (.accept packet))).run before
            RegistrationNativeIdentityUnissuedPacketClient.visit accept frontend (next reached.1) reached.2 (cursor + 1)
      | query => do
          let reached ← (frontend query).run before
          RegistrationNativeIdentityUnissuedPacketClient.visit accept frontend (next reached.1) reached.2 cursor) := by
  cases query with
  | inl coin => rfl
  | inr command => cases command <;> rfl


/-- The executable field client's packet is exactly this unmodified complete-source cut, with the same reached callback state. -/
theorem packet_source (accept cursor : Nat) (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (work : OracleComp TypedSpec A) (before : S) :
    RegistrationNativeIdentityUnissuedPacketClient.visit accept frontend work before cursor =
      (fun result => packet result.1) <$> (simulateQ frontend (stop accept work cursor)).run before := by
  induction work using OracleComp.inductionOn generalizing before cursor with
  | pure value => rfl
  | query_bind query next ih =>
      rw [visit_step,stop_step]
      cases query with
      | inl coin =>
          simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
          exact bind_congr (fun reached => ih reached.1 cursor reached.2)
      | inr command =>
          cases command
          case accept value =>
            by_cases chosen : cursor = accept
            · simp only [chosen,ite_true,simulateQ_pure,StateT.run_pure,map_pure,packet]
            · simp only [chosen,ite_false,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
              exact bind_congr (fun reached => ih reached.1 (cursor+1) reached.2)
          all_goals
            simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
            exact bind_congr (fun reached => ih reached.1 cursor reached.2)

/-- Every stateful private source interpretation factors at the same public acceptance, keeping all state and its literal original suffix. -/
theorem execution {m : Type → Type} [Monad m] [LawfulMonad m]
    (accept cursor : Nat) (handler : QueryImpl TypedSpec (StateT S m))
    (work : OracleComp TypedSpec A) (before : S) :
    (simulateQ handler work).run before = (do
      let cut ← (simulateQ handler (stop accept work cursor)).run before
      (simulateQ handler (resume cut.1)).run cut.2) := by
  have law := congrArg (fun code => (simulateQ handler code).run before) (factor accept cursor work)
  simpa only [simulateQ_bind,StateT.run_bind] using law.symm

/-- The public cut preserves every original typed query-class allowance, charging every earlier failed callback and adding no query. -/
theorem query_bound (accept cursor : Nat) (predicate : TypedSpec.Domain → Prop) [DecidablePred predicate]
    (cap : Nat) (work : OracleComp TypedSpec A) (bounded : work.IsQueryBoundP predicate cap) :
    (stop accept work cursor).IsQueryBoundP predicate cap := by
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
          case accept value =>
            by_cases chosen : cursor = accept
            · simp only [chosen,ite_true]
              exact isQueryBoundP_pure predicate _ _
            · simp only [chosen,ite_false]
              exact (isQueryBoundP_query_bind_iff predicate _ _ _).mpr ⟨first,fun reply => ih reply (cursor+1) _ (later reply)⟩
          all_goals exact (isQueryBoundP_query_bind_iff predicate _ _ _).mpr ⟨first,fun reply => ih reply cursor _ (later reply)⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut.factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut.factor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut.packet_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut.packet_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut.execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut.execution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut.query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut.query_bound
