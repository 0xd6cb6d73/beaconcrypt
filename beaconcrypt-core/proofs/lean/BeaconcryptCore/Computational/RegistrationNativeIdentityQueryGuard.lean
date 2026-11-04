-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicRom

/-! Executable public recognition guards stop before the first forbidden oracle input. The same adaptive source event is covered by guarded success or the explicit stop probability; every allowed callback retains its complete reached source state. No security, source-correspondence or event-coverage premise is supplied. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityQueryGuard
variable {I Value State : Type} {spec : OracleSpec I}

/-- Filter a free request tree before submission, using only its actual request value. -/
def cut (allowed : spec.Domain → Bool) (work : OracleComp spec Value) : OracleComp spec (Option Value) :=
  OracleComp.construct (C := fun _ => OracleComp spec (Option Value))
    (fun value => pure (some value))
    (fun query _next continued => if allowed query then (do
      let reply ← spec.query query
      continued reply) else pure none) work

private theorem cut_pure (allowed : spec.Domain → Bool) (value : Value) :
    cut allowed (pure value) = pure (some value) := rfl

private theorem cut_query_bind (allowed : spec.Domain → Bool) (query : spec.Domain)
    (next : spec.Range query → OracleComp spec Value) :
    cut allowed (spec.query query >>= next) = if allowed query then (do
      let reply ← spec.query query
      cut allowed (next reply)) else pure none := rfl

/-- Recognition prevents submission on every program branch, not merely on a final winning event. -/
theorem submitted (allowed : spec.Domain → Bool) (work : OracleComp spec Value) :
    AllQueriesSatisfy (cut allowed work) (fun query => allowed query = true) := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [cut_pure]; trivial
  | query_bind query next ih =>
    rw [cut_query_bind]
    cases admitted : allowed query with
    | false => simp only [Bool.false_eq_true, ite_false]; trivial
    | true =>
      simp only [ite_true]
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨admitted, ih⟩

/-- For any source event, the loss from public recognition is precisely exposed as the probability of a stopped guard. All allowed draws and complete final state remain the original ones. -/
theorem cover (handler : QueryImpl spec (StateT State ProbComp)) (allowed : spec.Domain → Bool)
    (work : OracleComp spec Value) (event : Value × State → Prop) (before : State) :
    Pr{let result ← (simulateQ handler work).run before}[event result] ≤
      Pr{let result ← (simulateQ handler (cut allowed work)).run before}[
        match result.1 with | none => True | some value => event (value, result.2)] := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [cut_pure, simulateQ_pure, StateT.run_pure]; exact le_rfl
  | query_bind query next ih =>
    rw [cut_query_bind]
    cases admitted : allowed query with
    | false =>
      simp only [Bool.false_eq_true, ite_false, simulateQ_pure, StateT.run_pure, prEvent_pure, ite_true]
      exact prEvent_le_one _
    | true =>
      simp only [ite_true, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact prEvent_bind_mono_of_forall_le _ _ _ _ _ (fun result => ih result.1 result.2)

variable {D R : Type} [DecidableEq D]
open RegistrationNativeIdentitySymbolicRom (PhysicalSpec SymbolicSpec address project cached)

/-- A symbolic token is internal; every public address is checked using the executable recognizer. -/
def publicAllowed (recognize : D → Bool) : Option D → Bool
  | none => true
  | some input => !recognize input

omit [DecidableEq D] in
private theorem no_hidden (recognize : D → Bool) (hidden : D) (recognized : recognize hidden = true)
    (work : OracleComp (SymbolicSpec D R) Value) :
    AllQueriesSatisfy (cut (publicAllowed recognize) work) (fun query => query ≠ some hidden) := by
  apply (submitted (publicAllowed recognize) work).mono
  intro query permitted same
  rw [same] at permitted
  simp only [publicAllowed, recognized, Bool.not_true, Bool.false_eq_true] at permitted

/-- The recognition guard discharges the symbolic source theorem's forbidden-public-address condition structurally. The executable guard never receives the hidden address. -/
theorem source (sampler : ProbComp R) (recognize : D → Bool) (hidden : D) (recognized : recognize hidden = true)
    (work : OracleComp (SymbolicSpec D R) Value) (cache : (SymbolicSpec D R).QueryCache) :
    Prod.map id (project hidden) <$> (simulateQ (cached sampler) (cut (publicAllowed recognize) work)).run cache =
      (simulateQ (fun query => cached sampler (address hidden query)) (cut (publicAllowed recognize) work)).run (project hidden cache) :=
  RegistrationNativeIdentitySymbolicRom.program_source sampler hidden _ (no_hidden recognize hidden recognized work) cache

/-- The physical source event is covered by the same event in the executable symbolic guarded run or a recognized public input. Only the private realization mentions the hidden address. -/
theorem source_cover (sampler : ProbComp R) (recognize : D → Bool) (hidden : D) (recognized : recognize hidden = true)
    (work : OracleComp (SymbolicSpec D R) Value) (event : Value × (PhysicalSpec D R).QueryCache → Prop)
    (cache : (SymbolicSpec D R).QueryCache) :
    Pr{let result ← (simulateQ (fun query => cached sampler (address hidden query)) work).run (project hidden cache)}[event result] ≤
      Pr{let result ← (simulateQ (cached sampler) (cut (publicAllowed recognize) work)).run cache}[
        match result.1 with | none => True | some value => event (value, project hidden result.2)] := by
  have upper := cover (fun query => cached sampler (address hidden query)) (publicAllowed recognize)
    work event (project hidden cache)
  rw [← source sampler recognize hidden recognized work cache] at upper
  simpa only [prEvent_map, Prod.map, id_eq] using upper

/-- The recognition loss is a separate literal probability, charged once; the successful symbolic event retains its full realized source cache. -/
theorem source_loss (sampler : ProbComp R) (recognize : D → Bool) (hidden : D) (recognized : recognize hidden = true)
    (work : OracleComp (SymbolicSpec D R) Value) (event : Value × (PhysicalSpec D R).QueryCache → Prop)
    (cache : (SymbolicSpec D R).QueryCache) :
    Pr{let result ← (simulateQ (fun query => cached sampler (address hidden query)) work).run (project hidden cache)}[event result] ≤
      Pr{let result ← (simulateQ (cached sampler) (cut (publicAllowed recognize) work)).run cache}[result.1 = none] +
      Pr{let result ← (simulateQ (cached sampler) (cut (publicAllowed recognize) work)).run cache}[
        ∃ value, result.1 = some value ∧ event (value, project hidden result.2)] := by
  apply (source_cover sampler recognize hidden recognized work event cache).trans
  apply (prEvent_mono_of_support _ _ _ ?_).trans (prEvent_or_le _ _ _)
  rintro ⟨value, current⟩ _ held
  cases value with
  | none => exact Or.inl rfl
  | some value => exact Or.inr ⟨value, rfl, held⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentityQueryGuard
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityQueryGuard.submitted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityQueryGuard.submitted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityQueryGuard.cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityQueryGuard.cover
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityQueryGuard.source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityQueryGuard.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityQueryGuard.source_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityQueryGuard.source_cover
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityQueryGuard.source_loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityQueryGuard.source_loss
