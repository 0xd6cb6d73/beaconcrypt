-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile
import BeaconcryptCore.Computational.RegistrationNativeIdentityNoReveal

/-! Structural query safety for the whole ordinary joint-service native client rejects exactly generated-identity reveal requests. Source coin sampling, reports and ordinary native work remain unrestricted. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore
open RegistrationNativeIdentityMain (State M)
variable {n : Nat} {KemSK Value Result : Type} {mlSource : RegistrationNativeMldsa.Source}

def DynamicAllowed : PqxdhDynamicIdentityPool.DynamicSpec.Domain → Prop
  | .inr (.reveal _) => False
  | _ => True

def Allowed : PqxdhJointPhase1Reports.ProtocolSpec.Domain → Prop
  | .inl query => DynamicAllowed query
  | .inr _ => True

def Safe (work : M n KemSK mlSource Value) : Prop :=
  ∀ before, AllQueriesSatisfy (work.run before) Allowed

/-- Computing a source reply from an already safe program adds no identity reveal request. -/
theorem mapped {I A B : Type} {spec : OracleSpec I} (work : OracleComp spec A) (change : A → B)
    (predicate : I → Prop) (safe : AllQueriesSatisfy work predicate) :
    AllQueriesSatisfy (change <$> work) predicate := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind safe (fun _ => allQueriesSatisfy_pure _ _)

/-- Literal native coins remain ordinary uniform requests in the protocol-facing joint client. -/
theorem coins_safe (work : ProbComp Value) :
    AllQueriesSatisfy (simulateQ RegistrationNativeIdentityMain.coins work) Allowed := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityMain.coins]
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

/-- Compiler-local randomness adds only ordinary joint-game uniform queries. -/
theorem dynamic_coins_safe (work : ProbComp Value) :
    AllQueriesSatisfy (simulateQ RegistrationNativeIdentityCompiler.coins work) DynamicAllowed := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityCompiler.coins]
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

/-- Embedding an ordinary non-revealing joint program preserves its complete allowed query trace. -/
theorem dynamic_safe (work : OracleComp PqxdhDynamicIdentityPool.DynamicSpec Value)
    (safe : AllQueriesSatisfy work DynamicAllowed) :
    AllQueriesSatisfy (simulateQ RegistrationNativeIdentityMain.dynamicLift work) Allowed := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
      simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityMain.dynamicLift]
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨first, fun reply => ih reply (later reply)⟩

/-- Pure native replies execute no joint request. -/
theorem pure_safe (value : Value) : Safe (pure value : M n KemSK mlSource Value) := by
  intro before
  simp only [StateT.run_pure]
  trivial

/-- All actual executable continuations retain the structural non-reveal property. -/
theorem bind_safe (work : M n KemSK mlSource Value) (next : Value → M n KemSK mlSource Result)
    (first : Safe work) (later : ∀ value, Safe (next value)) : Safe (work >>= next) := by
  intro before
  rw [StateT.run_bind]
  exact allQueriesSatisfy_bind (first before) (fun result => later result.1 result.2)

/-- Actual state lookup executes no generated-identity operation. -/
theorem get_safe : Safe (get : M n KemSK mlSource (State n KemSK mlSource)) := by
  intro before
  simp only [StateT.run_get]
  trivial

/-- Local control and parsed-counter updates execute no generated-identity operation. -/
theorem modify_safe (change : State n KemSK mlSource → State n KemSK mlSource) :
    Safe (modify change : M n KemSK mlSource Unit) := by
  intro before
  simp only [StateT.run_modify]
  trivial

/-- Any ordinary native SDK or World computation forwards only its original uniform randomness. -/
theorem ordinary_safe (work : StateT (RegistrationNativeIdentityWorld.Context n KemSK) ProbComp Value) :
    Safe (RegistrationNativeIdentityMain.ordinary work : M n KemSK mlSource Value) := by
  intro before
  exact mapped _ _ Allowed (coins_safe (work.run before.context))

/-- Every alias report remains an ordinary candidate report and cannot reveal an identity. -/
theorem emit_safe (reports : List PqxdhJointPhase1Reports.CandidateReport) :
    AllQueriesSatisfy (RegistrationNativeIdentityMain.emit reports) Allowed := by
  induction reports with
  | nil => trivial
  | cons report rest ih =>
      simp only [RegistrationNativeIdentityMain.emit]
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, fun _ => ih⟩

/-- Reporting every current public-key alias leaves structural non-reveal safety unchanged. -/
theorem report_safe (packet : beaconcrypt_core.registration.InitPacket) :
    Safe (RegistrationNativeIdentityMain.report packet : M n KemSK mlSource Unit) := by
  unfold RegistrationNativeIdentityMain.report
  apply bind_safe _ _ get_safe
  intro before current
  simp only [StateT.run_lift, bind_pure_comp]
  exact mapped _ _ Allowed (emit_safe _)

end BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.mapped' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.mapped
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.coins_safe' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.coins_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.dynamic_coins_safe' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.dynamic_coins_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.dynamic_safe' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.dynamic_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.pure_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.pure_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.bind_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.bind_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.get_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.get_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.modify_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.modify_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.ordinary_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.ordinary_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.emit_safe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.emit_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.report_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore.report_safe
