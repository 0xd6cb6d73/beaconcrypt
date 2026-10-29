-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRecordWorldMerge
import BeaconcryptCore.Computational.CborRawEnvironmentJoin

/-! Native size refusal is below the unchanged CE program, including its secret draws and analysis ledger. The generic environment split is reused with independent registration and record codecs. Actual World/native cursor equality supplies every admission decision; no cursor or game-simulation obligation is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawGuardedJoin
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Environment EnvQuery EnvEffects WorldSpec)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhDeploymentEnvironmentJoin (Good Splits Stable)
open PqxdhDeploymentBackend (RegImpl XState handlerWith)
open CborRecordWorldCursor (worldShell)
open CborRecordNativeAdmission (nativeShell)
open LazyOracleDiscard (LawEq)
variable {ι KemSK Reader Response Bk : Type} {baseSpec : OracleSpec ι} {n : Nat}

/-- Only established send requests may be refused; raw receive and all registration effects retain their original interpreter. -/
def refusal (query : Spec.Domain) (shell : CborRecordWorldClient.Shell) : Option (Spec.Range query) :=
  match query with
  | .inr (.serverSend keyId plaintext) =>
      CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inl (.inl (plaintext, keyId))))) shell
  | .inr (.beaconSend owner plaintext) =>
      CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inr (owner, .inl plaintext)))) shell
  | _ => none

section Join
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

noncomputable def worldStep (env : Environment n (EnvState KemSK Bk)) :
    QueryImpl Spec (StateT (EnvState KemSK Bk × PqxdhRecordLiftWorld.State n) ProbComp) :=
  ((CborRecordWorldSimulation.guarded setup codec route).mapStateTBase
    (PqxdhRecordLiftInterface.native env)).flattenStateT

noncomputable def nativeHandler (reg : RegImpl KemSK Bk n) : QueryImpl Spec (StateT (XState KemSK Bk n) ProbComp) :=
  fun query state => match refusal (n := n) query (nativeShell state.base) with
  | some reply => pure (reply, state)
  | none => (handlerWith setup codec route reg query).run state

/-- Registration and hash effects of the guarded interpreter are the actual unchanged shared effects. -/
theorem guarded_effects : (CborRecordWorldSimulation.guarded setup codec route (n := n)) ∘ₛ
    PqxdhRecordLiftInterface.effectLift = PqxdhRecordLiftWorld.effects := by
  funext query
  simp only [QueryImpl.apply_compose, PqxdhRecordLiftInterface.effectLift, simulateQ_spec_query]
  rfl

private theorem ordinary_effects : (PqxdhRecordLiftWorld.handler setup codec route (n := n)) ∘ₛ
    PqxdhRecordLiftInterface.effectLift = PqxdhRecordLiftWorld.effects := by
  funext query
  simp only [QueryImpl.apply_compose, PqxdhRecordLiftInterface.effectLift, simulateQ_spec_query]
  rfl

theorem worldStep_run (env : Environment n (EnvState KemSK Bk)) (query : Spec.Domain)
    (state : EnvState KemSK Bk × PqxdhRecordLiftWorld.State n) :
    (worldStep setup codec route env query).run state =
      (fun value => (value.1.1, (value.1.2, value.2))) <$>
        (simulateQ (CborRecordWorldSimulation.guarded setup codec route)
          ((PqxdhRecordLiftInterface.native env query).run state.1)).run state.2 := rfl

private theorem lifted_request {E : Type}
    (impl : QueryImpl (WorldSpec n) (StateT (PqxdhRecordLiftWorld.State n) ProbComp))
    (request : (WorldSpec n).Domain) (e : E) (world : PqxdhRecordLiftWorld.State n) :
    (simulateQ impl ((StateT.lift (liftM ((WorldSpec n).query request)) :
      StateT E (OracleComp (WorldSpec n)) _).run e)).run world =
      (fun value => ((value.1, e), value.2)) <$> (impl request).run world := by
  rw [StateT.run_lift, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp]

private theorem worldStep_reg (env : Environment n (EnvState KemSK Bk)) (query : EnvQuery) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) :
    (worldStep setup codec route env (.inr query.val)).run (e, w) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ PqxdhRecordLiftWorld.effects ((env.step query).run e)).run w := by
  rw [worldStep_run]
  rcases query with ⟨command, allowed⟩
  have composed : (CborRecordWorldSimulation.guarded setup codec route (n := n)) ∘ₛ PqxdhRecordLiftInterface.effectLift =
      PqxdhRecordLiftWorld.effects := by
    funext request
    simp only [QueryImpl.apply_compose, PqxdhRecordLiftInterface.effectLift, simulateQ_spec_query]
    rfl
  cases command
  all_goals first
    | exact absurd allowed id
    | (simp only [PqxdhRecordLiftInterface.native, PqxdhRecordLiftInterface.environmentStep, StateT.run]
       rw [← QueryImpl.simulateQ_compose, composed]
       rfl)

private theorem env_refusal (query : EnvQuery) (shell : CborRecordWorldClient.Shell) :
    refusal (n := n) (.inr query.val) shell = none := by
  rcases query with ⟨command, valid⟩
  cases command <;> first | rfl | exact absurd valid id

set_option backward.isDefEq.respectTransparency false in
/-- Guarding a CE step either refuses that one send with a full-state stutter, or executes the original concrete joint step. -/
theorem worldStep_body (env : Environment n (EnvState KemSK Bk)) (query : Spec.Domain)
    (e : EnvState KemSK Bk) (world : PqxdhRecordLiftWorld.State n) :
    (worldStep setup codec route env query).run (e, world) =
      match refusal (n := n) query (worldShell world) with
      | some reply => pure (reply, (e, world))
      | none => (PqxdhDeploymentEnvironmentJoin.worldStep setup codec route env query).run (e, world) := by
  by_cases registration : ∃ command : EnvQuery, query = .inr command.val
  · obtain ⟨command, rfl⟩ := registration
    rw [env_refusal, worldStep_reg, PqxdhDeploymentEnvironmentJoin.worldStep_reg]
  · rw [worldStep_run, PqxdhDeploymentEnvironmentJoin.worldStep_run]
    rcases query with coin | command
    · simp only [PqxdhRecordLiftInterface.native, StateT.run_lift, bind_pure_comp]
      rfl
    · cases command
      case create pin keyId => exact (registration ⟨⟨.create pin keyId, trivial⟩, rfl⟩).elim
      case bundle owner => exact (registration ⟨⟨.bundle owner, trivial⟩, rfl⟩).elim
      case accept raw => exact (registration ⟨⟨.accept raw, trivial⟩, rfl⟩).elim
      case build session payload => exact (registration ⟨⟨.build session payload, trivial⟩, rfl⟩).elim
      case finish owner raw => exact (registration ⟨⟨.finish owner raw, trivial⟩, rfl⟩).elim
      case hmac key message => exact (registration ⟨⟨.hmac key message, trivial⟩, rfl⟩).elim
      case hash bytes =>
        simp only [PqxdhRecordLiftInterface.native, StateT.run_lift, bind_pure_comp]
        rfl
      case serverRaw raw =>
        simp only [PqxdhRecordLiftInterface.native, StateT.run_lift, bind_pure_comp]
        rfl
      case beaconRaw owner raw =>
        simp only [PqxdhRecordLiftInterface.native, StateT.run_lift, bind_pure_comp]
        rfl
      case serverSend keyId plaintext =>
        erw [lifted_request (CborRecordWorldSimulation.guarded setup codec route)
          (.inr (.inr (.inl (.inl (plaintext, keyId))))) e world,
          lifted_request (PqxdhRecordLiftWorld.handler setup codec route)
          (.inr (.inr (.inl (.inl (plaintext, keyId))))) e world]
        simp only [Functor.map_map]
        dsimp only [refusal]
        cases refused : CborRecordWorldClient.refusal (n := n)
          (.inr (.inr (.inl (.inl (plaintext, keyId))))) (worldShell world) <;>
          simp only [CborRecordWorldSimulation.guarded, StateT.run, refused, map_pure]
      case beaconSend owner plaintext =>
        erw [lifted_request (CborRecordWorldSimulation.guarded setup codec route)
          (.inr (.inr (.inr (owner, .inl plaintext)))) e world,
          lifted_request (PqxdhRecordLiftWorld.handler setup codec route)
          (.inr (.inr (.inr (owner, .inl plaintext)))) e world]
        simp only [Functor.map_map]
        dsimp only [refusal]
        cases refused : CborRecordWorldClient.refusal (n := n)
          (.inr (.inr (.inr (owner, .inl plaintext)))) (worldShell world) <;>
          simp only [CborRecordWorldSimulation.guarded, StateT.run, refused, map_pure]

/-- The guarded joint step has the law of native early admission on the complete reassembly. -/
theorem step_law (env : Environment n (EnvState KemSK Bk)) (reg : RegImpl KemSK Bk n)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (inv : EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop) (splits : Splits created reg env.step inv)
    (query : Spec.Domain) (e : EnvState KemSK Bk) (world : PqxdhRecordLiftWorld.State n)
    (good : Good created e world) (holds : inv e world) :
    LawEq (Prod.map id (fun state => PqxdhDeploymentEnvironmentJoin.merge state.1 state.2) <$>
        (worldStep setup codec route env query).run (e, world))
      ((nativeHandler setup codec route reg query).run (PqxdhDeploymentEnvironmentJoin.merge e world)) := by
  rw [worldStep_body]
  simp only [nativeHandler, StateT.run, CborRecordWorldMerge.merge_shell created e world good]
  cases refused : refusal (n := n) query (worldShell world) with
  | some value => simp only [map_pure]; exact LawEq.refl _
  | none => exact PqxdhDeploymentEnvironmentJoin.worldStep_step setup codec route env reg created inv splits query e world good holds

/-- Refusal preserves admissibility and the environment's stable invariant without invoking a callback. -/
theorem step_keeps (env : Environment n (EnvState KemSK Bk)) (reg : RegImpl KemSK Bk n)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (inv : EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop) (stable : Stable inv)
    (splits : Splits created reg env.step inv)
    (query : Spec.Domain) (e : EnvState KemSK Bk) (world : PqxdhRecordLiftWorld.State n)
    (good : Good created e world) (holds : inv e world)
    (value : Spec.Range query × (EnvState KemSK Bk × PqxdhRecordLiftWorld.State n))
    (supported : value ∈ support ((worldStep setup codec route env query).run (e, world))) :
    Good created value.2.1 value.2.2 ∧ inv value.2.1 value.2.2 := by
  rw [worldStep_body] at supported
  cases refused : refusal (n := n) query (worldShell world) with
  | some reply =>
      rw [refused, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨good, holds⟩
  | none =>
      rw [refused] at supported
      exact PqxdhDeploymentEnvironmentJoin.worldStep_keeps setup codec route env reg created inv stable splits query
        e world good holds value supported

/-- Every adaptive CE program, including secret sampling and ledger code already inside it, has the same complete native execution through the actual public cursor filter. -/
theorem run_join {Result : Type} (env : Environment n (EnvState KemSK Bk)) (reg : RegImpl KemSK Bk n)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (inv : EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop) (stable : Stable inv)
    (splits : Splits created reg env.step inv) (work : OracleComp Spec Result)
    (e : EnvState KemSK Bk) (world : PqxdhRecordLiftWorld.State n)
    (good : Good created e world) (holds : inv e world) :
    LawEq ((fun value => (value.1.1, PqxdhDeploymentEnvironmentJoin.merge value.1.2 value.2)) <$>
        (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
          (CborRecordWorldClient.client ((simulateQ (PqxdhRecordLiftInterface.native env) work).run e)
            (worldShell world))).run world)
      ((simulateQ (nativeHandler setup codec route reg) work).run
        (PqxdhDeploymentEnvironmentJoin.merge e world)) := by
  rw [CborRecordWorldSimulation.client_simulation,
    OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  exact PqxdhDeploymentSeedSplit.lawEq_run_simulateQ_of_proj (worldStep setup codec route env)
    (nativeHandler setup codec route reg) (fun state => Good created state.1 state.2 ∧ inv state.1 state.2)
    (fun state => PqxdhDeploymentEnvironmentJoin.merge state.1 state.2)
    (fun query state both => step_law setup codec route env reg created inv splits query state.1 state.2 both.1 both.2)
    (fun query state both => step_keeps setup codec route env reg created inv stable splits query state.1 state.2 both.1 both.2)
    work (e, world) ⟨good, holds⟩

end Join
end BeaconcryptCore.Computational.CborRawGuardedJoin

/-- info: 'BeaconcryptCore.Computational.CborRawGuardedJoin.guarded_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawGuardedJoin.guarded_effects
/-- info: 'BeaconcryptCore.Computational.CborRawGuardedJoin.worldStep_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawGuardedJoin.worldStep_run
/-- info: 'BeaconcryptCore.Computational.CborRawGuardedJoin.worldStep_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawGuardedJoin.worldStep_body
/-- info: 'BeaconcryptCore.Computational.CborRawGuardedJoin.step_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawGuardedJoin.step_law
/-- info: 'BeaconcryptCore.Computational.CborRawGuardedJoin.step_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawGuardedJoin.step_keeps
/-- info: 'BeaconcryptCore.Computational.CborRawGuardedJoin.run_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawGuardedJoin.run_join
