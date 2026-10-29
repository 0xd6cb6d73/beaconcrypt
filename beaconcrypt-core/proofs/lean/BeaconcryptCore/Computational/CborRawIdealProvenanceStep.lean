-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealProvenanceGuard
import BeaconcryptCore.Computational.CborRawGuardedJoin

/-! The guarded provenance step is generic in the registration environment state. All registration effects use the original annotated World; every other command preserves the fixed World view and its origins, including early refusal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawIdealProvenanceStep
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Environment EnvQuery WorldSpec)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealOrigins (IsFixed aEffects)
open PqxdhDeploymentEnvironmentJoin (fixedView)
open PqxdhRecordLiftOrigins (Origins)
open CborRecordWorldCursor (worldShell)
open CborRawGuardedJoin (refusal)
variable {ι KemSK Reader Response E : Type} {baseSpec : OracleSpec ι} {n : Nat}
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

noncomputable def worldStep (env : Environment n E) :
    QueryImpl Spec (StateT (E × PqxdhRecordLiftOrigins.State n) ProbComp) :=
  ((CborRawIdealProvenanceGuard.handler setup codec route).mapStateTBase
    (PqxdhRecordLiftInterface.native env)).flattenStateT

theorem worldStep_run (env : Environment n E) (query : Spec.Domain)
    (state : E × PqxdhRecordLiftOrigins.State n) :
    (worldStep setup codec route env query).run state =
      (fun value => (value.1.1, (value.1.2, value.2))) <$>
        (simulateQ (CborRawIdealProvenanceGuard.handler setup codec route)
          ((PqxdhRecordLiftInterface.native env query).run state.1)).run state.2 := rfl

private theorem lifted_request
    (impl : QueryImpl (WorldSpec n) (StateT (PqxdhRecordLiftOrigins.State n) ProbComp))
    (request : (WorldSpec n).Domain) (e : E) (world : PqxdhRecordLiftOrigins.State n) :
    (simulateQ impl ((StateT.lift (liftM ((WorldSpec n).query request)) :
      StateT E (OracleComp (WorldSpec n)) _).run e)).run world =
      (fun value => ((value.1, e), value.2)) <$> (impl request).run world := by
  rw [StateT.run_lift, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp]

theorem worldStep_reg (env : Environment n E) (query : EnvQuery) (e : E)
    (w : PqxdhRecordLiftOrigins.State n) :
    (worldStep setup codec route env (.inr query.val)).run (e, w) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (PqxdhDeploymentIdealOrigins.aEffects setup codec route) ((env.step query).run e)).run w := by
  rw [worldStep_run]
  rcases query with ⟨command, allowed⟩
  have composed : (CborRawIdealProvenanceGuard.handler setup codec route (n := n)) ∘ₛ PqxdhRecordLiftInterface.effectLift =
      PqxdhDeploymentIdealOrigins.aEffects setup codec route := by
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
theorem worldStep_body (env : Environment n E) (query : Spec.Domain)
    (e : E) (world : PqxdhRecordLiftOrigins.State n) :
    (worldStep setup codec route env query).run (e, world) =
      match refusal (n := n) query (worldShell world.1) with
      | some reply => pure (reply, (e, world))
      | none => (PqxdhDeploymentIdealOrigins.aWorldStep setup codec route env query).run (e, world) := by
  by_cases registration : ∃ command : EnvQuery, query = .inr command.val
  · obtain ⟨command, rfl⟩ := registration
    rw [env_refusal, worldStep_reg, PqxdhDeploymentIdealOrigins.aWorldStep_reg]
  · rw [worldStep_run, PqxdhDeploymentIdealOrigins.aWorldStep_run]
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
        erw [lifted_request (CborRawIdealProvenanceGuard.handler setup codec route)
          (.inr (.inr (.inl (.inl (plaintext, keyId))))) e world,
          lifted_request (PqxdhRecordLiftOrigins.handler setup codec route)
          (.inr (.inr (.inl (.inl (plaintext, keyId))))) e world]
        simp only [Functor.map_map]
        dsimp only [refusal]
        cases refused : CborRecordWorldClient.refusal (n := n)
          (.inr (.inr (.inl (.inl (plaintext, keyId))))) (worldShell world.1) <;>
          simp only [CborRawIdealProvenanceGuard.handler, StateT.run, refused, map_pure]
      case beaconSend owner plaintext =>
        erw [lifted_request (CborRawIdealProvenanceGuard.handler setup codec route)
          (.inr (.inr (.inr (owner, .inl plaintext)))) e world,
          lifted_request (PqxdhRecordLiftOrigins.handler setup codec route)
          (.inr (.inr (.inr (owner, .inl plaintext)))) e world]
        simp only [Functor.map_map]
        dsimp only [refusal]
        cases refused : CborRecordWorldClient.refusal (n := n)
          (.inr (.inr (.inr (owner, .inl plaintext)))) (worldShell world.1) <;>
          simp only [CborRawIdealProvenanceGuard.handler, StateT.run, refused, map_pure]


/-- Fixed steps leave the registration state and provenance unchanged, and preserve every coordinate read by the existing ideal invariant. -/
theorem fixed (env : Environment n E) (query : Spec.Domain) (isFixed : IsFixed query)
    (state : E × PqxdhRecordLiftOrigins.State n)
    (result : Spec.Range query × (E × PqxdhRecordLiftOrigins.State n))
    (supported : result ∈ support ((worldStep setup codec route env query).run state)) :
    result.2.1 = state.1 ∧ result.2.2.2 = state.2.2 ∧
      fixedView result.2.2.1 = fixedView state.2.1 := by
  rcases state with ⟨e, w, o⟩
  rw [worldStep_body] at supported
  cases refused : refusal (n := n) query (worldShell w) with
  | some reply =>
      rw [refused, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨rfl, rfl, rfl⟩
  | none =>
      rw [refused, PqxdhDeploymentIdealOrigins.aWorldStep_fixed setup codec route env query isFixed e w o,
        support_map] at supported
      obtain ⟨plain, reached, rfl⟩ := supported
      obtain ⟨same, view⟩ := PqxdhDeploymentIdealOrigins.worldStep_fixedView setup codec route env query isFixed
        e w plain reached
      exact ⟨same, rfl, view⟩

/-- The environment-effect interpreter is independent of the codec and sender decoder used by record commands. -/
theorem effects_codec {OtherReader OtherResponse : Type} (other : Codec OtherReader OtherResponse)
    (otherRoute : RawCtxServerRouting.SenderDecoder) :
    aEffects setup codec route (n := n) = aEffects setup other otherRoute := by
  funext query
  rfl

end BeaconcryptCore.Computational.CborRawIdealProvenanceStep

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceStep.worldStep_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceStep.worldStep_run

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceStep.worldStep_reg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceStep.worldStep_reg

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceStep.worldStep_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceStep.worldStep_body

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceStep.fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceStep.fixed

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceStep.effects_codec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceStep.effects_codec
