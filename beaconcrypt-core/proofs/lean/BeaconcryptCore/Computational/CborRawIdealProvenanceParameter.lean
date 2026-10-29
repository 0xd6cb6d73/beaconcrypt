-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealProvenanceOutcome

/-! A drawn challenger parameter is retained in the private environment backend throughout raw public adaptation. The same single-command effects and full World execution commute with adding that parameter. This is an operational map law, proved from the actual parameterized step. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawIdealProvenanceParameter
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (Environment EnvQuery EnvSpec WorldSpec)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhDeploymentEnvironmentDraw (withE dropE paramStep paramEnv)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealSteps (SplitBk)
open CborRawPublicState (Public)
variable {ι KemSK Reader Response P Bk A : Type} {baseSpec : OracleSpec ι} {n : Nat}

def put (parameters : P) (state : Public × EnvState KemSK Bk) : Public × EnvState KemSK (P × Bk) :=
  (state.1, withE parameters state.2)

def drop (state : Public × EnvState KemSK (P × Bk)) : Public × EnvState KemSK Bk :=
  (state.1, dropE state.2)

theorem drop_put (parameters : P) (state : Public × EnvState KemSK Bk) : drop (put parameters state) = state := rfl

theorem put_drop (state : Public × EnvState KemSK (P × Bk)) : put state.2.backend.1 (drop state) = state := by
  rcases state with ⟨publicState, ⟨native, ⟨parameters, backend⟩, snap, log, created⟩⟩
  rfl

/-- Adding the parameter commutes with the actual raw registration environment step. -/
theorem registration_step (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A) (query : EnvQuery)
    (state : Public × EnvState KemSK SplitBk) :
    ((CborRawEnvironment.environment
      (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks target ensureInit
        identityIndex runtime) setup.serverKeyId).step query).run (put parameters state) =
      Prod.map id (put parameters) <$>
        ((CborRawEnvironment.environment
          (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse) checks target parameters
            ensureInit identityIndex runtime) setup.serverKeyId).step query).run state := by
  rw [show ((CborRawEnvironment.environment _ _).step query).run (put parameters state) = _ from
    CborRawEnvironment.step_run _ query (put parameters state),
    show ((CborRawEnvironment.environment _ _).step query).run state = _ from
      CborRawEnvironment.step_run _ query state]
  simp only [PqxdhDeploymentIdealEnv.envGD, PqxdhDeploymentIdealEnv.envG, paramEnv, paramStep,
    StateT.run, StateT.mk, put, withE, dropE, Functor.map_map]
  rfl

private theorem lift_embedding {E₁ E₂ Result : Type} (work : OracleComp (WorldSpec n) Result)
    (embed : E₁ → E₂) (state : E₁) :
    (StateT.lift work : StateT E₂ (OracleComp (WorldSpec n)) Result).run (embed state) =
      Prod.map id embed <$> (StateT.lift work : StateT E₁ (OracleComp (WorldSpec n)) Result).run state := by
  rw [StateT.run_lift, StateT.run_lift, map_bind]
  simp only [map_pure]
  rfl

/-- Native dispatch transports a pointwise actual registration embedding and otherwise forwards the original World query. -/
theorem native_embedding {E₁ E₂ : Type} (left : Environment n E₁) (right : Environment n E₂)
    (embed : E₁ → E₂)
    (registration : ∀ query state, (right.step query).run (embed state) =
      Prod.map id embed <$> (left.step query).run state)
    (query : Spec.Domain) (state : E₁) :
    (PqxdhRecordLiftInterface.native right query).run (embed state) =
      Prod.map id embed <$> (PqxdhRecordLiftInterface.native left query).run state := by
  have environment : ∀ query state,
      (PqxdhRecordLiftInterface.environmentStep right query).run (embed state) =
        Prod.map id embed <$> (PqxdhRecordLiftInterface.environmentStep left query).run state := by
    intro query state
    change simulateQ PqxdhRecordLiftInterface.effectLift ((right.step query).run (embed state)) =
      Prod.map id embed <$> simulateQ PqxdhRecordLiftInterface.effectLift ((left.step query).run state)
    rw [registration, simulateQ_map]
  rcases query with coin | command
  · exact lift_embedding _ embed state
  · cases command
    all_goals first
      | exact environment _ state
      | exact lift_embedding _ embed state

section Concrete
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)

/-- The whole guarded annotated dispatch step retains the same challenger parameter and complete World. -/
theorem world_step (query : Spec.Domain) (state : Public × EnvState KemSK SplitBk)
    (world : PqxdhRecordLiftOrigins.State 2) :
    (CborRawIdealProvenanceStep.worldStep setup (CborTaggedSimulation.boundaryWire wire parse)
      (CborRawCompile.route parse) (CborRawEnvironment.environment
        (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks target ensureInit
          identityIndex runtime) setup.serverKeyId) query).run (put parameters state, world) =
      (fun result => (result.1, (put parameters result.2.1, result.2.2))) <$>
        (CborRawIdealProvenanceStep.worldStep setup (CborTaggedSimulation.boundaryWire wire parse)
          (CborRawCompile.route parse) (CborRawEnvironment.environment
            (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse) checks target parameters
              ensureInit identityIndex runtime) setup.serverKeyId) query).run (state, world) := by
  rw [CborRawIdealProvenanceStep.worldStep_run, CborRawIdealProvenanceStep.worldStep_run,
    native_embedding _ _ (put parameters) (registration_step setup wire parse checks target parameters ensureInit
      identityIndex runtime), simulateQ_map, StateT.run_map, Functor.map_map, Functor.map_map]
  rfl

/-- The shared annotated registration effects commute with retaining the actual private parameter. -/
theorem registration_effects (query : EnvQuery) (state : Public × EnvState KemSK SplitBk)
    (world : PqxdhRecordLiftOrigins.State 2) :
    (simulateQ (PqxdhDeploymentIdealOrigins.aEffects setup (CborTaggedSimulation.boundaryWire wire parse)
      (CborRawCompile.route parse))
      (((CborRawEnvironment.environment
        (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks target ensureInit
          identityIndex runtime) setup.serverKeyId).step query).run (put parameters state))).run world =
      (fun result => ((result.1.1, put parameters result.1.2), result.2)) <$>
        (simulateQ (PqxdhDeploymentIdealOrigins.aEffects setup (CborTaggedSimulation.boundaryWire wire parse)
          (CborRawCompile.route parse))
          (((CborRawEnvironment.environment
            (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse) checks target parameters
              ensureInit identityIndex runtime) setup.serverKeyId).step query).run state)).run world := by
  rw [registration_step, simulateQ_map, StateT.run_map]
  rfl

end Concrete

end BeaconcryptCore.Computational.CborRawIdealProvenanceParameter

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceParameter.drop_put' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceParameter.drop_put

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceParameter.put_drop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceParameter.put_drop

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceParameter.registration_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceParameter.registration_step

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceParameter.native_embedding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceParameter.native_embedding

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceParameter.world_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceParameter.world_step

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceParameter.registration_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceParameter.registration_effects
