-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealProvenanceParameter
import BeaconcryptCore.Computational.CborRawIdealKeymatchWorld

/-! The actual retained challenger parameter commutes with arbitrary adaptive native programs before World interpretation. This follows from the proved single-command parameter embedding, and retains the complete public adapter and private World outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawIdealKeymatchStartupEmbedding
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealSteps (SplitBk)
open CborRawPublicState (Public)
open CborRawIdealProvenanceParameter (put)
variable {ι KemSK Reader Response A Result : Type} {baseSpec : OracleSpec ι}

/-- A proved single-query state embedding extends through every reply-dependent continuation. -/
theorem simulate_embed {κ targetIndex S₁ S₂ Value : Type} {source : OracleSpec κ} {target : OracleSpec targetIndex}
    (left : QueryImpl source (StateT S₁ (OracleComp target)))
    (right : QueryImpl source (StateT S₂ (OracleComp target))) (embed : S₁ → S₂)
    (step : ∀ query state, (right query).run (embed state) = Prod.map id embed <$> (left query).run state)
    (work : OracleComp source Value) (state : S₁) :
    (simulateQ right work).run (embed state) = Prod.map id embed <$> (simulateQ left work).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]; rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, step, bind_map_left, map_bind]
      exact bind_congr fun value => ih value.1 value.2

section Concrete
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)

/-- The actual EnvGD native dispatch is the actual fixed-parameter dispatch with its parameter retained. -/
theorem native_program (work : OracleComp Spec Result) (state : Public × EnvState KemSK SplitBk) :
    (simulateQ (PqxdhRecordLiftInterface.native (CborRawEnvironment.environment
      (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks target ensureInit
        identityIndex runtime) setup.serverKeyId)) work).run (put parameters state) =
      Prod.map id (put parameters) <$>
        (simulateQ (PqxdhRecordLiftInterface.native (CborRawEnvironment.environment
          (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse) checks target parameters ensureInit
            identityIndex runtime) setup.serverKeyId)) work).run state := by
  exact simulate_embed _ _ (put parameters)
    (fun query initial => CborRawIdealProvenanceParameter.native_embedding _ _ (put parameters)
      (CborRawIdealProvenanceParameter.registration_step setup wire parse checks target parameters ensureInit
        identityIndex runtime) query initial) work state

/-- Actual raw cursor execution commutes with retaining the same parameter, including its full World state. -/
theorem world_program (work : OracleComp Spec Result) (state : Public × EnvState KemSK SplitBk)
    (world : PqxdhRecordLiftWorld.State 2) :
    (simulateQ (PqxdhRecordLiftWorld.handler setup (CborTaggedSimulation.boundaryWire wire parse)
      (CborRawCompile.route parse))
      (CborRecordWorldClient.client ((simulateQ (PqxdhRecordLiftInterface.native (CborRawEnvironment.environment
        (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks target ensureInit
          identityIndex runtime) setup.serverKeyId)) work).run (put parameters state))
        (CborRecordWorldCursor.worldShell world))).run world =
      (fun value => ((value.1.1, put parameters value.1.2), value.2)) <$>
        (simulateQ (PqxdhRecordLiftWorld.handler setup (CborTaggedSimulation.boundaryWire wire parse)
          (CborRawCompile.route parse))
          (CborRecordWorldClient.client ((simulateQ (PqxdhRecordLiftInterface.native (CborRawEnvironment.environment
            (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse) checks target parameters ensureInit
              identityIndex runtime) setup.serverKeyId)) work).run state)
            (CborRecordWorldCursor.worldShell world))).run world := by
  rw [native_program, CborRawEnvironmentRun.cursor_map, simulateQ_map, StateT.run_map]
  rfl

end Concrete
end BeaconcryptCore.Computational.CborRawIdealKeymatchStartupEmbedding

/-- info: 'BeaconcryptCore.Computational.CborRawIdealKeymatchStartupEmbedding.simulate_embed' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealKeymatchStartupEmbedding.simulate_embed
/-- info: 'BeaconcryptCore.Computational.CborRawIdealKeymatchStartupEmbedding.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealKeymatchStartupEmbedding.native_program
/-- info: 'BeaconcryptCore.Computational.CborRawIdealKeymatchStartupEmbedding.world_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealKeymatchStartupEmbedding.world_program
