-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealKeymatchStartupEmbedding

/-! After actual counted startup and Server initialization, the complete EnvGD annotated raw program has key facts at its retained challenger parameter. The proof erases only the origin annotation, uses the concrete parameter embedding and applies the actual fresh-World fixed-parameter receipt. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawIdealKeymatchStartupRest
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec FullSpec FreshBounds)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentEnvironment (EnvState)
open CborRawPublicState (Public)
open CborRawIdealProvenanceParameter (put)
variable {ι KemSK Reader Response A Result : Type} {baseSpec : OracleSpec ι}

abbrev Env (KemSK : Type) (count : Nat) := Public × EnvState KemSK (Params KemSK count × SplitBk)
abbrev Output (KemSK Result : Type) (count : Nat) := ((Result × Ledger) × Env KemSK count) × PqxdhRecordLiftOrigins.State 2

section Rest
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (created : PqxdhLiveServerConstruction.Created Unit) (startupWorld : PqxdhRecordLiftWorld.State 2)

noncomputable def annotatedRest (bounds : FreshBounds) (work : OracleComp FullSpec Result) (publicState : Public) :
    ProbComp (Output KemSK Result count) :=
  (simulateQ (CborRawIdealProvenanceGuard.handler setup (CborTaggedSimulation.boundaryWire wire parse)
      (CborRawCompile.route parse))
    ((simulateQ (PqxdhRecordLiftInterface.native (CborRawEnvironment.environment
      (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks target ensureInit
        identityIndex runtime) setup.serverKeyId))
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
        setup.serverKeyId bounds work)).run
        (put parameters (publicState, PqxdhDeploymentEnvironment.envInitial created
          (PqxdhDeploymentIdealSteps.splitInit created))))).run
            (PqxdhDeploymentEnvironmentJoin.initialized created startupWorld, PqxdhRecordLiftOrigins.empty)

/-- Actual counted startup, full adaptive ledger and complete private parameter state yield native raw key facts. -/
theorem rest_keyFacts
    (fresh : PqxdhDeploymentEnvironmentJoin.uncount startupWorld =
      PqxdhDeploymentEnvironmentJoin.uncount (PqxdhRecordLiftWorld.initial (n := 2)))
    (bounds : FreshBounds) (work : OracleComp FullSpec Result) (publicState : Public)
    (result : Output KemSK Result count)
    (supported : result ∈ support (annotatedRest setup wire parse checks target parameters ensureInit identityIndex
      runtime created startupWorld bounds work publicState)) :
    PqxdhDeploymentIdealTrace.KeyFacts setup (CborTaggedSimulation.boundaryWire wire parse) checks target
      result.1.2.2.backend.1 result.1.1.2.transcript result.1.2.2.backend.2.2.2 := by
  have erased : (result.1, result.2.1) ∈ support (Prod.map id Prod.fst <$>
      annotatedRest setup wire parse checks target parameters ensureInit identityIndex runtime created startupWorld
        bounds work publicState) := by
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  rw [annotatedRest, CborRawIdealProvenanceGuard.client_erase,
    CborRawIdealKeymatchStartupEmbedding.world_program setup wire parse checks target parameters ensureInit
      identityIndex runtime, support_map] at erased
  obtain ⟨plain, reached, same⟩ := erased
  have member : plain ∈ support (CborRawIdealKeymatchWorld.fixedWorld_from setup wire parse checks target parameters created
      ensureInit identityIndex runtime startupWorld bounds work publicState) := reached
  have facts := CborRawIdealKeymatchWorld.fixed_keyFacts_from setup wire parse checks target parameters created ensureInit
    identityIndex runtime startupWorld fresh bounds work publicState plain member
  have state := congrArg Prod.fst same
  rw [← state]
  exact facts

end Rest
end BeaconcryptCore.Computational.CborRawIdealKeymatchStartupRest

/-- info: 'BeaconcryptCore.Computational.CborRawIdealKeymatchStartupRest.rest_keyFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealKeymatchStartupRest.rest_keyFacts
