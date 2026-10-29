-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealKeymatchStartupEmbedding
import BeaconcryptCore.Computational.CborRawHeadlineStartup

/-! The actual raw ideal World program factored into its challenger draws, exact source Server constructor and fixed-parameter continuation. All draws remain World coin requests. The only removed source constructor fields are its unused installed private pool and runtime result; the native environment retains its actual constructor and private state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawIdealWorldProgram
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentIdealParams (Target Params drawParams)
open PqxdhRecordLiftInterface (WorldSpec coinLift)
open CborRawPublicState (Public)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentInterface (Spec Mode ModeSpec FreshBounds)
variable {ι KemSK Reader Response A Result X : Type} {baseSpec : OracleSpec ι}
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (ensureInit : StateT A ProbComp Bool) (runtime : A)

abbrev Output (KemSK Result : Type) (count : Nat) :=
  Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Result ×
    (Public × EnvState KemSK (Params KemSK count × SplitBk)))

noncomputable def after (parameters : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (work : OracleComp Spec Result) :
    OracleComp (WorldSpec 2) (Output KemSK Result count) := do
  let _ ← (WorldSpec 2).query (.inl created)
  let result ← (simulateQ (PqxdhRecordLiftInterface.native (CborRawEnvironment.environment
    (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse) checks target parameters ensureInit 0
      runtime) setup.serverKeyId)) work).run
      (⟨PqxdhDeploymentCompile.Log.empty, setup.serverKeyId⟩,
        PqxdhDeploymentEnvironment.envInitial created (PqxdhDeploymentIdealSteps.splitInit created))
  pure (some (PqxdhRegistrationJointServerBirth.encode created, result.1,
    CborRawIdealProvenanceParameter.put parameters result.2))

noncomputable def fixedClient (parameters : Params KemSK count) (work : OracleComp Spec Result) :
    OracleComp (WorldSpec 2) (Output KemSK Result count) := do
  let born ← simulateQ coinLift
    ((PqxdhRegistrationJointServerBirth.source (KemSK := KemSK) setup.joint ensureInit setup.serverKeyId none).run
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))
  match born.1 with
  | none => pure none
  | some created => after setup wire parse checks target ensureInit runtime parameters created work

noncomputable def client (work : OracleComp Spec Result) : OracleComp (WorldSpec 2) (Output KemSK Result count) := do
  let parameters ← simulateQ coinLift (drawParams setup count)
  fixedClient setup wire parse checks target ensureInit runtime parameters work

/-- The factorization is an exact open-program equality before any record World is interpreted. -/
theorem program (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    PqxdhRecordLiftInterface.program
      (CborRawEnvironment.environment
        (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks target ensureInit 0 runtime)
        setup.serverKeyId) setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds
        mode adversary =
      client setup wire parse checks target ensureInit runtime
        (PqxdhDeploymentSecrecy.wrap setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
          setup.serverKeyId bounds (PqxdhDeploymentInterface.asModeO mode adversary)) := by
  let environment := CborRawEnvironment.environment
    (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks target ensureInit 0 runtime)
    setup.serverKeyId
  have startup : environment.start = drawParams setup count >>= fun parameters =>
      (fun result => result.1.map fun created =>
        (created, CborRawIdealProvenanceParameter.put parameters
          ((⟨PqxdhDeploymentCompile.Log.empty, setup.serverKeyId⟩ : Public),
            PqxdhDeploymentEnvironment.envInitial created (PqxdhDeploymentIdealSteps.splitInit created)))) <$>
        (PqxdhLiveServerConstruction.construct setup.joint ensureInit 0 setup.serverKeyId none).run runtime := by
    simp only [environment, CborRawEnvironment.environment, PqxdhDeploymentIdealEnv.envGD,
      PqxdhDeploymentEnvironmentDraw.paramEnv, PqxdhDeploymentEnvironment.start, map_bind, Functor.map_map, Option.map_map]
    rfl
  change PqxdhRecordLiftInterface.program environment setup.source.crypto
    (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds mode adversary = _
  rw [PqxdhRecordLiftInterface.program, startup, client, simulateQ_bind, bind_assoc]
  apply bind_congr
  intro parameters
  simp only [simulateQ_map, bind_map_left, fixedClient, PqxdhRegistrationJointServerBirth.source,
    StateT.run, PqxdhDynamicIdentityPool.initialState, List.length_nil]
  apply bind_congr
  intro constructed
  cases constructed with
  | mk answer runtime' =>
      cases answer with
      | none => rfl
      | some created =>
          simp only [Option.map_some, after]
          have nativeEq := CborRawIdealKeymatchStartupEmbedding.native_program setup wire parse checks target
            parameters ensureInit 0 runtime
            (PqxdhDeploymentSecrecy.wrap setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
              setup.serverKeyId bounds (PqxdhDeploymentInterface.asModeO mode adversary))
            ((⟨PqxdhDeploymentCompile.Log.empty, setup.serverKeyId⟩ : Public),
              PqxdhDeploymentEnvironment.envInitial created (PqxdhDeploymentIdealSteps.splitInit created))
          dsimp only [StateT.run] at nativeEq
          dsimp only [environment]
          rw [nativeEq]
          simp only [bind_map_left]
          rfl

end BeaconcryptCore.Computational.CborRawIdealWorldProgram

/-- info: 'BeaconcryptCore.Computational.CborRawIdealWorldProgram.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealWorldProgram.program
