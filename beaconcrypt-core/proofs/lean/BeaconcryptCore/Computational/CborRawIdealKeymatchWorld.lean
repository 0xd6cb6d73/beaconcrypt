-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealKeymatchRun
import BeaconcryptCore.Computational.CborRawWorldCoreHandoff

/-! Actual fixed-parameter raw record-world executions inherit key facts from the proved native raw ledger invariant. The operational client retains the original secrecy wrapper above the public registration adapter and native admission filter; the support transfer keeps the complete ideal registration core. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawIdealKeymatchWorld
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec FullSpec FreshBounds)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentEnvironment (EnvState)
open CborRawPublicState (Public)
variable {ι KemSK Reader Response A Result : Type} {baseSpec : OracleSpec ι}

abbrev Output (KemSK Result : Type) :=
  ((Result × Ledger) × (Public × EnvState KemSK SplitBk)) × PqxdhRecordLiftWorld.State 2

section World
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

/-- The actual raw World client, with unchanged secret draws and the original native wire transcript. -/
noncomputable def fixedWorld (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (bounds : FreshBounds) (work : OracleComp FullSpec Result) (publicState : Public) : ProbComp (Output KemSK Result) :=
  (simulateQ (PqxdhRecordLiftWorld.handler setup (CborTaggedSimulation.boundaryWire wire parse)
      (CborRawCompile.route parse))
    (CborRecordWorldClient.client ((simulateQ (PqxdhRecordLiftInterface.native
      (CborRawEnvironment.environment (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse)
        checks target parameters ensureInit identityIndex runtime) setup.serverKeyId))
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
        setup.serverKeyId bounds work)).run
        (publicState, PqxdhDeploymentEnvironment.envInitial created (PqxdhDeploymentIdealSteps.splitInit created)))
      (CborRecordWorldCursor.worldShell (PqxdhDeploymentEnvironmentJoin.initialized created
        (PqxdhRecordLiftWorld.initial (n := 2)))))).run
          (PqxdhDeploymentEnvironmentJoin.initialized created (PqxdhRecordLiftWorld.initial (n := 2)))

/-- Every actual raw fixed-parameter World outcome satisfies the native-wire selected-accept and published-bundle key facts. -/
theorem fixed_keyFacts (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (bounds : FreshBounds) (work : OracleComp FullSpec Result) (publicState : Public) (output : Output KemSK Result)
    (supported : output ∈ support (fixedWorld setup wire parse checks target parameters created ensureInit identityIndex
      runtime bounds work publicState)) :
    PqxdhDeploymentIdealTrace.KeyFacts setup (CborTaggedSimulation.boundaryWire wire parse) checks target parameters
      output.1.1.2.transcript output.1.2.2.backend.2.2 := by
  let project := fun value : Output KemSK Result =>
    (value.1.1, value.1.2.1, value.2.produced, value.1.2.2.backend.2.2)
  have projected : project output ∈ support (project <$>
      fixedWorld setup wire parse checks target parameters created ensureInit identityIndex runtime bounds work
        publicState) := by
    rw [support_map]
    exact ⟨output, supported, rfl⟩
  have joined := CborRawWorldCoreHandoff.native_world setup wire parse checks target parameters created ensureInit
    identityIndex runtime (PqxdhDeploymentSecrecy.wrap setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
      setup.serverKeyId bounds work) publicState
  change project output ∈ support ((fun value : Output KemSK Result => (value.1.1, value.1.2.1, value.2.produced,
      value.1.2.2.backend.2.2)) <$> _) at projected
  rw [fixedWorld] at projected
  rw [← PqxdhDeploymentIdealFrame.lawEq_support joined, support_map] at projected
  obtain ⟨native, member, same⟩ := projected
  have trace := CborRawIdealKeymatchRun.run_trace setup wire parse checks target parameters created bounds work publicState
    native member
  have ledger : native.1.2 = output.1.1.2 := congrArg (fun value => value.1.2) same
  have core : native.2.2.backend.2.2 = output.1.2.2.backend.2.2 :=
    congrArg (fun value => value.2.2.2) same
  have sourceFacts : PqxdhDeploymentIdealTrace.KeyFacts setup (CborRawCompile.sourceCodec wire parse) checks target
      parameters output.1.1.2.transcript output.1.2.2.backend.2.2 := by
    rw [← ledger, ← core]
    exact ⟨trace.selected, trace.bundles⟩
  exact ⟨sourceFacts.selected, sourceFacts.bundles⟩

/-- The full raw World client starts after actual counted startup effects. -/
noncomputable def fixedWorld_from (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (startupWorld : PqxdhRecordLiftWorld.State 2)
    (bounds : FreshBounds) (work : OracleComp FullSpec Result) (publicState : Public) : ProbComp (Output KemSK Result) :=
  (simulateQ (PqxdhRecordLiftWorld.handler setup (CborTaggedSimulation.boundaryWire wire parse)
      (CborRawCompile.route parse))
    (CborRecordWorldClient.client ((simulateQ (PqxdhRecordLiftInterface.native
      (CborRawEnvironment.environment (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse)
        checks target parameters ensureInit identityIndex runtime) setup.serverKeyId))
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
        setup.serverKeyId bounds work)).run
        (publicState, PqxdhDeploymentEnvironment.envInitial created (PqxdhDeploymentIdealSteps.splitInit created)))
      (CborRecordWorldCursor.worldShell (PqxdhDeploymentEnvironmentJoin.initialized created
        startupWorld)))).run
          (PqxdhDeploymentEnvironmentJoin.initialized created startupWorld)

/-- Every actual raw fixed-parameter World outcome satisfies the native-wire selected-accept and published-bundle key facts. -/
theorem fixed_keyFacts_from (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (startupWorld : PqxdhRecordLiftWorld.State 2)
    (fresh : PqxdhDeploymentEnvironmentJoin.uncount startupWorld =
      PqxdhDeploymentEnvironmentJoin.uncount (PqxdhRecordLiftWorld.initial (n := 2)))
    (bounds : FreshBounds) (work : OracleComp FullSpec Result) (publicState : Public) (output : Output KemSK Result)
    (supported : output ∈ support (fixedWorld_from setup wire parse checks target parameters created ensureInit identityIndex
      runtime startupWorld bounds work publicState)) :
    PqxdhDeploymentIdealTrace.KeyFacts setup (CborTaggedSimulation.boundaryWire wire parse) checks target parameters
      output.1.1.2.transcript output.1.2.2.backend.2.2 := by
  let project := fun value : Output KemSK Result =>
    (value.1.1, value.1.2.1, value.2.produced, value.1.2.2.backend.2.2)
  have projected : project output ∈ support (project <$>
      fixedWorld_from setup wire parse checks target parameters created ensureInit identityIndex runtime startupWorld bounds work
        publicState) := by
    rw [support_map]
    exact ⟨output, supported, rfl⟩
  have joined := CborRawWorldCoreHandoff.native_world_from setup wire parse checks target parameters created ensureInit
    identityIndex runtime startupWorld fresh (PqxdhDeploymentSecrecy.wrap setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
      setup.serverKeyId bounds work) publicState
  change project output ∈ support ((fun value : Output KemSK Result => (value.1.1, value.1.2.1, value.2.produced,
      value.1.2.2.backend.2.2)) <$> _) at projected
  rw [fixedWorld_from] at projected
  rw [← PqxdhDeploymentIdealFrame.lawEq_support joined, support_map] at projected
  obtain ⟨native, member, same⟩ := projected
  have trace := CborRawIdealKeymatchRun.run_trace setup wire parse checks target parameters created bounds work publicState
    native member
  have ledger : native.1.2 = output.1.1.2 := congrArg (fun value => value.1.2) same
  have core : native.2.2.backend.2.2 = output.1.2.2.backend.2.2 :=
    congrArg (fun value => value.2.2.2) same
  have sourceFacts : PqxdhDeploymentIdealTrace.KeyFacts setup (CborRawCompile.sourceCodec wire parse) checks target
      parameters output.1.1.2.transcript output.1.2.2.backend.2.2 := by
    rw [← ledger, ← core]
    exact ⟨trace.selected, trace.bundles⟩
  exact ⟨sourceFacts.selected, sourceFacts.bundles⟩


end World
end BeaconcryptCore.Computational.CborRawIdealKeymatchWorld

/-- info: 'BeaconcryptCore.Computational.CborRawIdealKeymatchWorld.fixed_keyFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealKeymatchWorld.fixed_keyFacts

/-- info: 'BeaconcryptCore.Computational.CborRawIdealKeymatchWorld.fixed_keyFacts_from' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealKeymatchWorld.fixed_keyFacts_from
