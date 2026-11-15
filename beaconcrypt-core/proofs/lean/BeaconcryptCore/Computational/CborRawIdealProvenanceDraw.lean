-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealProvenanceParameter

/-! Full raw-CBOR World provenance when challenger parameters are drawn at startup and retained in the private backend. Actual parameter and constructor coins, original native ledger, every refusal, and complete World state are included. The pointwise fixed-parameter results are transported by the actual parameter embedding. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.CborRawIdealProvenanceDraw
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (EnvQuery EnvSpec)
open PqxdhDeploymentInterface (Entry Spec FreshBounds Mode ModeSpec)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhDeploymentEnvironmentDraw (withE dropE paramEnv)
open PqxdhDeploymentIdealParams (Target Params drawParams)
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentIdealOrigins (IsFixed QuietEntry aEffects)
open PqxdhRecordLiftOrigins (Origins)
open CborRawPublicState (Public)
open CborRawIdealProvenanceParameter (put drop)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

def Holds (sourceCodec : Codec Reader Response) {count : Nat} (target : Target count)
    (created : PqxdhLiveServerConstruction.Created Unit) (transcript : List Entry)
    (state : Public × EnvState KemSK (Params KemSK count × SplitBk))
    (world : PqxdhRecordLiftWorld.State 2) (origins : Origins 2) : Prop :=
  CborRawIdealProvenanceOutcome.Holds sourceCodec target state.2.backend.1 created transcript (drop state) world origins

section Concrete
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)

/-- Every actual fixed command retains the drawn parameter and all raw/source provenance. -/
theorem fixed (created : PqxdhLiveServerConstruction.Created Unit) (query : Spec.Domain) (ordinary : IsFixed query)
    (transcript : List Entry) (state : Public × EnvState KemSK (Params KemSK count × SplitBk))
    (world : PqxdhRecordLiftWorld.State 2) (origins : Origins 2)
    (holds : Holds (CborRawCompile.sourceCodec wire parse) target created transcript state world origins)
    (result : Spec.Range query × ((Public × EnvState KemSK (Params KemSK count × SplitBk)) ×
      PqxdhRecordLiftOrigins.State 2))
    (supported : result ∈ support ((CborRawIdealProvenanceStep.worldStep setup
      (CborTaggedSimulation.boundaryWire wire parse) (CborRawCompile.route parse)
      (CborRawEnvironment.environment
        (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks target ensureInit
          identityIndex runtime) setup.serverKeyId) query).run (state, (world, origins)))) :
    Holds (CborRawCompile.sourceCodec wire parse) target created transcript result.2.1 result.2.2.1 result.2.2.2 := by
  have reassemble := CborRawIdealProvenanceParameter.put_drop state
  rw [← reassemble, CborRawIdealProvenanceParameter.world_step, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact CborRawIdealProvenanceOutcome.fixed setup wire parse checks target state.2.backend.1 ensureInit identityIndex
    runtime created query ordinary transcript (drop state) world origins holds inner reached

/-- Quiet ledger entries retain the same drawn parameter. -/
theorem quiet (created : PqxdhLiveServerConstruction.Created Unit) (transcript : List Entry)
    (state : Public × EnvState KemSK (Params KemSK count × SplitBk))
    (world : PqxdhRecordLiftWorld.State 2) (origins : Origins 2) (entry : Entry) (ordinary : QuietEntry entry)
    (holds : Holds (CborRawCompile.sourceCodec wire parse) target created transcript state world origins) :
    Holds (CborRawCompile.sourceCodec wire parse) target created (transcript ++ [entry]) state world origins :=
  CborRawIdealProvenanceOutcome.quiet wire parse target state.2.backend.1 created transcript (drop state) world origins
    entry ordinary holds

/-- The actual registration step keeps its parameter while constructing its new canonical shadow and native raw provenance. -/
theorem step (created : PqxdhLiveServerConstruction.Created Unit) (query : EnvQuery) (transcript : List Entry)
    (state : Public × EnvState KemSK (Params KemSK count × SplitBk))
    (world : PqxdhRecordLiftWorld.State 2) (origins : Origins 2)
    (holds : Holds (CborRawCompile.sourceCodec wire parse) target created transcript state world origins)
    (result : (EnvSpec.Range query × (Public × EnvState KemSK (Params KemSK count × SplitBk))) ×
      PqxdhRecordLiftOrigins.State 2)
    (supported : result ∈ support ((simulateQ
      (aEffects setup (CborTaggedSimulation.boundaryWire wire parse) (CborRawCompile.route parse))
      (((CborRawEnvironment.environment
        (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks target ensureInit
          identityIndex runtime) setup.serverKeyId).step query).run state)).run (world, origins))) :
    Holds (CborRawCompile.sourceCodec wire parse) target created
      (transcript ++ [⟨.inl (.inr query.val), result.1.1⟩]) result.1.2 result.2.1 result.2.2 := by
  have reassemble := CborRawIdealProvenanceParameter.put_drop state
  rw [← reassemble, CborRawIdealProvenanceParameter.registration_effects, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact CborRawIdealProvenanceOutcome.step setup wire parse checks target state.2.backend.1 ensureInit identityIndex
    runtime created query transcript (drop state) world origins holds inner reached

/-- The complete drawn-parameter raw adaptive World satisfies the actual native and source provenance invariants. -/
theorem world (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    ∀ result ∈ support (CborRawIdealProvenanceStartup.annotatedRun setup
      (CborTaggedSimulation.boundaryWire wire parse) (CborRawCompile.route parse)
      (CborRawEnvironment.environment
        (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks target ensureInit
          identityIndex runtime) setup.serverKeyId) setup.serverKeyId bounds mode adversary),
      ∀ value, result.1 = some value → ∃ created,
        Holds (CborRawCompile.sourceCodec wire parse) target created value.2.1.2.transcript value.2.2 result.2.1 result.2.2 := by
  apply CborRawIdealProvenanceStartup.world_keeps setup (CborTaggedSimulation.boundaryWire wire parse)
    (CborRawCompile.route parse) _
    (fun transcript state world origins => ∃ created,
      Holds (CborRawCompile.sourceCodec wire parse) target created transcript state world origins)
  · intro query transcript state world origins ordinary holds result reached
    obtain ⟨created, holds⟩ := holds
    exact ⟨created, fixed setup wire parse checks target ensureInit identityIndex runtime created query ordinary transcript
      state world origins holds result reached⟩
  · intro transcript state world origins entry ordinary holds
    obtain ⟨created, holds⟩ := holds
    exact ⟨created, quiet wire parse target created transcript state world origins entry ordinary holds⟩
  · intro query transcript state world origins holds result reached
    obtain ⟨created, holds⟩ := holds
    exact ⟨created, step setup wire parse checks target ensureInit identityIndex runtime created query transcript state world
      origins holds result reached⟩
  · intro created state started world fresh
    rw [CborRawEnvironment.environment, support_map] at started
    obtain ⟨born, supported, same⟩ := started
    cases born with
    | none => cases same
    | some born =>
        rcases born with ⟨made, environment⟩
        cases Option.some.inj same
        change some (made, environment) ∈ support
          (drawParams setup count >>= fun parameters =>
            PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime
              (fun made => (parameters, PqxdhDeploymentIdealSteps.splitInit made))) at supported
        rw [mem_support_bind_iff] at supported
        obtain ⟨parameters, _, constructed⟩ := supported
        have begins := PqxdhDeploymentEnvironment.start_initial setup ensureInit identityIndex runtime
          (fun made => (parameters, PqxdhDeploymentIdealSteps.splitInit made)) made environment constructed
        have initialized := CborRawIdealProvenanceStartup.initialized_start setup ensureInit identityIndex runtime
          (fun made => (parameters, PqxdhDeploymentIdealSteps.splitInit made)) made environment constructed world
        subst begins
        rw [initialized]
        exact ⟨PqxdhDeploymentEnvironment.eraseCreatedMetadata made,
          CborRawIdealProvenanceOutcome.initial wire parse target parameters
            (PqxdhDeploymentEnvironment.eraseCreatedMetadata made) _ world fresh⟩

end Concrete
end BeaconcryptCore.Computational.CborRawIdealProvenanceDraw

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceDraw.fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceDraw.fixed

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceDraw.quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceDraw.quiet

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceDraw.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceDraw.step

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceDraw.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceDraw.world
