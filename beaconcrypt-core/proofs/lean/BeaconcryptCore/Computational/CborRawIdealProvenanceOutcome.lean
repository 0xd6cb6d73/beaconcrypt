-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealProvenanceStartup
import BeaconcryptCore.Computational.CborRawIdealBeaconShadow

/-! Concrete full adaptive raw World provenance at fixed challenger parameters. Every local registration rule and startup condition is discharged from the actual ideal handler. The original raw ledger, all refusal paths, populated public pins, full private World and a constructed source-response shadow are retained. This legacy source14 instance derives its legacy AD restriction internally. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.CborRawIdealProvenanceOutcome
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (Environment EnvQuery EnvSpec)
open PqxdhDeploymentInterface (Entry Spec FreshBounds Mode ModeSpec)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhDeploymentEnvironmentJoin (Good initialized uncount)
open PqxdhDeploymentIdealOrigins (IsFixed QuietEntry aEffects)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentIdealProvenance (Prov)
open CborRawIdealBeaconShadow (Shadow)
open PqxdhRecordLiftOrigins (Origins)
open CborRawPublicState (Public)
open CborRawIdealProvenanceStep (worldStep)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

structure Holds (sourceCodec : Codec Reader Response) {count : Nat} (target : Target count)
    (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (transcript : List Entry) (state : Public × EnvState KemSK SplitBk)
    (world : PqxdhRecordLiftWorld.State 2) (origins : Origins 2) : Prop where
  good : Good created state.2 world
  inv : PqxdhDeploymentIdealEnv.IdealInv target state.2 world
  prov : Prov target transcript state.2 world origins
  shadow : Shadow sourceCodec target parameters transcript state.2 world origins

section Concrete
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)

/-- Every fixed command, including a refused send, preserves all concrete native and source provenance. -/
theorem fixed (created : PqxdhLiveServerConstruction.Created Unit) (query : Spec.Domain) (isFixed : IsFixed query)
    (transcript : List Entry) (state : Public × EnvState KemSK SplitBk)
    (world : PqxdhRecordLiftWorld.State 2) (origins : Origins 2)
    (holds : Holds (CborRawCompile.sourceCodec wire parse) target parameters created transcript state world origins)
    (result : Spec.Range query × ((Public × EnvState KemSK SplitBk) × PqxdhRecordLiftOrigins.State 2))
    (supported : result ∈ support ((worldStep setup (CborTaggedSimulation.boundaryWire wire parse)
      (CborRawCompile.route parse) (CborRawEnvironment.environment
        (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse) checks target parameters
          ensureInit identityIndex runtime) setup.serverKeyId) query).run (state, (world, origins)))) :
    Holds (CborRawCompile.sourceCodec wire parse) target parameters created transcript result.2.1 result.2.2.1
      result.2.2.2 := by
  obtain ⟨good, inv⟩ := CborRawIdealProvenanceWorld.fixed_keeps setup (CborTaggedSimulation.boundaryWire wire parse)
    (CborRawCompile.route parse) _ setup.serverKeyId _ created (PqxdhDeploymentIdealEnv.IdealInv target)
    (PqxdhDeploymentIdealEnv.idealInv_stable target)
    (PqxdhDeploymentIdealEnv.ideal_splits setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
      checks target parameters created) query isFixed state world origins holds.good holds.inv result supported
  obtain ⟨same, sameO, view⟩ := CborRawIdealProvenanceStep.fixed setup (CborTaggedSimulation.boundaryWire wire parse)
    (CborRawCompile.route parse) _ query isFixed (state, (world, origins)) result supported
  refine ⟨good, inv, ?_, ?_⟩
  · rw [same, sameO]
    exact PqxdhDeploymentIdealProvenance.prov_view target transcript state.2 world result.2.2.1 origins view holds.prov
  · rw [same, sameO]
    exact CborRawIdealBeaconShadow.view _ target parameters transcript state.2 world result.2.2.1 origins view holds.shadow

/-- Appending an actual nonregistration ledger entry changes neither private state nor the constructed shadow's provenance. -/
theorem quiet (created : PqxdhLiveServerConstruction.Created Unit) (transcript : List Entry)
    (state : Public × EnvState KemSK SplitBk) (world : PqxdhRecordLiftWorld.State 2) (origins : Origins 2)
    (entry : Entry) (ordinary : QuietEntry entry)
    (holds : Holds (CborRawCompile.sourceCodec wire parse) target parameters created transcript state world origins) :
    Holds (CborRawCompile.sourceCodec wire parse) target parameters created (transcript ++ [entry]) state world origins :=
  ⟨holds.good, holds.inv, PqxdhDeploymentIdealProvenance.prov_quiet target transcript state.2 world origins entry
    ordinary holds.prov, CborRawIdealBeaconShadow.quiet _ target parameters transcript state.2 world origins entry
      ordinary holds.shadow⟩

/-- Actual raw registration preserves admissibility and constructs the next raw/source provenance pair. -/
theorem step (created : PqxdhLiveServerConstruction.Created Unit) (query : EnvQuery) (transcript : List Entry)
    (state : Public × EnvState KemSK SplitBk) (world : PqxdhRecordLiftWorld.State 2) (origins : Origins 2)
    (holds : Holds (CborRawCompile.sourceCodec wire parse) target parameters created transcript state world origins)
    (result : (EnvSpec.Range query × (Public × EnvState KemSK SplitBk)) × PqxdhRecordLiftOrigins.State 2)
    (supported : result ∈ support ((simulateQ
      (aEffects setup (CborTaggedSimulation.boundaryWire wire parse) (CborRawCompile.route parse))
      ((CborRawEnvironment.step (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse)
        checks target parameters ensureInit identityIndex runtime) query).run state)).run (world, origins))) :
    Holds (CborRawCompile.sourceCodec wire parse) target parameters created
      (transcript ++ [⟨.inl (.inr query.val), result.1.1⟩]) result.1.2 result.2.1 result.2.2 := by
  obtain ⟨good, inv⟩ := CborRawIdealProvenanceWorld.registration_keeps setup
    (CborTaggedSimulation.boundaryWire wire parse) (CborRawCompile.route parse) _ _ created
    (PqxdhDeploymentIdealEnv.IdealInv target)
    (PqxdhDeploymentIdealEnv.ideal_splits setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
      checks target parameters created) query state world origins holds.good holds.inv result supported
  exact ⟨good, inv, CborRawIdealProvenance.step_prov setup wire parse checks target parameters ensureInit
    identityIndex runtime created query transcript state world origins holds.good holds.inv holds.prov result supported,
    CborRawIdealBeaconShadow.step setup wire parse checks target parameters ensureInit identityIndex runtime created
      query transcript state world origins holds.good holds.inv holds.shadow result supported⟩

/-- The actual initialized Server and the source's empty shadow establish every invariant after all startup coins. -/
theorem initial (created : PqxdhLiveServerConstruction.Created Unit) (publicState : Public)
    (world : PqxdhRecordLiftWorld.State 2) (fresh : uncount world = uncount PqxdhRecordLiftWorld.initial) :
    Holds (CborRawCompile.sourceCodec wire parse) target parameters created []
      (publicState, PqxdhDeploymentEnvironment.envInitial created (PqxdhDeploymentIdealSteps.splitInit created))
      (initialized created world) PqxdhRecordLiftOrigins.empty := by
  have view := PqxdhDeploymentEnvironmentJoin.initialized_view created world fresh
  exact ⟨PqxdhDeploymentEnvironmentJoin.good_initial created _ world fresh,
    PqxdhDeploymentIdealEnv.idealInv_stable target _ _ _ view (PqxdhDeploymentIdealEnv.idealInv_start target created),
    PqxdhDeploymentIdealProvenance.prov_view target [] _ _ _ _ view
      (PqxdhDeploymentIdealProvenance.prov_initial target created),
    CborRawIdealBeaconShadow.view _ target parameters [] _ _ _ _ view
      (CborRawIdealBeaconShadow.initial _ target parameters created)⟩

/-- Complete adaptive raw World outcomes satisfy the concrete provenance invariant after actual Server-construction startup. -/
theorem world (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    ∀ result ∈ support (CborRawIdealProvenanceStartup.annotatedRun setup
      (CborTaggedSimulation.boundaryWire wire parse) (CborRawCompile.route parse)
      (CborRawEnvironment.environment
        (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse) checks target parameters
          ensureInit identityIndex runtime) setup.serverKeyId) setup.serverKeyId bounds mode adversary),
      ∀ value, result.1 = some value → ∃ created,
        Holds (CborRawCompile.sourceCodec wire parse) target parameters created value.2.1.2.transcript value.2.2
          result.2.1 result.2.2 := by
  apply CborRawIdealProvenanceStartup.world_keeps setup (CborTaggedSimulation.boundaryWire wire parse)
    (CborRawCompile.route parse) _
    (fun transcript state world origins => ∃ created,
      Holds (CborRawCompile.sourceCodec wire parse) target parameters created transcript state world origins)
  · intro query transcript state world origins ordinary holds result reached
    obtain ⟨created, holds⟩ := holds
    exact ⟨created, fixed setup wire parse checks target parameters ensureInit identityIndex runtime created query
      ordinary transcript state world origins holds result reached⟩
  · intro transcript state world origins entry ordinary holds
    obtain ⟨created, holds⟩ := holds
    exact ⟨created, quiet wire parse target parameters created transcript state world origins entry ordinary holds⟩
  · intro query transcript state world origins holds result reached
    obtain ⟨created, holds⟩ := holds
    exact ⟨created, step setup wire parse checks target parameters ensureInit identityIndex runtime created query
      transcript state world origins holds result reached⟩
  · intro created state started world fresh
    rw [CborRawEnvironment.environment, support_map] at started
    obtain ⟨born, supported, same⟩ := started
    cases born with
    | none => cases same
    | some born =>
        rcases born with ⟨made, environment⟩
        cases Option.some.inj same
        have begins := PqxdhDeploymentEnvironment.start_initial setup ensureInit identityIndex runtime
          PqxdhDeploymentIdealSteps.splitInit made environment supported
        have initialized := CborRawIdealProvenanceStartup.initialized_start setup ensureInit identityIndex runtime
          PqxdhDeploymentIdealSteps.splitInit made environment supported world
        subst begins
        rw [initialized]
        exact ⟨PqxdhDeploymentEnvironment.eraseCreatedMetadata made,
          initial wire parse target parameters (PqxdhDeploymentEnvironment.eraseCreatedMetadata made) _ world fresh⟩

end Concrete
end BeaconcryptCore.Computational.CborRawIdealProvenanceOutcome

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceOutcome.fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceOutcome.fixed

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceOutcome.quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceOutcome.quiet

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceOutcome.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceOutcome.step

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceOutcome.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceOutcome.initial

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceOutcome.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceOutcome.world
