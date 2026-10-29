-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealBeaconTrace
import BeaconcryptCore.Computational.CborRawIdealProvenanceStep

/-! The canonical shadow is an existential history of the actual delegated calls, not a supplied game simulation. Existing registration and Beacon provenance are retained on that history while every original raw ledger entry remains in the observed transcript. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawIdealBeaconShadow
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Entry)
open PqxdhRecordLiftInterface (EnvQuery EnvSpec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhDeploymentEnvironmentJoin (Good)
open PqxdhDeploymentIdealProvenance (Prov)
open PqxdhDeploymentIdealBeacon (BeaconProv)
open PqxdhDeploymentIdealOrigins (aEffects QuietEntry)
open PqxdhRecordLiftOrigins (Origins)
open CborRawPublicState (Public)
open CborRawIdealBeaconTrace (Related)
variable {ι KemSK Reader Response A : Type} {baseSpec : OracleSpec ι}

structure Shadow (codec : Codec Reader Response) {count : Nat} (target : Target count)
    (parameters : Params KemSK count) (raw : List Entry) (state : EnvState KemSK SplitBk)
    (world : PqxdhRecordLiftWorld.State 2) (origins : Origins 2) : Prop where
  history : ∃ canonical, Related raw canonical ∧ Prov target canonical state world origins ∧
    BeaconProv codec target parameters canonical state

theorem initial (codec : Codec Reader Response) {count : Nat} (target : Target count)
    (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit) :
    Shadow codec target parameters []
      (PqxdhDeploymentEnvironment.envInitial created (PqxdhDeploymentIdealSteps.splitInit created))
      (PqxdhDeploymentEnvironmentJoin.initialized created (PqxdhRecordLiftWorld.initial (n := 2)))
      PqxdhRecordLiftOrigins.empty := by
  exact ⟨[], .nil, PqxdhDeploymentIdealProvenance.prov_initial target created,
    PqxdhDeploymentIdealBeacon.beacon_initial codec target parameters created⟩

theorem view (codec : Codec Reader Response) {count : Nat} (target : Target count)
    (parameters : Params KemSK count) (raw : List Entry) (state : EnvState KemSK SplitBk)
    (world world' : PqxdhRecordLiftWorld.State 2) (origins : Origins 2)
    (same : PqxdhDeploymentEnvironmentJoin.fixedView world' = PqxdhDeploymentEnvironmentJoin.fixedView world)
    (holds : Shadow codec target parameters raw state world origins) :
    Shadow codec target parameters raw state world' origins := by
  obtain ⟨canonical, related, prov, beacon⟩ := holds.history
  exact ⟨canonical, related, PqxdhDeploymentIdealProvenance.prov_view target canonical state world world' origins same
    prov, beacon⟩

theorem quiet (codec : Codec Reader Response) {count : Nat} (target : Target count)
    (parameters : Params KemSK count) (raw : List Entry) (state : EnvState KemSK SplitBk)
    (world : PqxdhRecordLiftWorld.State 2) (origins : Origins 2) (entry : Entry) (notRegistration : QuietEntry entry)
    (holds : Shadow codec target parameters raw state world origins) :
    Shadow codec target parameters (raw ++ [entry]) state world origins := by
  obtain ⟨canonical, related, prov, beacon⟩ := holds.history
  refine ⟨canonical ++ [entry], CborRawIdealBeaconTrace.append raw canonical related entry entry (.same entry ?_),
    PqxdhDeploymentIdealProvenance.prov_quiet target canonical state world origins entry notRegistration prov,
    PqxdhDeploymentIdealBeacon.beacon_quiet codec target parameters canonical state entry notRegistration beacon⟩
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · rfl
  · cases command with
    | build session payload => exact False.elim (notRegistration ⟨.build session payload, trivial⟩ reply rfl)
    | finish owner bytes => exact False.elim (notRegistration ⟨.finish owner bytes, trivial⟩ reply rfl)
    | _ => rfl
  · rfl

private theorem step_effects (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) {E : Type} (env : PqxdhRecordLiftInterface.Environment 2 E)
    (query : EnvQuery) (state : Public × E) (world : PqxdhRecordLiftOrigins.State 2) :
    (simulateQ (aEffects setup codec route) ((CborRawEnvironment.step env query).run state)).run world =
      (fun value => ((CborRawEnvironment.reply state.1 query value.1.1,
        (CborRawEnvironment.next state.1 query value.1.1, value.1.2)), value.2)) <$>
        (simulateQ (aEffects setup codec route)
          ((env.step (CborRawEnvironment.request state.1 query)).run state.2)).run world := by
  simp only [CborRawEnvironment.step_run, simulateQ_map, StateT.run_map]

/-- The actual wrapped ideal registration step constructs the next canonical shadow and preserves both original provenance invariants. -/
theorem step (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : EnvQuery) (raw : List Entry)
    (state : Public × EnvState KemSK SplitBk) (world : PqxdhRecordLiftWorld.State 2) (origins : Origins 2)
    (good : Good created state.2 world) (inv : PqxdhDeploymentIdealEnv.IdealInv target state.2 world)
    (holds : Shadow (CborRawCompile.sourceCodec wire parse) target parameters raw state.2 world origins)
    (result : (EnvSpec.Range query × (Public × EnvState KemSK SplitBk)) × PqxdhRecordLiftOrigins.State 2)
    (supported : result ∈ support ((simulateQ
      (aEffects setup (CborTaggedSimulation.boundaryWire wire parse) (CborRawCompile.route parse))
      ((CborRawEnvironment.step (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse)
        checks target parameters ensureInit identityIndex runtime) query).run state)).run (world, origins))) :
    Shadow (CborRawCompile.sourceCodec wire parse) target parameters
      (raw ++ [⟨.inl (.inr query.val), result.1.1⟩]) result.1.2.2 result.2.1 result.2.2 := by
  obtain ⟨canonical, related, prov, beacon⟩ := holds.history
  rw [step_effects, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  rw [CborRawIdealProvenanceStep.effects_codec setup (CborTaggedSimulation.boundaryWire wire parse)
    (CborRawCompile.route parse) (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)] at reached
  refine ⟨canonical ++ [⟨.inl (.inr (CborRawEnvironment.request state.1 query).val), inner.1.1⟩],
    CborRawIdealBeaconTrace.append raw canonical related _ _
      (CborRawIdealBeaconTrace.entry_relation state.1 query inner.1.1), ?_, ?_⟩
  · exact PqxdhDeploymentIdealProvenance.ideal_rStep setup (CborRawCompile.sourceCodec wire parse)
      (CborRawCompile.route parse) checks target parameters created (CborRawEnvironment.request state.1 query)
      canonical state.2 world origins good inv prov inner reached
  · exact PqxdhDeploymentIdealBeacon.beacon_rStep setup (CborRawCompile.sourceCodec wire parse)
      (CborRawCompile.route parse) checks target parameters created (CborRawEnvironment.request state.1 query)
      canonical state.2 world origins good inv prov beacon inner reached

end BeaconcryptCore.Computational.CborRawIdealBeaconShadow

/-- info: 'BeaconcryptCore.Computational.CborRawIdealBeaconShadow.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealBeaconShadow.initial
/-- info: 'BeaconcryptCore.Computational.CborRawIdealBeaconShadow.view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealBeaconShadow.view
/-- info: 'BeaconcryptCore.Computational.CborRawIdealBeaconShadow.quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealBeaconShadow.quiet
/-- info: 'BeaconcryptCore.Computational.CborRawIdealBeaconShadow.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealBeaconShadow.step
