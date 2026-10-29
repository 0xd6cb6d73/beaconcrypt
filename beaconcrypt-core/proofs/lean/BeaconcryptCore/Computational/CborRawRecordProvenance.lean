-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealSlotsWorld
import BeaconcryptCore.Computational.CborRawRecordLiftCrypto
import BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain

/-! The real compiled raw client's handle-to-slot map is the origin map of the actual complete raw World. This retains the full permitted record view, original ledger, produced frames and raw-attempt counters while placing the cursor below the ledger. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordProvenance
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (Environment)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
open PqxdhRecordLiftIdeal (chainView)
open PqxdhRecordLiftLaterWorlds (chainsOf)
open PqxdhDeploymentIdealHandoff (annotatedView)
open CborRawRecordLiftBounds (client)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- The real raw record view is exactly the provenance-annotated actual raw World view. -/
theorem real_view (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    chainView <$> chainsOf (fun _ => false) setup codec route
      (client env setup.source.crypto codec serverKid bounds mode adversary) =
      annotatedView <$> CborRawIdealProvenanceStartup.annotatedRun setup codec route env serverKid bounds mode adversary := by
  have factor := PqxdhRecordLiftProtocol.schedule_factor (PqxdhRecordLiftWorldCompiler.realPolicy setup codec)
    setup codec route (client env setup.source.crypto codec serverKid bounds mode adversary)
    PqxdhRecordLiftWorldCompiler.initial
  change PqxdhRecordLiftProtocol.execute _ _ _ _ _ PqxdhRecordLiftProtocol.initialControl
    PqxdhRecordLiftProtocol.initialPrivate = _ at factor
  change chainView <$> PqxdhRecordLiftProtocol.execute _ _ _ _ _ _ _ = _
  rw [PqxdhRecordLiftMixedWorld.policy_real, factor, Functor.map_map]
  have projected := PqxdhDeploymentIdealHandoff.schedule_project setup codec route
    (client env setup.source.crypto codec serverKid bounds mode adversary) PqxdhRecordLiftWorldCompiler.initial
    (PqxdhRecordLiftWorldCompiler.initial_good setup.source)
  have cursor := CborRawIdealProvenanceGuard.client_simulation setup codec route
    (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary)
    (PqxdhRecordLiftOrigins.initial : PqxdhRecordLiftOrigins.State n)
  rw [CborRawIdealProvenanceStartup.annotatedRun, ← cursor]
  change _ = annotatedView <$>
    (simulateQ (PqxdhRecordLiftOrigins.handler setup codec route)
      (client env setup.source.crypto codec serverKid bounds mode adversary)).run PqxdhRecordLiftOrigins.initial
  change Prod.map id PqxdhRecordLiftWorldCompiler.project <$>
    (simulateQ (PqxdhRecordLiftWorldCompiler.handler (PqxdhRecordLiftWorldCompiler.realPolicy setup codec)
      setup codec route) (client env setup.source.crypto codec serverKid bounds mode adversary)).run
        PqxdhRecordLiftWorldCompiler.initial =
    (simulateQ (PqxdhRecordLiftOrigins.handler setup codec route)
      (client env setup.source.crypto codec serverKid bounds mode adversary)).run PqxdhRecordLiftOrigins.initial at projected
  rw [← projected, Functor.map_map]
  congr 1
  funext result
  exact PqxdhDeploymentIdealHandoff.chainView_split result

/-- Every complete permitted real raw record view is reached by the actual provenance-annotated raw World. -/
theorem real_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (result : PqxdhRecordLiftProtocol.RunResult n E X)
    (reached : result ∈ support (chainsOf (fun _ => false) setup codec route
      (client env setup.source.crypto codec serverKid bounds mode adversary))) :
    ∃ annotated ∈ support (CborRawIdealProvenanceStartup.annotatedRun setup codec route env serverKid bounds mode adversary),
      chainView result = annotatedView annotated := by
  have viewed : chainView result ∈ support (chainView <$> chainsOf (fun _ => false) setup codec route
      (client env setup.source.crypto codec serverKid bounds mode adversary)) := by
    rw [support_map]
    exact ⟨result, reached, rfl⟩
  rw [real_view, support_map] at viewed
  obtain ⟨annotated, member, same⟩ := viewed
  exact ⟨annotated, member, same.symm⟩

/-- The concrete slot conditions and native early-finish alternative hold on every real raw compiled record view. -/
theorem real_slots_or_anomaly {A : Type} (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborTaggedSimulation.boundaryWire wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    {count : Nat} (target : PqxdhDeploymentIdealParams.Target count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : Nat) (runtime : A) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X)
    (result : PqxdhRecordLiftProtocol.RunResult 2
      (CborRawPublicState.Public × PqxdhDeploymentEnvironment.EnvState KemSK
        (PqxdhDeploymentIdealParams.Params KemSK count × PqxdhDeploymentIdealSteps.SplitBk)) X)
    (reached : result ∈ support (chainsOf (fun _ => false) setup (CborTaggedSimulation.boundaryWire wire parse)
      (CborRawCompile.route parse) (client (CborRawEnvironment.environment
        (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks target ensureInit identityIndex
          runtime) setup.serverKeyId) setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId
            bounds mode adversary))) :
    ∀ value, (chainView result).result = some value →
      PqxdhDeploymentIdealTrace.IdealSlots setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
        setup.serverKeyId target (chainView result).slots value.2.1.transcript ∨
      PqxdhDeploymentIdealTrace.Anomaly setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
        setup.serverKeyId target value.2.1.transcript := by
  intro value found
  obtain ⟨annotated, member, same⟩ := real_support setup (CborTaggedSimulation.boundaryWire wire parse)
    (CborRawCompile.route parse) _ setup.serverKeyId bounds mode adversary result reached
  rw [same] at found ⊢
  rcases annotated with ⟨_ | inner, state⟩
  · exact absurd found (by simp [annotatedView])
  · simp only [annotatedView, Option.map_some, Option.some.injEq] at found
    subst found
    have slots := CborRawIdealSlotsWorld.slots_or_anomaly setup wire parse checks phase1 phase2 target ensureInit
      identityIndex runtime bounds mode adversary _ member inner rfl
    rw [← PqxdhDeploymentIdealHandoff.originMap_two] at slots
    exact slots

/-- Every actual real raw record view has the three Server slot conditions, including native rejection branches. -/
theorem real_server_slots {A : Type} (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborTaggedSimulation.boundaryWire wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    {count : Nat} (target : PqxdhDeploymentIdealParams.Target count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : Nat) (runtime : A) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X)
    (result : PqxdhRecordLiftProtocol.RunResult 2
      (CborRawPublicState.Public × PqxdhDeploymentEnvironment.EnvState KemSK
        (PqxdhDeploymentIdealParams.Params KemSK count × PqxdhDeploymentIdealSteps.SplitBk)) X)
    (reached : result ∈ support (chainsOf (fun _ => false) setup (CborTaggedSimulation.boundaryWire wire parse)
      (CborRawCompile.route parse) (client (CborRawEnvironment.environment
        (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks target ensureInit identityIndex
          runtime) setup.serverKeyId) setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId
            bounds mode adversary))) :
    ∀ value, (chainView result).result = some value →
      PqxdhDeploymentHeadlineChain.ServerSlots setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
        setup.serverKeyId target (chainView result).slots value.2.1.transcript := by
  intro value found
  obtain ⟨annotated, member, same⟩ := real_support setup (CborTaggedSimulation.boundaryWire wire parse)
    (CborRawCompile.route parse) _ setup.serverKeyId bounds mode adversary result reached
  rw [same] at found ⊢
  rcases annotated with ⟨_ | inner, state⟩
  · exact absurd found (by simp [annotatedView])
  · simp only [annotatedView, Option.map_some, Option.some.injEq] at found
    subst found
    have slots := CborRawIdealSlotsWorld.slots_prefix setup wire parse checks phase1 phase2 target ensureInit identityIndex
      runtime bounds mode adversary _ member inner rfl _ [] (List.append_nil _).symm
    rw [← PqxdhDeploymentIdealHandoff.originMap_two] at slots
    exact ⟨slots.1, slots.2.1, slots.2.2.1⟩

end BeaconcryptCore.Computational.CborRawRecordProvenance

/-- info: 'BeaconcryptCore.Computational.CborRawRecordProvenance.real_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordProvenance.real_view

/-- info: 'BeaconcryptCore.Computational.CborRawRecordProvenance.real_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordProvenance.real_support

/-- info: 'BeaconcryptCore.Computational.CborRawRecordProvenance.real_slots_or_anomaly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordProvenance.real_slots_or_anomaly

/-- info: 'BeaconcryptCore.Computational.CborRawRecordProvenance.real_server_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordProvenance.real_server_slots
