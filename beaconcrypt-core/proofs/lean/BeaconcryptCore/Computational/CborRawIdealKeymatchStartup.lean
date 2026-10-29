-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealKeymatchStartupRest
import BeaconcryptCore.Computational.CborRawIdealProvenanceStartup

/-! Actual EnvGD startup key facts include every parameter and constructor draw, the counted startup World, one real Server initialization, and the unchanged full adaptive secrecy ledger. No local invariant or whole-game simulation is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawIdealKeymatchStartup
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
open PqxdhDeploymentIdealParams (Target)
open CborTaggedSimulation (boundaryWire)
open CborRawCompile (route)
open PqxdhRecordLiftOrigins (Origins)
open PqxdhDeploymentIdealOrigins (isAnnot query_free free_run)
open PqxdhDeploymentEnvironmentJoin (uncount initialized)
open CborRawIdealProvenanceStartup (annotatedRun coins_annotated)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

/-- Every full annotated raw World outcome has native-wire key facts at its actual retained challenger parameter. -/
theorem world (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    ∀ result ∈ support (annotatedRun setup (boundaryWire wire parse) (route parse)
      (CborRawEnvironment.environment
        (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks target ensureInit
          identityIndex runtime) setup.serverKeyId) setup.serverKeyId bounds mode adversary),
      ∀ value, result.1 = some value →
        PqxdhDeploymentIdealTrace.KeyFacts setup (boundaryWire wire parse) checks target
          value.2.2.2.backend.1 value.2.1.2.transcript value.2.2.2.backend.2.2.2 := by
  intro result member value found
  let env := CborRawEnvironment.environment
    (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks target ensureInit
      identityIndex runtime) setup.serverKeyId
  change result ∈ support (annotatedRun setup (boundaryWire wire parse)
    (route parse) env setup.serverKeyId bounds mode adversary) at member
  unfold annotatedRun at member
  rw [PqxdhDeploymentEnvironmentDraw.program_rest, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
  obtain ⟨step, stepMember, rest⟩ := member
  have coinsFree : (simulateQ PqxdhRecordLiftInterface.coinLift env.start).IsQueryBoundP
      (fun request => isAnnot request = true) 0 :=
    RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
      (fun coin => by
        simp only [ite_false]
        exact query_free (n := 2) (.inr (.inl (.inl coin))) rfl)
  have init : (PqxdhRecordLiftOrigins.initial : PqxdhRecordLiftOrigins.State 2) =
      (PqxdhRecordLiftWorld.initial, PqxdhRecordLiftOrigins.empty) := rfl
  rw [init, coins_annotated setup (boundaryWire wire parse) (route parse) env.start, free_run setup (boundaryWire wire parse) (route parse) _ coinsFree, support_map] at stepMember
  obtain ⟨plain, plainMember, rfl⟩ := stepMember
  have counted := PqxdhDeploymentEnvironmentJoin.coins_world setup (boundaryWire wire parse) (route parse) env.start
    (PqxdhRecordLiftWorld.initial (n := 2))
  have inMapped : Prod.map id PqxdhDeploymentEnvironmentJoin.uncount plain ∈ support (Prod.map id
      PqxdhDeploymentEnvironmentJoin.uncount <$> (simulateQ (PqxdhRecordLiftWorld.handler setup (boundaryWire wire parse) (route parse))
        (simulateQ PqxdhRecordLiftInterface.coinLift env.start)).run (PqxdhRecordLiftWorld.initial (n := 2))) := by
    rw [support_map]
    exact ⟨plain, plainMember, rfl⟩
  rw [counted, support_map] at inMapped
  obtain ⟨startValue, startMember, same⟩ := inMapped
  have started : plain.1 ∈ support env.start := by
    have first := congrArg Prod.fst same
    simp only [Prod.map_fst, id_eq] at first
    rw [← first]
    exact startMember
  have fresh : PqxdhDeploymentEnvironmentJoin.uncount plain.2 =
      PqxdhDeploymentEnvironmentJoin.uncount (PqxdhRecordLiftWorld.initial (n := 2)) := by
    have second := congrArg Prod.snd same
    simp only [Prod.map_snd] at second
    exact second.symm
  rcases plain with ⟨_ | ⟨created, start⟩, w⟩
  · simp only [PqxdhDeploymentEnvironmentDraw.worldRest, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at rest
    subst rest
    cases found
  · have vacant : w.server = none := congrArg PqxdhRecordLiftWorld.State.server fresh
    have initRun : (CborRawIdealProvenanceGuard.handler setup (boundaryWire wire parse) (route parse) (.inl created)).run (w, PqxdhRecordLiftOrigins.empty) =
        pure ((), (PqxdhDeploymentEnvironmentJoin.initialized created w, PqxdhRecordLiftOrigins.empty)) := by
      change (PqxdhRecordLiftOrigins.handler setup (boundaryWire wire parse) (route parse) (.inl created)).run
        (w, PqxdhRecordLiftOrigins.empty) = _
      rw [PqxdhDeploymentIdealOrigins.handler_other setup (boundaryWire wire parse) (route parse) _ _ rfl]
      change (fun result => (result.1, (result.2, PqxdhRecordLiftOrigins.empty))) <$>
        PqxdhRecordLiftWorld.initializeServer created w = _
      simp only [PqxdhRecordLiftWorld.initializeServer, vacant]
      rfl
    dsimp only [PqxdhDeploymentEnvironmentDraw.worldRest] at rest
    rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, initRun, pure_bind, simulateQ_bind, StateT.run_bind,
      mem_support_bind_iff] at rest
    obtain ⟨middle, middleMember, final⟩ := rest
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at final
    subst final
    simp only [Option.some.injEq] at found
    subst found
    dsimp only [env] at started
    rw [CborRawEnvironment.environment, support_map] at started
    obtain ⟨born, supported, sameStart⟩ := started
    cases born with
    | none => cases sameStart
    | some born =>
        rcases born with ⟨made, environment⟩
        cases Option.some.inj sameStart
        change some (made, environment) ∈ support
          (PqxdhDeploymentIdealParams.drawParams setup count >>= fun parameters =>
            PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime
              (fun made => (parameters, PqxdhDeploymentIdealSteps.splitInit made))) at supported
        rw [mem_support_bind_iff] at supported
        obtain ⟨parameters, _, constructed⟩ := supported
        have begins := PqxdhDeploymentEnvironment.start_initial setup ensureInit identityIndex runtime
          (fun made => (parameters, PqxdhDeploymentIdealSteps.splitInit made)) made environment constructed
        subst begins
        exact CborRawIdealKeymatchStartupRest.rest_keyFacts setup wire parse checks target parameters ensureInit
          identityIndex runtime made w fresh bounds (PqxdhDeploymentInterface.asModeO mode adversary)
          ⟨PqxdhDeploymentCompile.Log.empty, setup.serverKeyId⟩ middle middleMember

end BeaconcryptCore.Computational.CborRawIdealKeymatchStartup

/-- info: 'BeaconcryptCore.Computational.CborRawIdealKeymatchStartup.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealKeymatchStartup.world
