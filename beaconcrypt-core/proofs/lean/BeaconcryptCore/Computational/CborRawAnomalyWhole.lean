-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawAnomalyWorld
import BeaconcryptCore.Computational.CborRawAnomalyStartup

/-! The concrete native raw-pool predictor covers the actual complete raw World anomaly. Challenger draws and Server constructor coins remain counted until each corresponding full continuation has been related operationally. No challenge-hit, prefix or whole-game equality is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawAnomalyWhole
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec asModeO)
open PqxdhDeploymentIdealParams (Target Params drawParams)
open PqxdhDeploymentSecrecy (wrap)
open PqxdhDeploymentEnvironmentJoin (uncount)
open CborTaggedSimulation (boundaryWire)
open CborRawIdealWorldProgram (fixedClient client)
open CborRawHeadlineStartup (coins)
open CborRawAnomalyWorld (observe)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

section Fixed
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (ensureInit : StateT A ProbComp Bool) (runtime : A)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)

/-- The actual source constructor remains a counted World draw before its complete hit continuation. -/
theorem fixed_observe (world : PqxdhRecordLiftWorld.State 2) :
    observe wire parse target <$> (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse)
      (CborRawCompile.route parse)) (fixedClient setup wire parse checks target ensureInit runtime parameters
        (wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds (asModeO mode adversary)))).run world =
      (coins setup (boundaryWire wire parse) (CborRawCompile.route parse) (CborRawHeadlineSlot.birth setup ensureInit runtime)
        world >>= fun born => match born.1.1 with
          | none => pure false
          | some created => observe wire parse target <$>
              (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse) (CborRawCompile.route parse))
                (CborRawIdealWorldProgram.after setup wire parse checks target ensureInit runtime parameters created
                  (wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
                    (asModeO mode adversary)))).run born.2) := by
  simp only [fixedClient, simulateQ_bind, StateT.run_bind, map_bind]
  rw [CborRawHeadlineStartup.guarded_coins]
  apply bind_congr
  intro born
  cases found : born.1.1 with
  | none => simp only [simulateQ_pure, StateT.run_pure, map_pure, observe, Option.any_none]
  | some created => simp only []

/-- Actual constructor failure and every successful raw World continuation are bounded by the concrete native pool predictor. -/
theorem fixed_pool (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse))
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (world : PqxdhRecordLiftWorld.State 2) (fresh : uncount world = uncount PqxdhRecordLiftWorld.initial) :
    𝒟[observe wire parse target <$> (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse)
      (CborRawCompile.route parse)) (fixedClient setup wire parse checks target ensureInit runtime parameters
        (wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds (asModeO mode adversary)))).run world]
      {true} ≤
    𝒟[(fun value => decide (value = some parameters.challenge)) <$>
      CborRawAnomalyPool.fixed setup wire parse checks target parameters ensureInit runtime bounds mode adversary] {true} := by
  rw [fixed_observe]
  have weighted := CborRawAnomalyStartup.counted_le setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (CborRawHeadlineSlot.birth setup ensureInit runtime)
    (fun born current => match born.1 with
      | none => pure false
      | some created => observe wire parse target <$>
          (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse) (CborRawCompile.route parse))
            (CborRawIdealWorldProgram.after setup wire parse checks target ensureInit runtime parameters created
              (wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds (asModeO mode adversary)))).run current)
    (fun born => match born.1 with
      | none => pure false
      | some created => (fun value => decide (value = some parameters.challenge)) <$>
          CborRawAnomalyPool.atPool setup wire parse checks target parameters created bounds mode adversary) world (by
      intro born supported current same
      cases found : born.1 with
      | none => exact le_rfl
      | some created =>
          exact le_of_eq (CborRawAnomalyWorld.after_pool setup wire parse checks target parameters ensureInit runtime
            bounds mode adversary lengths parser phase1 phase2 created
            ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) born.2
            (by rw [← found]; exact supported) current (same.trans fresh)))
  have rightEq : (CborRawHeadlineSlot.birth setup ensureInit runtime >>= fun born => match born.1 with
      | none => pure false
      | some created => (fun value => decide (value = some parameters.challenge)) <$>
          CborRawAnomalyPool.atPool setup wire parse checks target parameters created bounds mode adversary) =
      (fun value => decide (value = some parameters.challenge)) <$>
        CborRawAnomalyPool.fixed setup wire parse checks target parameters ensureInit runtime bounds mode adversary := by
    rw [← CborRawAnomalyStartup.fixed_source setup wire parse checks target parameters ensureInit runtime bounds mode adversary,
      map_bind]
    apply bind_congr
    intro born
    cases born.1 <;> simp only [map_pure, reduceCtorEq, decide_false]
  rw [rightEq] at weighted
  exact weighted

end Fixed

/-- The complete raw record view's actual native anomaly is bounded by the explicit native raw-pool predictor hit probability. -/
theorem anomaly_pool (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse))
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    {count : Nat} (target : Target count) (ensureInit : StateT A ProbComp Bool) (runtime : A)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    𝒟[CborRawHeadlineSlots.anomaly setup wire parse target <$>
      CborRawHeadlineSlots.realView setup wire parse checks target ensureInit runtime bounds mode adversary] {true} ≤
    𝒟[CborRawAnomalyPool.hit setup wire parse checks target ensureInit runtime bounds mode adversary] {true} := by
  apply (CborRawAnomalyView.anomaly_le_hit setup wire parse checks nativePhase1 phase2 target ensureInit runtime bounds
    mode adversary).trans
  let event := fun result : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawAnomalyView.EnvironmentState KemSK count ×
      CborRawPostActive.Produced =>
    decide (PqxdhDeploymentIdealGuess.guessCt (boundaryWire wire parse) target result.1.2.transcript =
      some result.2.1.2.backend.1.challenge)
  have viewed := CborRawAnomalyView.full_event setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (CborRawHeadlineSlots.environment setup wire parse checks target ensureInit runtime) setup.serverKeyId bounds mode
    adversary event
  change observe wire parse target <$>
    (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse) (CborRawCompile.route parse))
      (PqxdhRecordLiftInterface.program (CborRawHeadlineSlots.environment setup wire parse checks target ensureInit runtime)
        setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds mode adversary)).run
      PqxdhRecordLiftWorld.initial = CborRawAnomalyView.hitView wire parse target <$>
        CborRawHeadlineSlots.realView setup wire parse checks target ensureInit runtime bounds mode adversary at viewed
  rw [← viewed, CborRawHeadlineSlots.environment, CborRawIdealWorldProgram.program, client, simulateQ_bind, StateT.run_bind, map_bind,
    CborRawHeadlineStartup.guarded_coins]
  have weighted := CborRawAnomalyStartup.counted_le setup (boundaryWire wire parse) (CborRawCompile.route parse)
    (drawParams setup count)
    (fun parameters world => observe wire parse target <$>
      (simulateQ (CborRecordWorldSimulation.guarded setup (boundaryWire wire parse) (CborRawCompile.route parse))
        (fixedClient setup wire parse checks target ensureInit runtime parameters
          (wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds (asModeO mode adversary)))).run world)
    (fun parameters => (fun value => decide (value = some parameters.challenge)) <$>
      CborRawAnomalyPool.fixed setup wire parse checks target parameters ensureInit runtime bounds mode adversary)
    PqxdhRecordLiftWorld.initial (fun parameters _ world fresh =>
      fixed_pool setup wire parse checks target parameters ensureInit runtime bounds mode adversary lengths parser phase1
        phase2 world fresh)
  convert weighted using 1
  rw [CborRawAnomalyPool.hit]
  simp only [map_eq_bind_pure_comp, Function.comp_def]

end BeaconcryptCore.Computational.CborRawAnomalyWhole

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyWhole.fixed_observe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyWhole.fixed_observe
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyWhole.fixed_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyWhole.fixed_pool
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyWhole.anomaly_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyWhole.anomaly_pool
