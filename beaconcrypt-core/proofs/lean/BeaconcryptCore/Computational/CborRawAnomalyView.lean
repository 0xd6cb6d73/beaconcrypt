-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawAnomalyGuess
import BeaconcryptCore.Computational.CborRawHeadlineSlots

/-! The actual raw record view retains drawn challenger parameters only for analysis. On every supported outcome its concrete native anomaly is contained in the original transcript guess hitting that same drawn ciphertext. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawAnomalyView
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhRecordLiftIdeal (View chainView)
open PqxdhDeploymentIdealHandoff (annotatedView)
open CborTaggedSimulation (boundaryWire)
variable {n : Nat} {ι KemSK Reader Response A E X : Type} {baseSpec : OracleSpec ι}

abbrev EnvironmentState (KemSK : Type) (count : Nat) :=
  CborRawPublicState.Public × PqxdhDeploymentEnvironment.EnvState KemSK (Params KemSK count × PqxdhDeploymentIdealSteps.SplitBk)

noncomputable def hitView (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) {count : Nat} (target : Target count)
    (view : View 2 (EnvironmentState KemSK count) X) : Bool :=
  view.result.any fun value => decide (PqxdhDeploymentIdealGuess.guessCt (boundaryWire wire parse) target
    value.2.1.transcript = some value.2.2.2.backend.1.challenge)

/-- The actual early-admission World and real compiled raw view agree on all permitted fields and retained environment state. -/
theorem full_event (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : PqxdhRecordLiftInterface.Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (event : (X × PqxdhDeploymentSecrecy.Ledger) × E × CborRawPostActive.Produced → Bool) :
    (fun result : PqxdhRecordLiftLaterWorlds.Outcome E X × PqxdhRecordLiftWorld.State n =>
      result.1.any fun value => event (value.2.1, value.2.2, result.2.produced)) <$>
      (simulateQ (CborRecordWorldSimulation.guarded setup codec route)
        (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary)).run
          PqxdhRecordLiftWorld.initial =
    (fun view : View n E X => view.result.any fun value => event ((value.1, value.2.1), value.2.2, view.produced)) <$>
      (chainView <$> PqxdhRecordLiftLaterWorlds.chainsOf (fun _ => false) setup codec route
        (CborRawRecordLiftBounds.client env setup.source.crypto codec serverKid bounds mode adversary)) := by
  rw [CborRawRecordProvenance.real_view]
  have erased := CborRawIdealProvenanceStartup.erase setup codec route env serverKid bounds mode adversary
  have compared := CborRecordWorldSimulation.client_simulation setup codec route
    (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary)
    (PqxdhRecordLiftWorld.initial (n := n))
  change _ = (simulateQ (CborRecordWorldSimulation.guarded setup codec route)
    (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary)).run
      PqxdhRecordLiftWorld.initial at compared
  have complete := erased.trans compared
  rw [← complete, Functor.map_map, Functor.map_map]
  congr 1
  funext result
  rcases result with ⟨_ | inner, state⟩ <;> rfl

/-- The actual raw anomaly on the complete real record view is contained in its same-run drawn-ciphertext hit event. -/
theorem anomaly_le_hit (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    {count : Nat} (target : Target count) (ensureInit : StateT A ProbComp Bool) (runtime : A)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    𝒟[CborRawHeadlineSlots.anomaly setup wire parse target <$>
      CborRawHeadlineSlots.realView setup wire parse checks target ensureInit runtime bounds mode adversary] {true} ≤
    𝒟[hitView wire parse target <$>
      CborRawHeadlineSlots.realView setup wire parse checks target ensureInit runtime bounds mode adversary] {true} := by
  classical
  rw [CborRawHeadlineSlots.realView, CborRawRecordProvenance.real_view]
  simp only [Functor.map_map]
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
  apply prEvent_mono_of_support
  intro result reached held
  change CborRawHeadlineSlots.anomaly setup wire parse target (annotatedView result) = true at held
  change hitView wire parse target (annotatedView result) = true
  unfold CborRawHeadlineSlots.anomaly at held
  have occurred := of_decide_eq_true held
  clear held
  rcases result with ⟨_ | inner, state⟩
  · simp [annotatedView] at occurred
  · simp only [annotatedView, Option.map_some, Option.some.injEq] at occurred
    obtain ⟨value, rfl, anomaly⟩ := occurred
    simp only [hitView, annotatedView, Option.map_some, Option.any_some]
    apply decide_eq_true
    exact CborRawAnomalyGuess.world setup wire parse checks phase1 phase2 target ensureInit 0 runtime bounds mode adversary
      _ reached inner rfl anomaly

end BeaconcryptCore.Computational.CborRawAnomalyView

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyView.full_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyView.full_event
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyView.anomaly_le_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyView.anomaly_le_hit
