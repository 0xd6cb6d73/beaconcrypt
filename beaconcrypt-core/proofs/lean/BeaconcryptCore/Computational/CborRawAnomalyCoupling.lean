-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawAnomalyPrefixLedger

/-! Actual raw middle and private pool executions are coupled through the same full-ledger prefix. At the selected raw accept both freeze the original prefix guess; all later native failures and private effects preserve that guess. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open OracleComp.ProgramLogic.Relational
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawAnomalyCoupling
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FullSpec FreshBounds)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealPostSource (Mid)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentTranscript (acceptCount)
open PqxdhDeploymentIdealGuess (UntilStop guessCt)
open CborRawPreScan (Source Inv counter native pool)
open CborRawAnomalyLedger (full stop)
variable {ι KemSK Reader Response Value : Type} {baseSpec : OracleSpec ι}

abbrev MiddleState (KemSK : Type) := Ledger × CborRawPublicState.Public × CborRawMiddleSimulation.Native KemSK
abbrev PoolState (KemSK : Type) := Ledger × CborAdmissionCompiler.Local × PqxdhRegistrationJointSchedule.State KemSK

def Related (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) {count : Nat} (target : Target count)
    (initial : Mid KemSK) (left : MiddleState KemSK) (right : PoolState KemSK) : Prop :=
  ∃ ledger state, Inv setup wire parse initial state ∧ counter state = acceptCount ledger.transcript ∧
    counter state ≤ target.accept ∧ left = (ledger, native state) ∧ right = (ledger, pool state)

/-- The full actual raw steps share a concrete source prefix or stop with the same original transcript guess. -/
theorem step (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (initial : Mid KemSK) (bounds : FreshBounds) (query : FullSpec.Domain)
    (left : MiddleState KemSK) (right : PoolState KemSK) (related : Related setup wire parse target initial left right) :
    RelTriple ((full (CborRawMiddleSimulation.handler setup wire parse checks target parameters created)
      setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds query).run left)
      ((full (CborRawPreScan.poolCompiler setup wire parse checks target parameters created)
        setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds query).run right)
      (UntilStop (Related setup wire parse target initial)
        (stop (CborTaggedSimulation.boundaryWire wire parse) target)
        (stop (CborTaggedSimulation.boundaryWire wire parse) target)) := by
  obtain ⟨ledger, state, valid, clock, before, rfl, rfl⟩ := related
  by_cases selected : ∃ raw, query = .inl (.inr (.accept raw)) ∧ acceptCount ledger.transcript = target.accept
  · obtain ⟨raw, rfl, selectedClock⟩ := selected
    exact relTriple_post_mono (PqxdhServerAuthEntryFactor.relTriple_support _ _ _ _
      (CborRawAnomalyLedger.selected_stop _ _ _ _ _ target raw (ledger, native state) selectedClock)
      (CborRawAnomalyLedger.selected_stop _ _ _ _ _ target raw (ledger, pool state) selectedClock))
      (fun _ _ both => Or.inr ⟨_, both⟩)
  · have other : ∀ raw, query = .inl (.inr (.accept raw)) → counter state ≠ target.accept := by
      intro raw same current
      exact selected ⟨raw, same, clock.symm.trans current⟩
    have first := CborRawAnomalyPrefixLedger.middle_project setup wire parse checks target parameters created phase1 phase2
      initial bounds query ledger state valid
    have second := CborRawAnomalyPrefixLedger.pool_project setup wire parse checks target parameters created phase1 phase2
      initial bounds query ledger state valid other
    rw [← first, ← second, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
    have diagonal : RelTriple
        ((full (CborRawMiddleSimulation.compiled setup wire parse checks target parameters created) setup.source.crypto
          (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds query).run (ledger, state))
        ((full (CborRawMiddleSimulation.compiled setup wire parse checks target parameters created) setup.source.crypto
          (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds query).run (ledger, state))
        (fun left right => left = right ∧ Inv setup wire parse initial left.2.2 ∧
          counter left.2.2 = acceptCount left.2.1.transcript ∧ counter left.2.2 ≤ target.accept) :=
      relTriple_refl_of_mem_support _ (fun result reached => ⟨rfl,
        CborRawAnomalyPrefixLedger.keeps setup wire parse checks target parameters created phase1 phase2 initial bounds
          query ledger state valid clock before other result reached⟩)
    refine relTriple_bind diagonal ?_
    intro left right pair
    obtain ⟨rfl, held, clock', before'⟩ := pair
    exact relTriple_pure_pure (Or.inl ⟨rfl, left.2.1, left.2.2, held, clock', before', rfl, rfl⟩)

/-- Equality of the frozen public guess holds for arbitrary adaptive full-interface programs, from every actual valid prefix state. -/
theorem program_law (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (initial : Mid KemSK) (bounds : FreshBounds) (work : OracleComp FullSpec Value)
    (ledger : Ledger) (state : Source KemSK) (valid : Inv setup wire parse initial state)
    (clock : counter state = acceptCount ledger.transcript) (before : counter state ≤ target.accept) :
    LazyOracleDiscard.LawEq
      ((fun result => guessCt (CborTaggedSimulation.boundaryWire wire parse) target result.2.1.transcript) <$>
        (simulateQ (full (CborRawMiddleSimulation.handler setup wire parse checks target parameters created)
          setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds) work).run
            (ledger, native state))
      ((fun result => guessCt (CborTaggedSimulation.boundaryWire wire parse) target result.2.1.transcript) <$>
        (simulateQ (full (CborRawPreScan.poolCompiler setup wire parse checks target parameters created)
          setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds) work).run
            (ledger, pool state)) := by
  apply PqxdhDeploymentIdealGuess.lawEq_until_stop _ _ (Related setup wire parse target initial)
    (stop (CborTaggedSimulation.boundaryWire wire parse) target)
    (stop (CborTaggedSimulation.boundaryWire wire parse) target)
    (CborRawAnomalyLedger.stop_keeps _ _ _ _ _ target)
    (CborRawAnomalyLedger.stop_keeps _ _ _ _ _ target)
    (step setup wire parse checks target parameters created phase1 phase2 initial bounds) work _ _
    ⟨ledger, state, valid, clock, before, rfl, rfl⟩
  intro left right paired
  rcases paired with ⟨_, ledger, state, _, _, _, sameLeft, sameRight⟩ | ⟨value, first, second⟩
  · rw [sameLeft, sameRight]
  · have firstGuess : guessCt (CborTaggedSimulation.boundaryWire wire parse) target left.2.1.transcript = value := by
      unfold stop at first
      split at first
      · exact Option.some.inj first
      · cases first
    have secondGuess : guessCt (CborTaggedSimulation.boundaryWire wire parse) target right.2.1.transcript = value := by
      unfold stop at second
      split at second
      · exact Option.some.inj second
      · cases second
    exact firstGuess.trans secondGuess.symm

end BeaconcryptCore.Computational.CborRawAnomalyCoupling

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyCoupling.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyCoupling.step
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyCoupling.program_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyCoupling.program_law
