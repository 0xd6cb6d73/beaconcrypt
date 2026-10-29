-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawAnomalyGuesser

/-! The explicit raw CCA predictor retains the complete original secrecy ledger and the selected public key. After interpretation by the selected secret's decapsulation oracle, its raw transcript prediction has exactly the actual native pool predictor's law. The sampled dummy secret is discarded only after that exact operational equality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawAnomalyGuesserRun
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealKeySwap (swapNative withChosen)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
open PqxdhDeploymentIdealAnomalyGuesser (interp simulateQ_interp)
open PqxdhPrivateKemSource (evalKem)
open PqxdhInitializerSecrecy (kemAmbientImpl)
open CborRawAnomalyGuesser (guesser)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

/-- The actual original raw ledger prediction is unchanged by replacing the selected secret and answering its finishes by the CCA oracle. -/
theorem atPool_interp (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (dummy : KemSK) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    simulateQ (interp setup parameters.chosen.2)
      ((fun result => PqxdhDeploymentIdealGuess.guessCt (CborTaggedSimulation.boundaryWire wire parse)
        target result.1.2.transcript) <$>
          (simulateQ (CborRawAnomalyNativeGuesser.native setup wire parse checks target (withChosen parameters dummy) created)
            (PqxdhDeploymentSecrecy.wrap setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
              setup.serverKeyId bounds (PqxdhDeploymentInterface.asModeO mode adversary))).run
                (PqxdhDeploymentNative.initial created)) =
      CborRawAnomalyPool.atPool setup wire parse checks target parameters created bounds mode adversary := by
  have same := CborRawAnomalyNativeGuesser.program_interp setup wire parse checks target parameters created dummy
    (PqxdhDeploymentSecrecy.wrap setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
      setup.serverKeyId bounds (PqxdhDeploymentInterface.asModeO mode adversary))
    (PqxdhDeploymentNative.initial created) (fun _ found => by cases found)
  have initialSwap : swapNative target.kem.val dummy (PqxdhDeploymentNative.initial created) =
      PqxdhDeploymentNative.initial created := by
    have owners : (PqxdhDeploymentNative.initial (KemSK := KemSK) created).native.owners = [] := rfl
    simp only [swapNative, PqxdhDeploymentIdealKeySwap.swapSched, owners, List.modify_nil]
    rfl
  rw [initialSwap] at same
  rw [simulateQ_map, same, Functor.map_map]
  rfl

/-- Exact evaluation of the public-key-only raw predictor: its own dummy, other-key and constructor draws, followed by the actual original native pool prediction. -/
theorem guesser_eval (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (ensureInit : StateT A ProbComp Bool) (runtime : A) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (pair : PqxdhLiveKemReservation.Pair KemSK) :
    evalKem setup.baseImpl setup.kem pair.2
      (guesser setup wire parse checks target ensureInit runtime bounds mode adversary pair.1) =
      simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen >>= fun _dummy =>
        PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen) count >>= fun others =>
          CborRawAnomalyPool.fixed setup wire parse checks target
            ⟨pair, others, PqxdhDeploymentIdealAnomalyBound.zeroCt⟩ ensureInit runtime bounds mode adversary := by
  simp only [guesser, PqxdhPrivateKemSource.evalKem_bind, PqxdhPrivateKemSource.evalKem_coins,
    CborRawAnomalyPool.fixed]
  apply bind_congr
  intro dummy
  apply bind_congr
  intro others
  apply bind_congr
  intro born
  rcases born with ⟨_ | created, after⟩
  · rw [← simulateQ_interp, simulateQ_pure]
  · simp only [← simulateQ_interp, bind_pure_comp]
    exact atPool_interp setup wire parse checks target
      ⟨pair, others, PqxdhDeploymentIdealAnomalyBound.zeroCt⟩ created dummy.2 bounds mode adversary

/-- The actual raw pool predictor for a selected key has the law of an explicit pre-challenge CCA guesser on its public key. -/
theorem pair_law (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (ensureInit : StateT A ProbComp Bool) (runtime : A) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (pair : PqxdhLiveKemReservation.Pair KemSK) :
    LazyOracleDiscard.LawEq
      (PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen) count >>= fun others =>
        CborRawAnomalyPool.fixed setup wire parse checks target
          ⟨pair, others, PqxdhDeploymentIdealAnomalyBound.zeroCt⟩ ensureInit runtime bounds mode adversary)
      (evalKem setup.baseImpl setup.kem pair.2
        (guesser setup wire parse checks target ensureInit runtime bounds mode adversary pair.1)) := by
  rw [guesser_eval]
  exact (LazyOracleDiscard.lawEq_drop (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen) _).symm

end BeaconcryptCore.Computational.CborRawAnomalyGuesserRun

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyGuesserRun.atPool_interp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyGuesserRun.atPool_interp
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyGuesserRun.guesser_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyGuesserRun.guesser_eval
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyGuesserRun.pair_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyGuesserRun.pair_law
