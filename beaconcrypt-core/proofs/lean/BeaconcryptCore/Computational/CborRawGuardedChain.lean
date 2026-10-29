-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawGuardedSeedDefer

/-! The full concrete ideal-registration handoff to the actual split record environment under native CBOR admission. The chain combines checked CTX completion erasure, actual slot-service representation, exact seed relocation, kernel identities and actual install-time seed deferral for arbitrary adaptive CE clients. No whole-game handoff assumption is introduced. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawGuardedChain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentBackend (XState)
open PqxdhDeploymentIdealKeys (splitView moveSeeds)
open PqxdhDeploymentSeedSplit (mapBackend seedFree)
open PqxdhDeploymentFinishErasure (fullX)
open LazyOracleDiscard (LawEq)
variable {ι KemSK Reader Response SourceReader SourceResponse Result : Type} {baseSpec : OracleSpec ι}

private theorem view_full {S : Type} (state : XState KemSK (PqxdhDeploymentIdealSteps.IdealBk S) 2) :
    splitView (fullX state) = splitView state := by
  simp only [splitView, fullX, LazyOracleDiscard.StateLens.set_set]
  rfl

private theorem view_backend {S₁ S₂ : Type} (project : S₁ → S₂)
    (state : XState KemSK (PqxdhDeploymentIdealSteps.IdealBk S₁) 2) :
    splitView (mapBackend project state) = splitView state := rfl

private theorem view_move {M : Type}
    (state : XState KemSK ((M × (PqxdhRecordLiftWorld.SeedSpec 2).QueryCache) ×
      (PqxdhRegistrationJointKemSecondEntry.Alloc PqxdhDeploymentIdealSlots.Coord 2 ×
        PqxdhDeploymentIdealSteps.IdealCore)) 2) : splitView (moveSeeds state) = splitView state := rfl

private theorem view_seed {S : Type} (state : XState KemSK (PqxdhDeploymentIdealSteps.IdealBk S) 2) :
    splitView (seedFree state) = splitView state := rfl

/-- The actual ideal and install-time split registration interpreters have the same law of every adaptive result and the complete split view, with independent codecs and native admission. The only erased fields are those explicitly excluded by the existing split view. -/
theorem ideal_to_split (setup : Setup baseSpec KemSK) (recordCodec : Codec Reader Response)
    (sourceCodec : Codec SourceReader SourceResponse) (route : RawCtxServerRouting.SenderDecoder) (checks : Checks)
    {count : Nat} (target : PqxdhDeploymentIdealParams.Target count)
    (parameters : PqxdhDeploymentIdealParams.Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (work : OracleComp Spec Result) :
    LawEq ((fun value => (value.1, splitView value.2)) <$>
        (simulateQ (CborRawGuardedJoin.nativeHandler setup recordCodec route
          (PqxdhDeploymentIdealSteps.idealReg setup sourceCodec route checks target parameters created)) work).run
          (PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)))
      ((fun value => (value.1, splitView value.2)) <$>
        (simulateQ (CborRawGuardedJoin.nativeHandler setup recordCodec route
          (PqxdhDeploymentIdealDefer.idealSplit setup sourceCodec route checks target parameters created)) work).run
          (PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.splitInit created))) := by
  have erased := (CborRawGuardedErasure.ideal_erase setup recordCodec sourceCodec route checks target parameters created
    work (PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created))).map
      (fun value => (value.1, splitView value.2))
  simp only [Functor.map_map, Prod.map_fst, Prod.map_snd, id_eq, view_full] at erased
  have represented := (CborRawGuardedRepresentation.represent_ideal setup recordCodec sourceCodec route checks target
    parameters created work).map (fun value => (value.1, splitView value.2))
  simp only [Functor.map_map, Prod.map_fst, Prod.map_snd, id_eq, view_backend] at represented
  have moved := congrArg (fun program => (fun value => (value.1, splitView value.2)) <$> program)
    (CborRawGuardedSeedMove.seed_move setup recordCodec sourceCodec route checks target parameters created work)
  simp only [Functor.map_map, Prod.map_fst, Prod.map_snd, id_eq, view_move] at moved
  have kernel : PqxdhDeploymentIdealKeys.idealSplitX setup sourceCodec route checks target parameters created =
      PqxdhDeploymentIdealKernel.idealSplitEager setup sourceCodec route checks target parameters created := by
    funext query
    exact PqxdhDeploymentIdealKernel.split_kernel setup sourceCodec route checks target parameters created query
  rw [kernel] at moved
  have deferred := (CborRawGuardedSeedDefer.ideal_defer setup recordCodec sourceCodec route checks target parameters
    created work).map (fun value => (value.1, splitView value.2))
  simp only [Functor.map_map, Prod.map_fst, Prod.map_snd, id_eq, view_seed] at deferred
  exact erased.trans (represented.trans ((LawEq.of_eq moved).trans deferred))

end BeaconcryptCore.Computational.CborRawGuardedChain

/-- info: 'BeaconcryptCore.Computational.CborRawGuardedChain.ideal_to_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawGuardedChain.ideal_to_split
