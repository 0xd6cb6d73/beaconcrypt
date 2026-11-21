-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawAnomalyNativeSwap

/-! The selected owner's actual raw finish is implemented with a pre-challenge decapsulation oracle. Its command-dependent CBOR codec uses the retained native owner pin; the oracle receives ciphertext bytes and never the selected secret key. Only unused extended analysis ghosts are introduced locally and immediately projected away. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawAnomalyOracle
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentIdealKeySwap (swapNative swapX Holds HoldsX)
open PqxdhDeploymentNative (State)
open PqxdhDeploymentBackend (XState)
open PqxdhDeploymentIdealAnomalyGuesser (interp oracleFinish)
open PqxdhKemIndCca (MlKemCCAOracleSpec IsMlKemLogicalDecapsulationQuery)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

def virtual (state : State KemSK) : XState KemSK Unit 0 :=
  ⟨state, (), ∅, PqxdhDeploymentLater.Snap.empty, []⟩

private noncomputable opaque sealedFinish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (raw : Pqxdh.Bytes) :
    {implementation : StateT (State KemSK) (OracleComp (MlKemCCAOracleSpec baseSpec)) (Option Pqxdh.Bytes) //
      ∀ state, implementation.run state = Prod.map id XState.base <$>
        (oracleFinish setup codec index raw).run (virtual state)} :=
  ⟨fun state => Prod.map id XState.base <$> (oracleFinish setup codec index raw).run (virtual state), fun _ => rfl⟩

noncomputable def finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (raw : Pqxdh.Bytes) : StateT (State KemSK) (OracleComp (MlKemCCAOracleSpec baseSpec)) (Option Pqxdh.Bytes) :=
  (sealedFinish setup codec index raw).val

private theorem finish_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (raw : Pqxdh.Bytes) (state : State KemSK) :
    (finish setup codec index raw).run state = Prod.map id XState.base <$>
      (oracleFinish setup codec index raw).run (virtual state) :=
  (sealedFinish setup codec index raw).property state

private theorem real_finish_base (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (raw : Pqxdh.Bytes) (state : State KemSK) :
    Prod.map id XState.base <$>
      (PqxdhDeploymentIdealSteps.realRegAt setup codec route checks created ⟨.finish index raw, trivial⟩).run (virtual state) =
      (PqxdhDeploymentNative.handler setup codec checks route created.seed (.inr (.finish index raw))).run state := by
  rw [PqxdhDeploymentIdealEnvReal.realRegAt_quiet setup codec checks route created _ (fun _ same => by cases same)]
  simp only [StateT.run, virtual, Functor.map_map, Prod.map, id_eq, Prod.mk.eta, id_map']

/-- The raw native oracle finish has precisely the original finish outcome and complete state with only the selected KEM secret replaced. -/
theorem finish_interp (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (old new : KemSK) (raw : Pqxdh.Bytes) (state : State KemSK)
    (held : Holds index old state.native.owners) :
    simulateQ (interp setup old) ((finish setup codec index raw).run (swapNative index new state)) =
      Prod.map id (swapNative index new) <$>
        (PqxdhDeploymentNative.handler setup codec checks route created.seed (.inr (.finish index raw))).run state ∧
    ∀ result ∈ support ((PqxdhDeploymentNative.handler setup codec checks route created.seed (.inr (.finish index raw))).run state),
      Holds index old result.2.native.owners := by
  have full := PqxdhDeploymentIdealAnomalyGuesser.oracleFinish_interp setup codec checks route created index old new raw (virtual state) held
  refine ⟨?_, ?_⟩
  · have mapped := congrArg (fun work => Prod.map id XState.base <$> work) full.1
    rw [← real_finish_base setup codec checks route created index raw state]
    rw [finish_run, simulateQ_map]
    simpa only [Functor.map_map, virtual, swapX, Prod.map, id_eq] using mapped
  · intro result supported
    rw [← real_finish_base setup codec checks route created index raw state, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact full.2 inner reached

noncomputable def actualCodec (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (index : Nat) (raw : Pqxdh.Bytes) (state : State KemSK) : Codec Reader Response :=
  PqxdhBoundaryRecordPrelude.withReader
    (CborProductionBoundary.commandCodec wire parse
      (CborProductionBoundary.normalizationSender (.inr (.finish index raw)) state) (.inr (.finish index raw)))
    (CborProductionBoundary.nativeReader parse)

noncomputable def rawFinish (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (index : Nat) (raw : Pqxdh.Bytes) :
    StateT (State KemSK) (OracleComp (MlKemCCAOracleSpec baseSpec)) (Option Pqxdh.Bytes) :=
  fun state => (finish setup (actualCodec wire parse index raw state) index raw).run state

private theorem actualCodec_swap (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (index : Nat) (raw : Pqxdh.Bytes)
    (new : KemSK) (state : State KemSK) :
    actualCodec wire parse index raw (swapNative index new state) = actualCodec wire parse index raw state := by
  unfold actualCodec
  rw [CborRawAnomalySwap.normalization_swap]

attribute [local irreducible] finish actualCodec

private theorem handler_finish (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) (raw : Pqxdh.Bytes) (state : State KemSK) :
    (CborProductionBoundary.handler setup wire parse checks created.seed (.inr (.finish index raw))).run state =
      (PqxdhDeploymentNative.handler setup (actualCodec wire parse index raw state) checks
        (RawCtxFrameDecoding.sender (CborProductionBoundary.nativeReader parse).model) created.seed
          (.inr (.finish index raw))).run state := by
  unfold CborProductionBoundary.handler
  erw [CborCommandFilter.admitted_run (spec := PqxdhDeploymentInterface.Spec)
    CborProductionBoundary.allowed CborProductionBoundary.reject
    (CborProductionBoundary.baseHandler setup wire parse checks created.seed)
    (.inr (.finish index raw)) state (by rfl)]
  unfold CborProductionBoundary.baseHandler
  rw [CborCommandFilter.atState_run]
  unfold actualCodec
  rfl

private theorem rawFinish_swap (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (index : Nat) (new : KemSK)
    (raw : Pqxdh.Bytes) (state : State KemSK) :
    (rawFinish setup wire parse index raw).run (swapNative index new state) =
      (finish setup (actualCodec wire parse index raw state) index raw).run (swapNative index new state) := by
  simpa only [rawFinish, StateT.run] using congrArg (fun codec : Codec Reader Response =>
    (finish setup codec index raw).run (swapNative index new state))
      (actualCodec_swap wire parse index raw new state)

/-- The actual dynamic raw CBOR finish, with its native parser and retained owner pin, is realized by the decapsulation oracle. -/
theorem rawFinish_interp (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) (old new : KemSK) (raw : Pqxdh.Bytes)
    (state : State KemSK) (held : Holds index old state.native.owners) :
    simulateQ (interp setup old) ((rawFinish setup wire parse index raw).run (swapNative index new state)) =
      Prod.map id (swapNative index new) <$>
        (CborProductionBoundary.handler setup wire parse checks created.seed (.inr (.finish index raw))).run state ∧
    ∀ result ∈ support ((CborProductionBoundary.handler setup wire parse checks created.seed (.inr (.finish index raw))).run state),
      Holds index old result.2.native.owners := by
  rw [rawFinish_swap, handler_finish]
  exact finish_interp setup (actualCodec wire parse index raw state) checks
    (RawCtxFrameDecoding.sender (CborProductionBoundary.nativeReader parse).model) created index old new raw state held


/-- One selected-owner finish makes at most one logical pre-challenge decapsulation query. -/
theorem rawFinish_decapsulations (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (index : Nat) (raw : Pqxdh.Bytes)
    (state : State KemSK) :
    ((rawFinish setup wire parse index raw).run state).IsQueryBoundP IsMlKemLogicalDecapsulationQuery 1 := by
  change ((finish setup (actualCodec wire parse index raw state) index raw).run state).IsQueryBoundP _ _
  rw [finish_run, isQueryBoundP_map_iff]
  exact PqxdhDeploymentIdealAnomalyGuesser.oracleFinish_decapsulate setup (actualCodec wire parse index raw state) index raw (virtual state)


end BeaconcryptCore.Computational.CborRawAnomalyOracle

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyOracle.finish_interp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyOracle.finish_interp
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyOracle.rawFinish_interp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyOracle.rawFinish_interp
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyOracle.rawFinish_decapsulations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyOracle.rawFinish_decapsulations
