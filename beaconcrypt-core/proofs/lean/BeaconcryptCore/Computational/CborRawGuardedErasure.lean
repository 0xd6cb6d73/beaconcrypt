-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawNativePublic

/-! CTX completion erasure for arbitrary early-admission native clients, with independent registration and record codecs. Refusal depends on actual send cursors and is unchanged by completing the shared cache. The concrete ideal registration instance uses the existing proved pointed service, rather than taking an erasure or whole-game simulation premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawGuardedErasure
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentBackend (XState ctxLens)
open PqxdhDeploymentFinishErasure (FinishPair fullX fullX_set pointedWith pointedWith_factor pointedWith_erased
  pointedWith_oblivious)
open LazyOracleDiscard (Commutes LawEq)
variable {ι KemSK Reader Response Bk Result : Type} {baseSpec : OracleSpec ι} {n : Nat}
section Erasure
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

noncomputable def pointed (pair : FinishPair KemSK Bk n) (query : Spec.Domain) :
    StateT (XState KemSK Bk n) ProbComp (Spec.Range query × Option CtxRomAuth.CtxRO.Domain) := fun state =>
  match CborRawGuardedJoin.refusal (n := n) query (CborRecordNativeAdmission.nativeShell state.base) with
  | some reply => pure ((reply, none), state)
  | none => (pointedWith setup codec route pair query).run state

private theorem map_state_apply {Input Output : Type} (f : Input → Output)
    (work : StateT (XState KemSK Bk n) ProbComp Input) (state : XState KemSK Bk n) :
    (f <$> work) state = Prod.map f id <$> work state :=
  bind_pure_comp (Prod.map f id) (work state)

private theorem factor (pair : FinishPair KemSK Bk n) (query : Spec.Domain) (state : XState KemSK Bk n) :
    LawEq ((CborRawGuardedJoin.nativeHandler setup codec route pair.reg query).run state)
      ((pointed setup codec route pair query).run state >>= fun value =>
        (value.1.1, ·) <$> ctxLens.completeOpt value.1.2 value.2) := by
  cases refused : CborRawGuardedJoin.refusal (n := n) query (CborRecordNativeAdmission.nativeShell state.base) with
  | none =>
      simpa only [CborRawGuardedJoin.nativeHandler, pointed, StateT.run, refused] using
        pointedWith_factor setup codec route pair query state
  | some reply =>
      apply LawEq.of_eq
      simp only [CborRawGuardedJoin.nativeHandler, pointed, StateT.run, refused, pure_bind,
        LazyOracleDiscard.StateLens.completeOpt, map_pure]

private theorem erased (pair : FinishPair KemSK Bk n) :
    (fun query => Prod.fst <$> pointed setup codec route pair query : QueryImpl Spec _) =
      CborRawGuardedJoin.nativeHandler setup codec route pair.erased := by
  funext query
  apply StateT.ext
  intro state
  cases refused : CborRawGuardedJoin.refusal (n := n) query (CborRecordNativeAdmission.nativeShell state.base) with
  | some reply =>
      simp only [map_state_apply, pointed, StateT.run, refused, map_pure, CborRawGuardedJoin.nativeHandler]
      rfl
  | none =>
      have old := congrArg (fun implementation => (implementation query).run state)
        (pointedWith_erased setup codec route pair)
      simpa only [map_state_apply, pointed, StateT.run_map, StateT.run, refused, CborRawGuardedJoin.nativeHandler] using old

private theorem oblivious (pair : FinishPair KemSK Bk n) (query : Spec.Domain) :
    Commutes ctxLens (Prod.fst <$> pointed setup codec route pair query) := by
  let choose : Option (Spec.Range query) → StateT (XState KemSK Bk n) ProbComp (Spec.Range query) :=
    fun value => match value with
    | some reply => pure reply
    | none => Prod.fst <$> pointedWith setup codec route pair query
  apply PqxdhDeploymentBackend.commutes_dispatch ctxLens _
    (fun state => CborRawGuardedJoin.refusal (n := n) query (CborRecordNativeAdmission.nativeShell state.base))
    (fun _ _ => rfl) choose
  · intro state
    cases refused : CborRawGuardedJoin.refusal (n := n) query (CborRecordNativeAdmission.nativeShell state.base) <;>
      simp only [map_state_apply, pointed, StateT.run, refused, choose, map_pure]; rfl
  · intro value
    cases value with
    | some reply => exact LazyOracleDiscard.commutes_pure ctxLens reply
    | none =>
        exact pointedWith_oblivious setup codec route pair
          (fun query => PqxdhDeploymentBackend.fixed_commute_ctx setup codec route pair.reg query) query

/-- Completing unused CTX points can be erased from every adaptive guarded native client. The client may already contain the unchanged secrecy sampling and raw public adapter. -/
theorem erase (pair : FinishPair KemSK Bk n) (work : OracleComp Spec Result) (state : XState KemSK Bk n) :
    LawEq (Prod.map id fullX <$>
        (simulateQ (CborRawGuardedJoin.nativeHandler setup codec route pair.reg) work).run state)
      (Prod.map id fullX <$>
        (simulateQ (CborRawGuardedJoin.nativeHandler setup codec route pair.erased) work).run state) := by
  have result := LazyOracleDiscard.discard_erase_proj ctxLens
    (CborRawGuardedJoin.nativeHandler setup codec route pair.reg) (pointed setup codec route pair)
    (factor setup codec route pair) (oblivious setup codec route pair) fullX fullX_set work state
  rw [erased] at result
  exact result

end Erasure
section Ideal
open PqxdhDeploymentIdealParams (Target Params)
variable {SourceReader SourceResponse : Type}

/-- Concrete ideal registration erasure under independent record and registration codecs, with actual native admission on every record command. -/
theorem ideal_erase (setup : Setup baseSpec KemSK) (recordCodec : Codec Reader Response)
    (sourceCodec : Codec SourceReader SourceResponse) (route : RawCtxServerRouting.SenderDecoder) (checks : Checks)
    {count : Nat} (target : Target count) (parameters : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (work : OracleComp Spec Result)
    (state : XState KemSK (PqxdhDeploymentIdealSteps.IdealBk PqxdhDeploymentIdealSteps.TableState) 2) :
    LawEq (Prod.map id fullX <$>
        (simulateQ (CborRawGuardedJoin.nativeHandler setup recordCodec route
          (PqxdhDeploymentIdealSteps.idealReg setup sourceCodec route checks target parameters created)) work).run state)
      (Prod.map id fullX <$>
        (simulateQ (CborRawGuardedJoin.nativeHandler setup recordCodec route
          (PqxdhDeploymentIdealSteps.idealCoreErased setup sourceCodec route checks target parameters
            PqxdhDeploymentSeedSplit.tableService created)) work).run state) := by
  simpa only [PqxdhDeploymentIdealErase.idealPair_reg, PqxdhDeploymentIdealErase.idealPair_erased,
    PqxdhDeploymentIdealSteps.idealReg] using
    erase setup recordCodec route
      (PqxdhDeploymentIdealErase.idealPair setup sourceCodec route checks target parameters
        PqxdhDeploymentSeedSplit.tableService created) work state

end Ideal
end BeaconcryptCore.Computational.CborRawGuardedErasure

/-- info: 'BeaconcryptCore.Computational.CborRawGuardedErasure.erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawGuardedErasure.erase
/-- info: 'BeaconcryptCore.Computational.CborRawGuardedErasure.ideal_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawGuardedErasure.ideal_erase
