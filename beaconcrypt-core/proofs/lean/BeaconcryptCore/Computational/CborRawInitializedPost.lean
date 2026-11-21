-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawSlotCut

/-! The active raw-CBOR slot handoff is discharged on actual initialized prefix outcomes. Ownership, creation residuals, owner positions, public assignment and the native reconstruction invariant are all derived from that one reached execution. The remaining premises are parser contracts and ordinary all-reply source budgets. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawInitializedPost
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealCut (CutCE)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
open PqxdhDeploymentIdealPostItemRun (afterSelected)
open CborRawInitializedCut (commonPrefix compilerCut)
variable {ι KemSK Reader Response A Y : Type} {baseSpec : OracleSpec ι}
section Active
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count)

/-- The complete selected branch uses the native raw continuation with no supplied source-to-native relation. Every cut invariant and remaining resource certificate is obtained from the actual initialized source prefix. -/
theorem active_prefix
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (ensureInit : StateT A ProbComp Bool) (runtime : A)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (bornState : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (born : (some created, bornState) ∈ support
      ((PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId none).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)))
    (work : OracleComp Spec Y) (event : Y × CborRawPostActive.Produced → Bool)
    (budget : SourceKind → Nat)
    (whole : ∀ kind, (CborRawCompile.compile setup wire parse work).IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = kind) (budget kind))
    (unreadIdentity : budget (.inr 0) = 0) (unreadKem : budget (.inr 1) = 0)
    (room : budget (.inl 1) ≤ (parameters.pool target).length)
    (reached : (CutCE Y × CborAdmissionCompiler.Local) × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : reached ∈ support
      (commonPrefix setup wire parse checks target parameters created bornState.1 work))
    (raw : Pqxdh.Bytes) (next : Option Nat → OracleComp Spec Y)
    (pending : reached.1.1 = .pending raw next) (value : PqxdhServerRootPreparation.Verified Reader)
    (verified : PqxdhRegistrationJointRawSignatures.verified setup (CborRawCompile.sourceCodec wire parse)
      checks raw = some value) (matched : value.keys.pqKey = parameters.chosen.1) :
    LazyOracleDiscard.LawEq
      (CborRawSlotCut.itemRest setup wire parse checks target parameters
        (fun result => event (result.1, result.2.copies.produced))
        (PqxdhRegistrationJointServerBirth.encode created) bornState.2 reached)
      ((simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup (CborRawCompile.sourceCodec wire parse) checks
          created.seed)
        (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := PqxdhBeaconPhase2Preparation.Word32) value)).run
          reached.2.shared.2.server.consumed >>= fun pre =>
        match pre.1.1 with
        | none => pure false
        | some ephemeral =>
          (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
            ((PqxdhDeploymentIdealActive.acceptAfter setup (CborRawCompile.sourceCodec wire parse) checks created.seed
              parameters.challenge value ephemeral pre.2 pre.1.2).run reached.2.shared)).run
                (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial) >>= fun selected =>
            (fun result => event (result.1, result.2.2.base.produced) && selected.1.1.1.1.isSome) <$>
              (simulateQ (CborRawMiddleSimulation.handler setup wire parse checks target parameters created)
                (next selected.1.1.1.1)).run
                (CborRawMiddleSimulation.merge (CborRawCompileCut.logAccept reached.1.2 raw selected.1.1.1.1)
                  (afterSelected target reached.2 selected))) := by
  have empty : bornState.1.2 = PqxdhLiveKemBirth.empty := by
    rw [(PqxdhRegistrationJointServerBirth.source_constructor setup.joint ensureInit setup.serverKeyId none
      _ bornState created born).1]
    rfl
  have slot := PqxdhRegistrationJointServerBirth.source_owned setup.joint ensureInit setup.serverKeyId none
    _ bornState created born
  have identity := PqxdhRegistrationJointInitializedAccept.source_public setup.joint ensureInit setup.serverKeyId none
    _ bornState created born
  have good := CborRawInitializedCut.cut_good setup wire parse checks target parameters created phase1 phase2
    ensureInit none _ bornState born work reached supported
  have certified := fun kind => PqxdhRegistrationJointAcceptCut.scan_bound _ target.accept _ _ (whole kind)
  have owned := CborRawCutRelations.cut_owned setup wire parse checks target parameters created bornState.1 empty slot
    work reached supported
  have prefixed := (CborRawCutRelations.cut_prefix setup wire parse checks target parameters created bornState.1
    empty slot work budget certified room reached supported).1
  have indexed := CborRawCutRelations.cut_indexed setup wire parse checks target parameters created bornState.1
    empty slot work reached supported
  have cutEq : compilerCut setup wire parse reached.1 =
      .pending raw (CborRawPostActive.compiledNext setup wire parse raw next reached.1.2) := by
    rcases reached with ⟨⟨cut, memory⟩, state⟩
    simp only at pending
    subst pending
    rfl
  have residual := (CborRawCutRelations.cut_residual setup wire parse checks target parameters created bornState.1
    empty work budget whole reached supported).2 raw _ cutEq
  have onlyAllowed : ∀ answer, (CborRawPostActive.compiledNext setup wire parse raw next reached.1.2 answer).IsQueryBoundP
      (fun query => ¬ PqxdhDeploymentIdealPostInvariant.Allowed (KemSK := KemSK) query) 0 := by
    intro answer
    have first := residual answer (.inr 0)
    have second := residual answer (.inr 1)
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne, unreadIdentity, unreadKem] at first second
    refine (isQueryBoundP_congr_pred (fun query => ?_)).mpr
      (PqxdhDeploymentIdealPostSource.bound_or_zero _ _ _ first second)
    simp only [PqxdhDeploymentIdealPostInvariant.Allowed, not_and_or, not_not]
  have bounded : ∀ answer, (CborRawPostActive.compiledNext setup wire parse raw next reached.1.2 answer).IsQueryBoundP
      (PqxdhDeploymentIdealPostInvariant.Costly (KemSK := KemSK))
      (budget (.inl 1) - reached.2.pool.2.keys.length) := by
    intro answer
    have creations := residual answer (.inl 1)
    simp only [Function.update_self] at creations
    exact creations
  refine (CborRawSlotCut.itemRest_selected setup wire parse checks target parameters _ _ bornState.2 reached raw next
    pending value verified created.seed).trans (LazyOracleDiscard.LawEq.of_eq ?_)
  refine bind_congr fun pre => ?_
  rcases pre with ⟨⟨_ | ephemeral, logged⟩, consumed⟩
  · rfl
  · exact CborRawPostActive.itemPost_native setup wire parse checks target parameters phase1 phase2 event created
      identity raw reached.1.2 reached.2 good value verified matched ephemeral consumed logged owned prefixed indexed
      next onlyAllowed _ bounded (Nat.sub_le_sub_right room _) bornState.2

end Active
end BeaconcryptCore.Computational.CborRawInitializedPost

/-- info: 'BeaconcryptCore.Computational.CborRawInitializedPost.active_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawInitializedPost.active_prefix
