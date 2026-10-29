-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawCutBranches

/-! The complete initialized raw source slot game equals the independently defined native raw ideal game with its actual selected-session mark. All source-prefix invariants, resource residuals, active callbacks, failure and off-target branches are discharged from the reached execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawInitializedSlot
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealCut (CutCE)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
open CborRawPublicState (Public ofMemory)
open LazyOracleDiscard (LawEq)
variable {ι KemSK Reader Response A Result : Type} {baseSpec : OracleSpec ι}
section Slot
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count)

theorem item_rest
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (ensureInit : StateT A ProbComp Bool) (runtime : A)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (born : (some created, after) ∈ support
      ((PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId none).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)))
    (work : OracleComp Spec Result) (event : Result × CborRawPostActive.Produced → Bool)
    (budget : SourceKind → Nat)
    (whole : ∀ kind, (CborRawCompile.compile setup wire parse work).IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = kind) (budget kind))
    (unreadIdentity : budget (.inr 0) = 0) (unreadKem : budget (.inr 1) = 0)
    (room : budget (.inl 1) ≤ (parameters.pool target).length)
    (reached : (CutCE Result × CborAdmissionCompiler.Local) × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : reached ∈ support
      (CborRawInitializedCut.commonPrefix setup wire parse checks target parameters created after.1 work)) :
    LawEq (CborRawSlotCut.itemRest setup wire parse checks target parameters
        (fun result => event (result.1, result.2.copies.produced))
        (PqxdhRegistrationJointServerBirth.encode created) after.2 reached)
      (CborRawMarkedPrefix.resume setup wire parse checks target parameters created event reached.1.1
        (CborRawPrefixHandoff.atCut target created reached)) := by
  cases cut : reached.1.1 with
  | complete result =>
      refine (CborRawSlotCut.itemRest_dead setup wire parse checks target parameters _ _ after.2 reached ?_).trans ?_
      · intro raw next pending
        rw [cut] at pending
        cases pending
      · exact LawEq.of_eq rfl
  | pending raw next =>
      by_cases active : ∃ value, PqxdhRegistrationJointRawSignatures.verified setup
          (CborRawCompile.sourceCodec wire parse) checks raw = some value ∧ value.keys.pqKey = parameters.chosen.1
      · obtain ⟨value, verified, matched⟩ := active
        refine (CborRawInitializedPost.active_prefix setup wire parse checks target parameters phase1 phase2 ensureInit
          runtime created after born work event budget whole unreadIdentity unreadKem room reached supported raw next cut
          value verified matched).trans ?_
        exact (CborRawCutBranches.selected_resume setup wire parse checks target parameters created event reached.1.2
          reached.2 raw next value verified matched).symm
      · have inactive : ∀ value, PqxdhRegistrationJointRawSignatures.verified setup
            (CborRawCompile.sourceCodec wire parse) checks raw = some value → value.keys.pqKey ≠ parameters.chosen.1 := by
          intro value verified matched
          exact active ⟨value, verified, matched⟩
        refine (CborRawSlotCut.itemRest_dead setup wire parse checks target parameters _ _ after.2 reached ?_).trans ?_
        · intro raw' next' pending value verified
          rw [cut] at pending
          cases pending
          exact inactive value verified
        · exact (CborRawMarkedBranch.resume_dead setup wire parse checks target parameters created event raw next
            (CborRawPrefixHandoff.atCut target created reached) rfl inactive).symm

/-- The full initialized slot game has the marked native raw ideal law, for every observation of the result and produced frames. -/
theorem slot_native
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (ensureInit : StateT A ProbComp Bool) (runtime : A)
    (work : OracleComp Spec Result) (event : Result × CborRawPostActive.Produced → Bool)
    (budget : SourceKind → Nat)
    (whole : ∀ kind, (CborRawCompile.compile setup wire parse work).IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = kind) (budget kind))
    (unreadIdentity : budget (.inr 0) = 0) (unreadKem : budget (.inr 1) = 0)
    (room : budget (.inl 1) ≤ (parameters.pool target).length) :
    LawEq (PqxdhDeploymentIdealParams.slotGameAt (Reader := Reader) setup (CborRawCompile.sourceCodec wire parse) checks
        ensureInit none (fun result => event (result.1, result.2.copies.produced))
        (CborRawCompile.compile setup wire parse work) runtime count target.kem target.accept 2 parameters)
      ((PqxdhRegistrationJointServerBirth.source (KemSK := KemSK) setup.joint ensureInit setup.serverKeyId none).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) >>= fun born =>
        match born.1 with
        | none => pure false
        | some created => CborRawMarkedPrefix.run setup wire parse checks target parameters created work event
            (ofMemory (CborAdmissionCompiler.Local.empty setup.serverKeyId),
              PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created))) := by
  refine (LawEq.of_eq (CborRawSlotCut.slotGameAt_cut setup wire parse checks target parameters _ ensureInit work runtime
    budget (fun kind => PqxdhRegistrationJointAcceptCut.scan_bound _ target.accept _ _ (whole kind)) unreadIdentity
    unreadKem room)).trans ?_
  refine PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun born supported => ?_
  rcases born with ⟨_ | created, after⟩
  · exact LawEq.of_eq (CborRawSlotCut.itemPost_failed setup wire parse checks target parameters _ after)
  · dsimp only
    rw [CborRawMarkedPrefix.common_prefix setup wire parse checks target parameters created phase1 phase2 ensureInit
      none _ after supported work event]
    exact PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun reached member =>
      item_rest setup wire parse checks target parameters phase1 phase2 ensureInit runtime created after supported work
        event budget whole unreadIdentity unreadKem room reached member

end Slot
end BeaconcryptCore.Computational.CborRawInitializedSlot

/-- info: 'BeaconcryptCore.Computational.CborRawInitializedSlot.item_rest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawInitializedSlot.item_rest
/-- info: 'BeaconcryptCore.Computational.CborRawInitializedSlot.slot_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawInitializedSlot.slot_native
