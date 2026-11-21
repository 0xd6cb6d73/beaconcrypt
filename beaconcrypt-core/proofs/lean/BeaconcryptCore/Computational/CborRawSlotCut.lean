-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawPostActive
import BeaconcryptCore.Computational.CborRawCutRelations

/-! Item 2's complete raw-CBOR slot game is factored at the same adaptive accept cut as the native prefix. Failed construction, stopped execution, completed runs, off-target verified keys and pre-encapsulation rejection are accounted for explicitly. The active branch uses the actual native preparation and retains the raw compiler's complete continuation state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.CborRawSlotCut
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhServerRootPreparation (Verified)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealCut (CutCE)
open PqxdhRegistrationJointGeneratedFinish (encodeState)
open PqxdhRegistrationJointKemEntryFactor (Output factoredServices publicLocalV)
open CborRawPostItemGeneric (itemPost)
open PqxdhDeploymentIdealBranch (optionRun_support rejectRun_complete)
open LazyOracleDiscard (LawEq)
variable {ι KemSK Reader Response A Y : Type} {baseSpec : OracleSpec ι}
section Slot
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (t : Target count) (p : Params KemSK count) (decision : Y × CborAdmissionCompiler.Local → Bool)

noncomputable def itemRest (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (after : A)
    (reached : (CutCE Y × CborAdmissionCompiler.Local) × PqxdhRegistrationJointSchedule.State KemSK) : ProbComp Bool :=
  ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem t.kem.val (p.pool t))
      (PqxdhDeploymentIdealCut.opaqueRest setup (CborRawCompile.sourceCodec wire parse) checks created.server.server.metadata.identityIndex
        created.publicIdentity (PqxdhRegistrationJointAcceptCutTag.decideTag decision)
        ((CborRawInitializedCut.compilerCut setup wire parse reached.1,
          ((PqxdhRegistrationJointGeneratedFinish.encodeState setup reached.2).owners, (PqxdhRegistrationJointGeneratedFinish.encodeState setup reached.2).inits)), reached.2.shared))).run).run
      (reached.2.pool.1, PqxdhDeploymentIdealPoolSource.routerOf reached.2.pool.2) >>= fun result =>
    itemPost setup (CborRawCompile.sourceCodec wire parse) checks t p decision (.ready created p.others result.1 result.2 after)


theorem slotGameAt_cut (ensureInit : StateT A ProbComp Bool) (work : OracleComp Spec Y) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (certified : ∀ source, (PqxdhRegistrationJointAcceptCut.scan (CborRawCompile.compile setup wire parse work)
      t.accept).IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (unreadIdentity : budget (.inr 0) = 0) (unreadKem : budget (.inr 1) = 0)
    (room : budget (.inl 1) ≤ (p.pool t).length) :
    PqxdhDeploymentIdealParams.slotGameAt (Reader := Reader) setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none decision
        (CborRawCompile.compile setup wire parse work) runtime count t.kem t.accept 2 p =
      (PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId none).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) >>= fun born =>
        match born.1 with
        | none => itemPost setup (CborRawCompile.sourceCodec wire parse) checks t p decision (.failed born.2)
        | some created =>
            CborRawInitializedCut.commonPrefix setup wire parse checks t p created born.2.1 work >>= fun reached =>
              itemRest setup wire parse checks t p decision (PqxdhRegistrationJointServerBirth.encode created) born.2.2
                reached := by
  unfold PqxdhDeploymentIdealParams.slotGameAt PqxdhDeploymentIdealParams.entryClientAt
  rw [PqxdhDeploymentIdealParams.internalize_run]
  unfold PqxdhDeploymentIdealParams.startPool
  rw [bind_assoc]
  simp only [pure_bind]
  rw [CborRawInitializedCut.item2_prefix setup wire parse checks t p ensureInit decision work runtime budget certified
    unreadIdentity unreadKem room, bind_assoc]
  refine bind_congr fun born => ?_
  rcases born with ⟨_ | created, after⟩
  · simp only [pure_bind]
    rfl
  · simp only [bind_assoc, pure_bind]
    rfl


theorem itemPost_failed (state : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    itemPost setup (CborRawCompile.sourceCodec wire parse) checks t p decision (.failed state) = pure false := by
  simp only [itemPost, PqxdhRegistrationJointKemPostSkeleton.postSkel, simulateQ_pure, StateT.run'_eq, StateT.run_pure,
    map_pure]

/-- Item 2's post-challenge phase accepts nothing on a prechallenge context without an active cut at the selected PQ key: a stopped run, a completed run, or a cut whose verified PQ key is not the selected one. -/
theorem itemPost_dead (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit)
    (cut : Option (PqxdhRegistrationJointKemRawOpaque.OpaqueCut Reader KemSK (Y × CborAdmissionCompiler.Local) Bool))
    (state : PqxdhDynamicKemJointSource.State KemSK) (after : A)
    (dead : ∀ raw value ephemeral consumed native owners next,
      cut = some (.pending raw value ephemeral consumed native owners next) → value.keys.pqKey ≠ p.chosen.1) :
    itemPost setup (CborRawCompile.sourceCodec wire parse) checks t p decision (.ready created p.others cut state after) = pure false := by
  rcases cut with _ | (outcome | ⟨raw, value, ephemeral, consumed, native, owners, next⟩)
  · simp only [itemPost, PqxdhRegistrationJointKemPostSkeleton.postSkel, simulateQ_pure, StateT.run'_eq, StateT.run_pure,
      map_pure]
  · simp only [itemPost, PqxdhRegistrationJointKemPostSkeleton.postSkel, simulateQ_pure, StateT.run'_eq, StateT.run_pure,
      map_pure]
  · have other := dead raw value ephemeral consumed native owners next rfl
    simp only [itemPost, PqxdhRegistrationJointKemPostSkeleton.postSkel, other, ↓reduceIte, simulateQ_pure,
      StateT.run'_eq, StateT.run_pure, map_pure]


theorem opaqueRest_dead {R : Type} (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (observe : (Y × CborAdmissionCompiler.Local) × PqxdhRegistrationJointAcceptCutTag.Tag → R) (cutCE : CutCE Y) (copies : CborAdmissionCompiler.Local)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × (Nat → Option PqxdhEd25519EufCma.Phase1Candidate))
    (state : PqxdhServerAuthNative.NativeState KemSK)
    (dead : ∀ raw next, cutCE = .pending raw next → ∀ value,
      PqxdhRegistrationJointRawSignatures.verified setup (CborRawCompile.sourceCodec wire parse) checks raw = some value → value.keys.pqKey ≠ p.chosen.1)
    (cut : PqxdhRegistrationJointKemRawOpaque.OpaqueCut Reader KemSK (Y × CborAdmissionCompiler.Local) R)
    (member : cut ∈ support (PqxdhDeploymentIdealCut.opaqueRest setup (CborRawCompile.sourceCodec wire parse) checks identityIndex publicIdentity observe
      ((CborRawInitializedCut.compilerCut setup wire parse (cutCE, copies), owners), state))) :
    ∀ raw value ephemeral consumed native owners' next,
      cut = .pending raw value ephemeral consumed native owners' next → value.keys.pqKey ≠ p.chosen.1 := by
  intro raw value ephemeral consumed native owners' next same
  subst same
  rcases cutCE with result | ⟨raw0, next0⟩
  · simp [PqxdhDeploymentIdealCut.opaqueRest, CborRawInitializedCut.compilerCut, CborRawCompileCut.cut] at member
  · unfold PqxdhDeploymentIdealCut.opaqueRest at member
    simp only [CborRawInitializedCut.compilerCut, CborRawCompileCut.cut] at member
    rcases found : PqxdhRegistrationJointRawSignatures.verified setup (CborRawCompile.sourceCodec wire parse) checks raw0 with _ | verified
    · rw [found] at member
      obtain ⟨outcome, impossible⟩ := rejectRun_complete setup (CborRawCompile.sourceCodec wire parse) checks _ _ _ _ _ _ _ _ _ member
      cases impossible
    · rw [found] at member
      simp only [mem_support_bind_iff] at member
      obtain ⟨prepared, -, member⟩ := member
      split at member
      · obtain ⟨outcome, impossible⟩ := rejectRun_complete setup (CborRawCompile.sourceCodec wire parse) checks _ _ _ _ _ _ _ _ _ member
        cases impossible
      · rw [support_pure, Set.mem_singleton_iff] at member
        injection member with sameRaw sameValue
        subst sameValue
        exact dead raw0 next0 rfl _ found


theorem itemRest_dead (decision : Y × CborAdmissionCompiler.Local → Bool) (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit)
    (after : A) (reached : (CutCE Y × CborAdmissionCompiler.Local) × PqxdhRegistrationJointSchedule.State KemSK)
    (dead : ∀ raw next, reached.1.1 = .pending raw next → ∀ value,
      PqxdhRegistrationJointRawSignatures.verified setup (CborRawCompile.sourceCodec wire parse) checks raw = some value → value.keys.pqKey ≠ p.chosen.1) :
    LawEq (itemRest (Reader := Reader) setup wire parse checks t p decision created after reached) (pure false) := by
  unfold itemRest
  refine (PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun result member => LawEq.of_eq
    (itemPost_dead setup wire parse checks t p decision created result.1 result.2 after ?_)).trans
    (LazyOracleDiscard.lawEq_drop _ _)
  intro raw value ephemeral consumed native owners next found
  have produced := optionRun_support _ _ _ result member _ found
  exact opaqueRest_dead setup wire parse checks p _ _ _ reached.1.1 reached.1.2 _ _ dead _ produced raw value ephemeral
    consumed native owners next rfl


theorem itemRest_selected {A Y : Type} (t : Target count) (p : Params KemSK count) (decision : Y × CborAdmissionCompiler.Local → Bool)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (after : A)
    (reached : (CutCE Y × CborAdmissionCompiler.Local) × PqxdhRegistrationJointSchedule.State KemSK) (raw : Pqxdh.Bytes)
    (next : Option ℕ → OracleComp Spec Y) (pending : reached.1.1 = .pending raw next) (value : Verified Reader)
    (verified : PqxdhRegistrationJointRawSignatures.verified setup (CborRawCompile.sourceCodec wire parse) checks raw = some value)
    (seed : PqxdhJointIdentity.IdentitySeed) :
    LazyOracleDiscard.LawEq
      (itemRest (Reader := Reader) setup wire parse checks t p decision created after reached)
      ((simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup (CborRawCompile.sourceCodec wire parse) checks seed)
          (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := PqxdhBeaconPhase2Preparation.Word32) value)).run
          reached.2.shared.2.server.consumed >>= fun pre =>
        match pre.1.1 with
        | none => pure false
        | some ephemeral => itemPost setup (CborRawCompile.sourceCodec wire parse) checks t p decision
            (.ready created p.others (some (.pending raw value ephemeral pre.2 reached.2.shared
              ((PqxdhRegistrationJointGeneratedFinish.encodeState setup reached.2).owners, (PqxdhRegistrationJointGeneratedFinish.encodeState setup reached.2).inits)
              (CborRawPostActive.compiledNext setup wire parse raw next reached.1.2)))
              (reached.2.pool.1, PqxdhDeploymentIdealPoolSource.routerOf reached.2.pool.2) after)) := by
  rcases reached with ⟨⟨cut, copies⟩, source⟩
  simp only at pending
  subst pending
  unfold itemRest
  rw [CborRawPostActive.opaqueRest_selected setup wire parse checks _ _ _ raw next copies _ _ value verified seed, bind_assoc]
  refine PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun pre _ => ?_
  rcases pre with ⟨⟨_ | ephemeral, logged⟩, consumed⟩
  · refine (PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun result member => LazyOracleDiscard.LawEq.of_eq
      (itemPost_dead setup wire parse checks t p decision created result.1 result.2 after ?_)).trans
      (LazyOracleDiscard.lawEq_drop _ _)
    intro raw' value' ephemeral' consumed' native' owners' next' found
    have produced := PqxdhDeploymentIdealBranch.optionRun_support _ _ _ result member _ found
    obtain ⟨outcome, impossible⟩ := PqxdhDeploymentIdealBranch.rejectRun_complete setup (CborRawCompile.sourceCodec wire parse) checks _ _ _ _ _ _ _ _ _
      produced
    cases impossible
  · simp only [pure_bind]
    exact LazyOracleDiscard.LawEq.refl _

end Slot
end BeaconcryptCore.Computational.CborRawSlotCut

/-- info: 'BeaconcryptCore.Computational.CborRawSlotCut.slotGameAt_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawSlotCut.slotGameAt_cut

/-- info: 'BeaconcryptCore.Computational.CborRawSlotCut.itemPost_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawSlotCut.itemPost_failed

/-- info: 'BeaconcryptCore.Computational.CborRawSlotCut.itemPost_dead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawSlotCut.itemPost_dead

/-- info: 'BeaconcryptCore.Computational.CborRawSlotCut.opaqueRest_dead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawSlotCut.opaqueRest_dead

/-- info: 'BeaconcryptCore.Computational.CborRawSlotCut.itemRest_dead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawSlotCut.itemRest_dead

/-- info: 'BeaconcryptCore.Computational.CborRawSlotCut.itemRest_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawSlotCut.itemRest_selected
