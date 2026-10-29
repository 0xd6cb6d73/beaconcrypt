-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawKemTransfer
import BeaconcryptCore.Computational.CborRawHeadlineChain
import BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided

/-! Exact two-sided KEM transfer for the actual raw compiler. Its own accept/bundle trace proves key matching, so the reverse transfer introduces no discarded-session or mismatch term. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawKemTwoSided
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle ModeSpec Mode Budget FreshBounds)
open PqxdhDeploymentSecrecy (Ledger)
open CborAdmissionCompiler (Local)
open CborRawCompileSecrecy (compileFull)
open CborRawKemTransfer (decision)
open CborTaggedSimulation (boundaryWire)
open PqxdhDeploymentRegistrationTrace (traceFrom)
open PqxdhDeploymentKemTransfer (Observed happens designated selectedKem)
open PqxdhRegistrationJointAcceptCutTag (tag)
open PqxdhRegistrationJointKemRawBridge (Decided GoodKem KeyMatchFinal)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

/-- The actual raw decision proves both stopped-source secrecy and checked chosen-key matching. -/
theorem decision_implies (setup : Setup baseSpec KemSK) (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse)) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (event : Observed X → Bool)
    (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A)
    (final : PqxdhRegistrationJointKemRawBridge.Final KemSK A ((X × Ledger) × Local))
    (reached : final ∈ support ((fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome
      setup), result.2)) <$> (PqxdhRegistrationJointInitializedSchedule.source setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
        (tag (compileFull setup wire parse bounds mode adversary) g.1.val)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)))
    (decided : Decided (decision setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget event claim g) final) :
    GoodKem (selectedKem budget g) final ∧ KeyMatchFinal setup (CborRawCompile.sourceCodec wire parse) checks (selectedKem budget g) final := by
  have good := CborRawKemTransfer.approved_goodkem setup wire parse checks ensureInit bounds mode
    adversary g.1.val runtime (selectedKem budget g) final reached
  set work := compileFull setup wire parse bounds mode adversary with workEq
  set tagged := tag (traceFrom work []) g.1.val with taggedEq
  set start : PqxdhRegistrationJointServerPrefix.State KemSK A :=
    ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) with startEq
  have retagged : tag work g.1.val = (fun outcome => (outcome.1.1, outcome.2)) <$> tagged := by
    have mapped := PqxdhDeploymentRegistrationTrace.tag_map Prod.fst (traceFrom work []) g.1.val
    rw [PqxdhDeploymentRegistrationTrace.traceFrom_erase] at mapped
    exact mapped
  have rightRun : (PqxdhRegistrationJointInitializedSchedule.source setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
      (tag work g.1.val)).run start =
      (fun result => (result.1.map fun outcome => (outcome.1, (outcome.2.1.1.1, outcome.2.1.2), outcome.2.2),
        result.2)) <$> (PqxdhRegistrationJointInitializedSchedule.source setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none tagged).run
          start := by
    rw [retagged]
    exact PqxdhDeploymentRegistrationTrace.source_map setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none _ tagged start
  rw [rightRun, Functor.map_map, support_map] at reached
  obtain ⟨⟨_ | outcome, after⟩, member, rfl⟩ := reached
  · obtain ⟨_, found, _⟩ := decided
    cases found
  · obtain ⟨_, found, chosen, _⟩ := decided
    simp only [Option.map_some, Option.some.injEq] at found
    subst found
    obtain ⟨raw, value, tagEq, checked, keys⟩ := CborRawKemTransfer.keymatch_point setup wire parse checks
      ensureInit phase1 bounds mode adversary budget event claim g runtime outcome after member chosen
    exact ⟨good, _, raw, some g.1.val, value, rfl, tagEq, checked, keys⟩


/-- The original raw per-target event equals the actual raw-ordinal KEM real game. -/
theorem eligible_real (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
      designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget claim outcome = some g)) <$>
      (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime] {true} =
    𝒟[PqxdhRegistrationJointKemRawGame.sourceReal setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
      (decision setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget event claim g)
      (compileFull setup wire parse bounds mode adversary) runtime budget.create (selectedKem budget g) g.1.val] {true} := by
  rw [CborRawKemTransfer.eligible_actual setup wire parse checks lengths parser ensureInit phase1 phase2 bounds mode
    adversary budget event claim g runtime]
  exact PqxdhDeploymentKemTwoSided.actual_eq_real setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none _
    (compileFull setup wire parse bounds mode adversary) runtime (PqxdhDeploymentCompileCaps.transported bounds budget)
    (CborRawCompileCaps.certified setup wire parse bounds mode adversary budget respects) budget.create
    (selectedKem budget g) g.1.val (PqxdhDeploymentCompileCaps.transported_room bounds budget)
    fun final member decided _ => (decision_implies setup wire parse checks ensureInit phase1 bounds mode adversary
      budget event claim g runtime final member decided).2

/-- The actual raw event and opaque KEM ideal branch differ by the concrete certified IND-CCA advantage and correctness error. -/
theorem kem_transfer (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
      designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget claim outcome = some g)) <$>
      (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime] {true}).toReal -
      (𝒟[PqxdhRegistrationJointKemRawOpaque.opaqueBranch setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
        (decision setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget event claim g)
        (compileFull setup wire parse bounds mode adversary) runtime budget.create (selectedKem budget g) g.1.val false] {true}).toReal| ≤
      CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds mode adversary budget event claim g runtime := by
  rw [eligible_real setup wire parse checks lengths parser ensureInit phase1 phase2 bounds mode adversary budget respects
    event claim g runtime, ← PqxdhRegistrationJointKemRawOpaque.branchRaw_opaque]
  exact PqxdhRegistrationJointKemRawCertified.ideal_close setup functional (CborRawCompile.sourceCodec wire parse)
    checks ensureInit none _ _ runtime budget.create (selectedKem budget g) g.1.val

end BeaconcryptCore.Computational.CborRawKemTwoSided
/-- info: 'BeaconcryptCore.Computational.CborRawKemTwoSided.decision_implies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawKemTwoSided.decision_implies
/-- info: 'BeaconcryptCore.Computational.CborRawKemTwoSided.eligible_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawKemTwoSided.eligible_real
/-- info: 'BeaconcryptCore.Computational.CborRawKemTwoSided.kem_transfer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawKemTwoSided.kem_transfer
