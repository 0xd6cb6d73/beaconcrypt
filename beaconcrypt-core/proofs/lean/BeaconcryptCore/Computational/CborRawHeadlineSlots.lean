-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawHeadlineWorld

/-! Per-target slot restriction on the actual raw record view. Any failure of the full native slot conditions is charged to the concrete early-finish event on the same raw transcript. The explicit anomaly event remains available to the native ciphertext predictor bound. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawHeadlineSlots
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget Handle)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealHandoff (viewObserved decisionOn evalDist_le_add)
open PqxdhRecordLiftIdeal (View chainView)
open PqxdhDeploymentIdealTrace (IdealSlots Anomaly)
open CborTaggedSimulation (boundaryWire)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

noncomputable def environment (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (ensureInit : StateT A ProbComp Bool) (runtime : A) :=
  CborRawEnvironment.environment
    (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks target ensureInit 0 runtime)
      setup.serverKeyId

noncomputable def realView (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (ensureInit : StateT A ProbComp Bool) (runtime : A) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :=
  chainView <$> PqxdhRecordLiftLaterWorlds.chainsOf (fun _ => false) setup (boundaryWire wire parse)
    (CborRawCompile.route parse) (CborRawRecordLiftBounds.client
      (environment setup wire parse checks target ensureInit runtime) setup.source.crypto (boundaryWire wire parse)
        setup.serverKeyId bounds mode adversary)

open Classical in
noncomputable def anomaly (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) {count : Nat} (target : Target count)
    {E : Type} (view : View 2 E X) : Bool :=
  decide (∃ value, view.result = some value ∧
    Anomaly setup.source.crypto (boundaryWire wire parse) setup.serverKeyId target value.2.1.transcript)

open Classical in
/-- Every unslotted raw event is covered by the actual early-finish anomaly on the same complete permitted view. -/
theorem split (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (ensureInit : StateT A ProbComp Bool) (runtime : A) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (event : Observed X → Bool)
    (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun view => (viewObserved view).any (decisionOn setup (boundaryWire wire parse) budget event claim g)) <$>
      realView setup wire parse checks (Target.ofCE budget g) ensureInit runtime bounds mode adversary] {true} ≤
    𝒟[PqxdhDeploymentHeadlineChain.slotted setup (boundaryWire wire parse) budget event claim g <$>
      realView setup wire parse checks (Target.ofCE budget g) ensureInit runtime bounds mode adversary] {true} +
    𝒟[anomaly setup wire parse (Target.ofCE budget g) <$>
      realView setup wire parse checks (Target.ofCE budget g) ensureInit runtime bounds mode adversary] {true} := by
  refine Eq.trans_le ?_ (evalDist_le_add _ (fun view => (viewObserved view).any
    (decisionOn setup (boundaryWire wire parse) budget event claim g) = true) _ _ fun view member held => ?_)
  · simp only [Bool.decide_eq_true]
  rw [realView, support_map] at member
  obtain ⟨result, resultMember, rfl⟩ := member
  by_cases slotted : ∀ value, (chainView result).result = some value →
      IdealSlots setup.source.crypto (boundaryWire wire parse) setup.serverKeyId (Target.ofCE budget g)
        (chainView result).slots value.2.1.transcript
  · exact Or.inl ⟨held, slotted⟩
  · obtain ⟨value, unslotted⟩ := Classical.not_forall.mp slotted
    obtain ⟨found, failed⟩ := Classical.not_imp.mp unslotted
    exact Or.inr ⟨value, found, (CborRawRecordProvenance.real_slots_or_anomaly setup wire parse checks phase1 phase2
      (Target.ofCE budget g) ensureInit 0 runtime bounds mode adversary result resultMember value found).resolve_left failed⟩

/-- The actual raw-CBOR source security chain reaches its actual slotted raw record view and concrete anomaly. -/
theorem chain_slots (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (target : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
      designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget claim outcome = some target)) <$>
      (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[PqxdhDeploymentHeadlineChain.slotted setup (boundaryWire wire parse) budget event claim target <$>
        realView setup wire parse checks (Target.ofCE budget target) ensureInit runtime bounds mode adversary] {true} +
      𝒟[anomaly setup wire parse (Target.ofCE budget target) <$>
        realView setup wire parse checks (Target.ofCE budget target) ensureInit runtime bounds mode adversary] {true} +
      ENNReal.ofReal (CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds mode adversary budget event claim target runtime) +
      ENNReal.ofReal (CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds mode adversary budget event claim target runtime) := by
  have source := CborRawHeadlineWorld.chain_real setup functional wire parse checks lengths parser ensureInit phase1
    phase2 correct bounds mode adversary budget respects event claim target runtime
  have slots := split setup wire parse checks nativePhase1 phase2 ensureInit runtime bounds mode adversary budget event
    claim target
  exact source.trans (add_le_add (add_le_add slots le_rfl) le_rfl)

/-- The actual raw Server-side chain has its proved Server slot conditions with no native early-finish anomaly term. -/
theorem chain_server (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (nativePhase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (target : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
      designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget claim outcome = some target)) <$>
      (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[PqxdhDeploymentHeadlineChain.serverSlotted setup (boundaryWire wire parse) budget event claim target <$>
        realView setup wire parse checks (Target.ofCE budget target) ensureInit runtime bounds mode adversary] {true} +
      ENNReal.ofReal (CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds mode adversary budget event claim target runtime) +
      ENNReal.ofReal (CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds mode adversary budget event claim target runtime) := by
  classical
  refine (CborRawHeadlineWorld.chain_real setup functional wire parse checks lengths parser ensureInit phase1 phase2
    correct bounds mode adversary budget respects event claim target runtime).trans_eq ?_
  unfold realView
  congr 3
  rw [Functor.map_map, Functor.map_map]
  congr 1
  refine PqxdhDeploymentKemTransfer.map_support_congr _ _ _ fun result member => ?_
  simp only [PqxdhDeploymentHeadlineChain.serverSlotted]
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact ⟨fun held => ⟨held, CborRawRecordProvenance.real_server_slots setup wire parse checks nativePhase1 phase2
    (Target.ofCE budget target) ensureInit 0 runtime bounds mode adversary result member⟩, And.left⟩

end BeaconcryptCore.Computational.CborRawHeadlineSlots

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineSlots.split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineSlots.split

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineSlots.chain_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineSlots.chain_slots

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineSlots.chain_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineSlots.chain_server
