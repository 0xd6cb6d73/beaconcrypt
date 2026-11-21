-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawHeadlineChain
import BeaconcryptCore.Computational.CborRawHeadlineSlot
import BeaconcryptCore.Computational.CborRawRecordProvenance

/-! The raw source cryptographic chain reaches the actual complete permitted raw record view. The proof retains the original raw-CBOR ledger and all challenger draws. Its two primitive losses are instantiated by the concrete raw compiler and its proved caps. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawHeadlineWorld
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (Environment)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget Handle)
open PqxdhDeploymentKemTransfer (Observed happens designated selectedKem)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealHandoff (viewObserved decisionOn annotatedView)
open PqxdhRecordLiftIdeal (chainView)
open CborTaggedSimulation (boundaryWire)
variable {n : Nat} {ι KemSK Reader Response A E X : Type} {baseSpec : OracleSpec ι}

/-- The raw early-admission World's complete event projection equals that of the real cursor-compiled record world. -/
theorem real_event (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (event : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced → Bool) :
    (fun result : PqxdhRecordLiftLaterWorlds.Outcome E X × PqxdhRecordLiftWorld.State n =>
      result.1.any fun value => event (value.2.1, result.2.produced)) <$>
      (simulateQ (CborRecordWorldSimulation.guarded setup codec route)
        (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary)).run
          PqxdhRecordLiftWorld.initial =
      (fun view : PqxdhRecordLiftIdeal.View n E X =>
        view.result.any fun value => event ((value.1, value.2.1), view.produced)) <$>
      (chainView <$> PqxdhRecordLiftLaterWorlds.chainsOf (fun _ => false) setup codec route
        (CborRawRecordLiftBounds.client env setup.source.crypto codec serverKid bounds mode adversary)) := by
  rw [CborRawRecordProvenance.real_view]
  have erased := CborRawIdealProvenanceStartup.erase setup codec route env serverKid bounds mode adversary
  have compared := CborRecordWorldSimulation.client_simulation setup codec route
    (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary)
    (PqxdhRecordLiftWorld.initial (n := n))
  change _ = (simulateQ (CborRecordWorldSimulation.guarded setup codec route)
    (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary)).run
      PqxdhRecordLiftWorld.initial at compared
  have complete := erased.trans compared
  rw [← complete, Functor.map_map, Functor.map_map]
  congr 1
  funext result
  rcases result with ⟨_ | inner, state⟩ <;> rfl

/-- The raw source slot game is bounded by its decision on the actual complete raw compiled record view. -/
theorem slot_real (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[PqxdhRegistrationJointKemSecondEntry.slotGame setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
      (CborRawKemTransfer.decision setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget event claim g)
      (CborRawCompileSecrecy.compileFull setup wire parse bounds mode adversary) runtime budget.create
      (selectedKem budget g) g.1.val 2] {true} ≤
    𝒟[(fun view => (viewObserved view).any (decisionOn setup (boundaryWire wire parse) budget event claim g)) <$>
      (chainView <$> PqxdhRecordLiftLaterWorlds.chainsOf (fun _ => false) setup (boundaryWire wire parse)
        (CborRawCompile.route parse) (CborRawRecordLiftBounds.client (CborRawEnvironment.environment
          (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks (Target.ofCE budget g)
            ensureInit 0 runtime) setup.serverKeyId) setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
              mode adversary))] {true} := by
  let work := PqxdhDeploymentSecrecy.wrap setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)
  let chosen : (X × PqxdhDeploymentSecrecy.Ledger) × CborRawPostActive.Produced → Bool := fun result =>
    decisionOn setup (boundaryWire wire parse) budget event claim g (result.1.1, result.1.2, result.2)
  have bounded := CborRawHeadlineSlot.drawn_world setup wire parse checks (Target.ofCE budget g) ensureInit runtime
    work chosen phase1 phase2 (PqxdhDeploymentCompileCaps.transported bounds budget)
    (CborRawCompileCaps.certified setup wire parse bounds mode adversary budget respects)
    rfl rfl (PqxdhDeploymentCompileCaps.transported_room bounds budget)
  rw [← CborRawIdealWorldProgram.program setup wire parse checks (Target.ofCE budget g) ensureInit runtime bounds mode
    adversary] at bounded
  unfold CborRawHeadlineSlot.observe at bounded
  rw [real_event] at bounded
  convert bounded using 1
  · rfl
  · congr 2
    congr 1
    funext view
    simp only [viewObserved, Option.any_map]
    rfl

/-- The actual raw-CBOR experiment reaches the actual full raw record view with concrete KEM and root/key-schedule losses. -/
theorem chain_real (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (target : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
      designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget claim outcome = some target)) <$>
      (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[(fun view => (viewObserved view).any (decisionOn setup (boundaryWire wire parse) budget event claim target)) <$>
        (chainView <$> PqxdhRecordLiftLaterWorlds.chainsOf (fun _ => false) setup (boundaryWire wire parse)
          (CborRawCompile.route parse) (CborRawRecordLiftBounds.client (CborRawEnvironment.environment
            (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks (Target.ofCE budget target)
              ensureInit 0 runtime) setup.serverKeyId) setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds
                mode adversary))] {true} +
      ENNReal.ofReal (CborRawHeadlineChain.kemLoss setup wire parse checks ensureInit bounds mode adversary budget event claim target runtime) +
      ENNReal.ofReal (CborRawHeadlineChain.slotLoss setup wire parse checks ensureInit bounds mode adversary budget event claim target runtime) := by
  have source := CborRawHeadlineChain.chain_slot setup functional wire parse checks lengths parser ensureInit phase1
    phase2 correct bounds mode adversary budget respects event claim target runtime
  have records := slot_real setup wire parse checks phase1 phase2 ensureInit bounds mode adversary budget respects
    event claim target runtime
  exact source.trans (add_le_add (add_le_add records le_rfl) le_rfl)

end BeaconcryptCore.Computational.CborRawHeadlineWorld

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineWorld.real_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineWorld.real_event
/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineWorld.slot_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineWorld.slot_real

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineWorld.chain_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineWorld.chain_real
