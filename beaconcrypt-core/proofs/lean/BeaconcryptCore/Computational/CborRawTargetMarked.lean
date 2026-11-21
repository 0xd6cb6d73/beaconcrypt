-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealKeymatchRun
import BeaconcryptCore.Computational.CborRawHeadlineWorld

/-! A genuine native-wire target designation forces the private selected-session mark in the same complete raw run. The existing concrete accept/bundle trace supplies the actual chosen KEM key; only unused analysis ghosts are removed by the native/middle operational equation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawTargetMarked
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget Handle Spec FullSpec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealSteps (IdealCore)
open PqxdhDeploymentIdealTrace (KeyFacts)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentIdealHandoff (decisionOn)
open PqxdhDeploymentSecrecy (Ledger)
open CborRawPublicState (Public)
open CborRawMiddleSimulation (Native)
variable {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι}

/-- The exact key facts of a transcript turn a native-wire designation into a selected-session mark. -/
theorem keyFacts_designated (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    {count : Nat} (t : Target count) (p : Params KemSK count)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (serverKid : Std.U64)
    (ledger : Ledger) (core : IdealCore) (trace : KeyFacts setup codec checks t p ledger.transcript core)
    (handle : Handle)
    (designated : PqxdhDeploymentTranscript.designate setup.source.crypto codec serverKid ledger.transcript handle =
      some (t.accept, t.kem.val)) : core.marks.isSome := by
  obtain ⟨raw, accepted, keys, published, rawFound, candidateFound, keysFound, publishedFound, pqFound⟩ :=
    PqxdhDeploymentKemTransfer.designate_keys setup.source.crypto codec serverKid ledger.transcript handle t.accept
      t.kem.val designated
  obtain ⟨value, verified, marked⟩ := trace.selected raw
    (PqxdhDeploymentKemTransfer.acceptOf_mem ledger.transcript t.accept raw rawFound)
  obtain ⟨candidateEq, keysEq⟩ := PqxdhDeploymentKeyMatch.verified_keys setup codec checks raw value verified
  rw [candidateFound, Option.some.injEq] at candidateEq
  subst candidateEq
  rw [keysFound, Option.some.injEq] at keysEq
  subst keysEq
  obtain ⟨bytes, bytesFound, publishedRead⟩ := Option.bind_eq_some_iff.mp publishedFound
  obtain ⟨identity, tuple, s1, s2, s3, written, pooled⟩ := trace.bundles t.kem.val bytes
    (PqxdhDeploymentKeyMatch.bundleOf_mem ledger.transcript t.kem.val bytes bytesFound)
  rw [PqxdhDeploymentKeyMatch.candidateOf_written codec phase1 _ bytes written, Option.some.injEq] at publishedRead
  subst publishedRead
  rw [PqxdhDeploymentKeyMatch.publishedPq_candidate, Option.some.injEq] at pqFound
  apply marked
  rw [← pqFound]
  exact pooled p.chosen (PqxdhDeploymentIdealParams.pool_kem t p)

/-- Every actual initialized raw middle run retains the exact selected-accept and published-bundle facts on its original ledger. -/
theorem middle_keyFacts (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (bounds : FreshBounds) (work : OracleComp FullSpec X) (publicState : Public)
    (result : (X × Ledger) × (Public × Native KemSK))
    (supported : result ∈ support ((simulateQ (CborRawMiddleSimulation.handler setup wire parse checks target parameters created)
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
        setup.serverKeyId bounds work)).run
          (publicState, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)))) :
    KeyFacts setup (CborTaggedSimulation.boundaryWire wire parse) checks target parameters result.1.2.transcript
      result.2.2.backend.2.2 := by
  have resetInitial : CborRawNativePublic.reset (KemSK := KemSK)
      (publicState, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)) =
      (publicState, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)) := rfl
  have same := CborRawNativePublic.run setup wire parse checks target parameters created
    (PqxdhDeploymentSecrecy.wrap setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
      setup.serverKeyId bounds work)
    (publicState, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created))
  rw [resetInitial] at same
  rw [← same, support_map] at supported
  obtain ⟨actual, reached, equal⟩ := supported
  have trace := CborRawIdealKeymatchRun.run_trace setup wire parse checks target parameters created bounds work publicState actual reached
  have ledger : actual.1.2 = result.1.2 := congrArg (fun value => value.1.2) equal
  have core : actual.2.2.backend.2.2 = result.2.2.backend.2.2 := congrArg (fun value => value.2.2.backend.2.2) equal
  have sourceFacts : KeyFacts setup (CborRawCompile.sourceCodec wire parse) checks target parameters
      result.1.2.transcript result.2.2.backend.2.2 := by
    rw [← ledger, ← core]
    exact ⟨trace.selected, trace.bundles⟩
  exact ⟨sourceFacts.selected, sourceFacts.bundles⟩

/-- An actual raw per-target decision supplies its own mark from the same native ledger; no mark implication is assumed. -/
theorem decision_marked (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborTaggedSimulation.boundaryWire wire parse))
    (budget : Budget) (g : Fin budget.accept × Fin budget.capacity) (parameters : Params KemSK budget.create)
    (created : PqxdhLiveServerConstruction.Created Unit) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (publicState : Public) (result : (X × Ledger) × (Public × Native KemSK))
    (supported : result ∈ support ((simulateQ (CborRawMiddleSimulation.handler setup wire parse checks (Target.ofCE budget g) parameters created)
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
        setup.serverKeyId bounds (PqxdhDeploymentInterface.asModeO mode adversary))).run
          (publicState, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created))))
    (decided : decisionOn setup (CborTaggedSimulation.boundaryWire wire parse) budget event claim g
      (result.1.1, result.1.2, result.2.2.base.produced) = true) : result.2.2.backend.2.2.marks.isSome := by
  have facts := middle_keyFacts setup wire parse checks (Target.ofCE budget g) parameters created bounds
    (PqxdhDeploymentInterface.asModeO mode adversary) publicState result supported
  simp only [decisionOn, Bool.and_eq_true, decide_eq_true_eq] at decided
  obtain ⟨handle, _, chosen⟩ := Option.bind_eq_some_iff.mp decided.2
  exact keyFacts_designated setup (CborTaggedSimulation.boundaryWire wire parse) checks (Target.ofCE budget g)
    parameters phase1 setup.serverKeyId result.1.2 result.2.2.backend.2.2 facts handle
      (PqxdhDeploymentKemTransfer.designateIn_some setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
        setup.serverKeyId budget _ handle g chosen)

/-- The actual raw target decision has exactly the same law with its derived private selected-session mark retained. -/
theorem marked_eq (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborTaggedSimulation.boundaryWire wire parse))
    (budget : Budget) (g : Fin budget.accept × Fin budget.capacity) (parameters : Params KemSK budget.create)
    (created : PqxdhLiveServerConstruction.Created Unit) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (publicState : Public) :
    CborRawMarkedPrefix.run setup wire parse checks (Target.ofCE budget g) parameters created
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
        setup.serverKeyId bounds (PqxdhDeploymentInterface.asModeO mode adversary))
      (fun value => decisionOn setup (CborTaggedSimulation.boundaryWire wire parse) budget event claim g
        (value.1.1, value.1.2, value.2))
      (publicState, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)) =
    (fun value => decisionOn setup (CborTaggedSimulation.boundaryWire wire parse) budget event claim g
      (value.1.1, value.1.2, value.2.2.base.produced)) <$>
        (simulateQ (CborRawMiddleSimulation.handler setup wire parse checks (Target.ofCE budget g) parameters created)
          (PqxdhDeploymentSecrecy.wrap setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
            setup.serverKeyId bounds (PqxdhDeploymentInterface.asModeO mode adversary))).run
              (publicState, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)) := by
  unfold CborRawMarkedPrefix.run
  apply PqxdhDeploymentKemTransfer.map_support_congr
  intro result supported
  by_cases decided : decisionOn setup (CborTaggedSimulation.boundaryWire wire parse) budget event claim g
      (result.1.1, result.1.2, result.2.2.base.produced) = true
  · have marked := decision_marked setup wire parse checks phase1 budget g parameters created bounds mode adversary event claim publicState result supported decided
    simp only [decided, CborRawMiddleMarks.marks, marked, Bool.and_true]
  · have no : decisionOn setup (CborTaggedSimulation.boundaryWire wire parse) budget event claim g
      (result.1.1, result.1.2, result.2.2.base.produced) = false := Bool.eq_false_iff.mpr decided
    simp only [no, Bool.false_and]

end BeaconcryptCore.Computational.CborRawTargetMarked

/-- info: 'BeaconcryptCore.Computational.CborRawTargetMarked.keyFacts_designated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawTargetMarked.keyFacts_designated
/-- info: 'BeaconcryptCore.Computational.CborRawTargetMarked.middle_keyFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawTargetMarked.middle_keyFacts
/-- info: 'BeaconcryptCore.Computational.CborRawTargetMarked.decision_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawTargetMarked.decision_marked
/-- info: 'BeaconcryptCore.Computational.CborRawTargetMarked.marked_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawTargetMarked.marked_eq
