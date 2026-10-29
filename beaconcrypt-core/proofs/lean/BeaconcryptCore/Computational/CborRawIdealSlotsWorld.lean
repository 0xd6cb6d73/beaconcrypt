-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealSlots
import BeaconcryptCore.Computational.CborRawIdealKeymatchStartup

/-! Slot provenance on every outcome of the actual complete raw World client, including challenger draws and the original secrecy ledger. All support hypotheses used by the local slot theorem are supplied by the concrete startup and execution proofs. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawIdealSlotsWorld
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Entry FreshBounds Mode ModeSpec)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (originSlots IdealSlots Anomaly BeaconLinked FinishBefore peerOf)
open PqxdhDeploymentTranscript (designate)
open CborRawIdealProvenanceParameter (drop)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborTaggedSimulation.boundaryWire wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    {count : Nat} (target : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)

noncomputable def annotated (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :=
  CborRawIdealProvenanceStartup.annotatedRun setup (CborTaggedSimulation.boundaryWire wire parse)
    (CborRawCompile.route parse) (CborRawEnvironment.environment
      (PqxdhDeploymentIdealEnv.envGD setup (CborRawCompile.sourceCodec wire parse) checks target ensureInit identityIndex
        runtime) setup.serverKeyId) setup.serverKeyId bounds mode adversary

include phase1 phase2

/-- Every actual raw prefix designation satisfies the concrete slot restrictions and both native converses. -/
theorem slots_prefix (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    ∀ result ∈ support (annotated setup wire parse checks target ensureInit identityIndex runtime bounds mode adversary),
      ∀ value, result.1 = some value → ∀ pre rest, value.2.1.2.transcript = pre ++ rest →
        (∀ keyId slot, originSlots result.2.2 (.peer keyId) = some slot →
          slot = 0 ∧ peerOf target value.2.1.2.transcript = some keyId) ∧
        (∀ owner slot, originSlots result.2.2 (.owner owner) = some slot → owner = target.kem.val) ∧
        (∀ keyId, designate setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId pre
          (.peer keyId) = some (target.accept, target.kem.val) → originSlots result.2.2 (.peer keyId) = some 0) ∧
        (BeaconLinked setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId target pre →
          (originSlots result.2.2 (.owner target.kem.val)).isSome = true ∨ FinishBefore target pre) := by
  intro result reached value found pre rest split
  obtain ⟨created, holds⟩ := CborRawIdealProvenanceDraw.world setup wire parse checks target ensureInit identityIndex
    runtime bounds mode adversary result reached value found
  have facts := CborRawIdealKeymatchStartup.world setup wire parse checks target ensureInit identityIndex runtime bounds
    mode adversary result reached value found
  exact CborRawIdealSlots.slots_prefix setup wire parse checks phase1 phase2 target value.2.2.2.backend.1 created
    value.2.1.2.transcript pre rest split (drop value.2.2) result.2.1 result.2.2 holds facts

/-- All four slot conditions hold on every actual raw World outcome, with precisely the native early-finish anomaly as alternative. -/
theorem slots_or_anomaly (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    ∀ result ∈ support (annotated setup wire parse checks target ensureInit identityIndex runtime bounds mode adversary),
      ∀ value, result.1 = some value →
        IdealSlots setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId target
          (originSlots result.2.2) value.2.1.2.transcript ∨
        Anomaly setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId target
          value.2.1.2.transcript := by
  intro result reached value found
  obtain ⟨created, holds⟩ := CborRawIdealProvenanceDraw.world setup wire parse checks target ensureInit identityIndex
    runtime bounds mode adversary result reached value found
  have facts := CborRawIdealKeymatchStartup.world setup wire parse checks target ensureInit identityIndex runtime bounds
    mode adversary result reached value found
  exact CborRawIdealSlots.slots_or_anomaly setup wire parse checks phase1 phase2 target value.2.2.2.backend.1 created
    value.2.1.2.transcript (drop value.2.2) result.2.1 result.2.2 holds facts

end BeaconcryptCore.Computational.CborRawIdealSlotsWorld

/-- info: 'BeaconcryptCore.Computational.CborRawIdealSlotsWorld.slots_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealSlotsWorld.slots_prefix

/-- info: 'BeaconcryptCore.Computational.CborRawIdealSlotsWorld.slots_or_anomaly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealSlotsWorld.slots_or_anomaly
