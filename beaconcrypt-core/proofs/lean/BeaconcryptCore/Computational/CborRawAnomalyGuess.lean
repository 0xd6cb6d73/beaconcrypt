-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordProvenance
import BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess

/-! The actual raw early-finish anomaly predicts the drawn ciphertext. Native designation reads the original raw ledger; only the already constructed source shadow supplies the written challenge response. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawAnomalyGuess
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Entry FreshBounds Mode ModeSpec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealTrace (Anomaly KeyFacts)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhRecordLiftOrigins (Origins)
open CborRawPublicState (Public)
open CborTaggedSimulation (boundaryWire)
open PqxdhDeploymentIdealGuess (guessCt earlyFinish_eq)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

/-- Concrete raw provenance and the constructed canonical shadow determine the ciphertext in the original early finish. -/
theorem from_invariants (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    {count : Nat} (target : Target count) (parameters : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (transcript : List Entry)
    (state : Public × EnvState KemSK SplitBk) (world : PqxdhRecordLiftWorld.State 2) (origins : Origins 2)
    (holds : CborRawIdealProvenanceOutcome.Holds (CborRawCompile.sourceCodec wire parse) target parameters created
      transcript state world origins)
    (facts : KeyFacts setup (boundaryWire wire parse) checks target parameters transcript state.2.backend.2.2)
    (anomaly : Anomaly setup.source.crypto (boundaryWire wire parse) setup.serverKeyId target transcript) :
    guessCt (boundaryWire wire parse) target transcript = some parameters.challenge := by
  obtain ⟨linked, early⟩ := anomaly
  obtain ⟨canonical, related, _, shadow⟩ := holds.shadow.history
  have marked := PqxdhDeploymentIdealBeacon.keyFacts_marked_prefix setup (boundaryWire wire parse) checks phase1
    setup.serverKeyId target parameters transcript transcript [] (List.append_nil _).symm state.2.backend.2.2 facts
    (.owner target.kem.val) linked
  obtain ⟨⟨session, coordinates⟩, marks⟩ := Option.isSome_iff_exists.mp marked
  have selected := (holds.prov.marked session coordinates marks).1
  subst selected
  obtain ⟨-, -, pin, bytes, ciphertext, published, pqKey, -, rawFound, ciphertextFound, -, -, -, link⟩ :=
    PqxdhDeploymentTranscript.designate_owner setup.source.crypto (boundaryWire wire parse) setup.serverKeyId transcript
      target.kem.val _ _ linked
  obtain ⟨response, -, -, builtFound, responseCiphertext, -⟩ := link
  obtain ⟨payload, built⟩ := PqxdhDeploymentKeyMatch.buildOf_mem transcript _ response builtFound
  obtain ⟨original, originalBuilt, stripped⟩ := CborRawIdealBeaconTransport.built transcript canonical related _ response
    ⟨payload, built⟩
  have written := shadow.built _ coordinates original marks originalBuilt
  have same := CborRawIdealProvenanceCodec.written_read_strip wire parse phase2 parameters.challenge original written
    ciphertext (by rw [stripped]; exact responseCiphertext)
  unfold guessCt
  rw [earlyFinish_eq target _ early, rawFound, Option.bind_some, ciphertextFound, Option.map_some, same]

/-- Every actual complete raw World anomaly hits the challenge retained from its actual startup draw. -/
theorem world (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    {count : Nat} (target : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    ∀ result ∈ support (CborRawIdealSlotsWorld.annotated setup wire parse checks target ensureInit identityIndex runtime
      bounds mode adversary), ∀ value, result.1 = some value →
      Anomaly setup.source.crypto (boundaryWire wire parse) setup.serverKeyId target value.2.1.2.transcript →
      guessCt (boundaryWire wire parse) target value.2.1.2.transcript = some value.2.2.2.backend.1.challenge := by
  intro result reached value found anomaly
  obtain ⟨created, holds⟩ := CborRawIdealProvenanceDraw.world setup wire parse checks target ensureInit identityIndex
    runtime bounds mode adversary result reached value found
  have facts := CborRawIdealKeymatchStartup.world setup wire parse checks target ensureInit identityIndex runtime bounds
    mode adversary result reached value found
  exact from_invariants setup wire parse checks phase1 phase2 target value.2.2.2.backend.1 created
    value.2.1.2.transcript (CborRawIdealProvenanceParameter.drop value.2.2) result.2.1 result.2.2 holds facts anomaly

end BeaconcryptCore.Computational.CborRawAnomalyGuess

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyGuess.from_invariants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyGuess.from_invariants
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyGuess.world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyGuess.world
