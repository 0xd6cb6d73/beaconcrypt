-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealBeaconShadow
import BeaconcryptCore.Computational.CborRawIdealBeaconTransport
import BeaconcryptCore.Computational.CborRawIdealProvenanceCodec

/-! The native raw designation implies the ideal Beacon slot or the actual early-finish anomaly. The proof reads the raw transcript for all public eligibility and timing decisions, and uses the constructed canonical shadow only to recover the challenge ciphertext and the actual delegated finish. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawIdealBeaconConverse
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Entry)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhRecordLiftOrigins (Origins)
open PqxdhDeploymentIdealTrace (BeaconLinked FinishBefore KeyFacts)
open PqxdhDeploymentIdealProvenance (Prov)
open CborTaggedSimulation (boundaryWire)
open CborRawIdealBeaconShadow (Shadow)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Every native raw Beacon designation on a prefix has the final ideal slot, unless that successful raw finish preceded the selected accept. -/
theorem beacon_converse (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (serverKid : Std.U64) {count : Nat} (target : Target count) (parameters : Params KemSK count)
    (raw pre rest : List Entry) (split : raw = pre ++ rest) (state : EnvState KemSK SplitBk)
    (world : PqxdhRecordLiftWorld.State 2) (origins : Origins 2)
    (prov : Prov target raw state world origins)
    (shadow : Shadow (CborRawCompile.sourceCodec wire parse) target parameters raw state world origins)
    (facts : KeyFacts setup (boundaryWire wire parse) checks target parameters raw state.backend.2.2)
    (linked : BeaconLinked setup.source.crypto (boundaryWire wire parse) serverKid target pre) :
    (∃ coordinates slot, state.backend.2.2.beacon = some coordinates ∧ state.backend.2.1.1 coordinates = some slot) ∨
      FinishBefore target pre := by
  obtain ⟨canonical, related, _, holds⟩ := shadow.history
  have marked := PqxdhDeploymentIdealBeacon.keyFacts_marked_prefix setup (boundaryWire wire parse) checks phase1
    serverKid target parameters raw pre rest split state.backend.2.2 facts (.owner target.kem.val) linked
  obtain ⟨⟨session, coordinates⟩, marks⟩ := Option.isSome_iff_exists.mp marked
  have selected := (prov.marked session coordinates marks).1
  subst selected
  obtain ⟨-, -, pin, bytes, ciphertext, published, pqKey, -, rawFound, ciphertextFound, -, -, -, link⟩ :=
    PqxdhDeploymentTranscript.designate_owner setup.source.crypto (boundaryWire wire parse) serverKid pre
      target.kem.val _ _ linked
  obtain ⟨response, -, -, builtFound, responseCiphertext, -⟩ := link
  obtain ⟨payload, built⟩ := PqxdhDeploymentKeyMatch.buildOf_mem pre _ response builtFound
  have builtAll : PqxdhDeploymentIdealProvenance.BuiltIn raw _ response :=
    ⟨payload, by rw [split]; exact List.mem_append_left rest built⟩
  obtain ⟨original, originalBuilt, stripped⟩ :=
    CborRawIdealBeaconTransport.built raw canonical related _ response builtAll
  have written := holds.built _ coordinates original marks originalBuilt
  have recovered := CborRawIdealProvenanceCodec.written_read_strip wire parse phase2 parameters.challenge original written
    ciphertext (by rw [stripped]; exact responseCiphertext)
  have read : PqxdhDeploymentIdealBeacon.ChallengeRead (boundaryWire wire parse) parameters.challenge bytes :=
    ⟨ciphertext, ciphertextFound, recovered⟩
  obtain ⟨reply, member⟩ := PqxdhDeploymentIdealBeacon.finishOf_mem pre target.kem.val bytes rawFound
  rcases PqxdhDeploymentIdealBeacon.finish_split target pre bytes reply member with early | late
  · exact Or.inr early
  · obtain ⟨before, reply', after, preSplit, clock⟩ := late
    have lateAll : PqxdhDeploymentIdealBeacon.LateFinish target raw bytes :=
      ⟨before, reply', after ++ rest, by rw [split, preSplit]; simp, clock⟩
    obtain ⟨sender, delegated⟩ := CborRawIdealBeaconTransport.late_finish target raw canonical related bytes lateAll
    rcases holds.finishes (CborTaggedCodec.tag sender bytes) delegated
      (CborRawIdealProvenanceCodec.challenge_read_tag wire parse parameters.challenge sender bytes read) with none | some
    · rw [marks] at none
      cases none
    · obtain ⟨coordinates', found⟩ := Option.isSome_iff_exists.mp some
      obtain ⟨slot, assigned⟩ := Option.isSome_iff_exists.mp (holds.slot coordinates' found)
      exact Or.inl ⟨coordinates', slot, found, assigned⟩

end BeaconcryptCore.Computational.CborRawIdealBeaconConverse

/-- info: 'BeaconcryptCore.Computational.CborRawIdealBeaconConverse.beacon_converse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealBeaconConverse.beacon_converse
