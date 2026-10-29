-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealProvenanceDraw
import BeaconcryptCore.Computational.CborRawIdealBeaconConverse

/-! Native raw-transcript slot provenance from the concrete World invariants. Both converses use designation on the actual raw prefix. The source shadow is constructed operationally and supplies only the marked ciphertext and tagged-finish facts; no canonical designation or whole-game relation is required. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawIdealSlots
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Entry)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhDeploymentIdealTrace (originSlots peerOf IdealSlots BeaconLinked FinishBefore Anomaly KeyFacts)
open PqxdhDeploymentTranscript (designate)
open PqxdhRecordLiftOrigins (Origins)
open CborRawPublicState (Public)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The two slot restrictions and both raw prefix converses follow from the actual native World invariants. -/
theorem slots_prefix (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborTaggedSimulation.boundaryWire wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    {count : Nat} (target : Target count) (parameters : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (transcript pre rest : List Entry)
    (split : transcript = pre ++ rest) (state : Public × EnvState KemSK SplitBk)
    (world : PqxdhRecordLiftWorld.State 2) (origins : Origins 2)
    (holds : CborRawIdealProvenanceOutcome.Holds (CborRawCompile.sourceCodec wire parse) target parameters created
      transcript state world origins)
    (facts : KeyFacts setup (CborTaggedSimulation.boundaryWire wire parse) checks target parameters transcript
      state.2.backend.2.2) :
    (∀ keyId slot, originSlots origins (.peer keyId) = some slot → slot = 0 ∧ peerOf target transcript = some keyId) ∧
    (∀ owner slot, originSlots origins (.owner owner) = some slot → owner = target.kem.val) ∧
    (∀ keyId, designate setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId pre
      (.peer keyId) = some (target.accept, target.kem.val) → originSlots origins (.peer keyId) = some 0) ∧
    (BeaconLinked setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId target pre →
      (originSlots origins (.owner target.kem.val)).isSome = true ∨ FinishBefore target pre) := by
  have ghost := PqxdhDeploymentIdealProvenance.origins_eq_ghost target transcript state.2 world origins holds.prov holds.inv
  refine ⟨fun keyId slot slotted => ?_, fun owner slot slotted => holds.prov.ownerKey owner slot slotted,
    fun keyId designated => ?_, fun linked => ?_⟩
  · change origins.peers keyId = some slot at slotted
    obtain ⟨coordinates, peer⟩ := holds.prov.peerKey keyId slot slotted
    obtain ⟨zero, named⟩ := PqxdhDeploymentIdealProvenance.trace_peer target transcript state.2 world origins holds.prov
      holds.inv keyId coordinates peer
    rw [ghost] at slotted
    simp only [PqxdhDeploymentIdealTrace.ghostOrigins, peer, ite_true, zero, Option.some.injEq] at slotted
    exact ⟨slotted.symm, named⟩
  · obtain ⟨coordinates, peer⟩ := PqxdhDeploymentIdealBeacon.trace_designated_prefix setup
      (CborTaggedSimulation.boundaryWire wire parse) checks phase1 setup.serverKeyId target parameters transcript pre rest
      split state.2 world origins holds.prov facts keyId designated
    obtain ⟨zero, _⟩ := PqxdhDeploymentIdealProvenance.trace_peer target transcript state.2 world origins holds.prov
      holds.inv keyId coordinates peer
    change origins.peers keyId = some 0
    rw [ghost]
    simp only [PqxdhDeploymentIdealTrace.ghostOrigins, peer, ite_true, zero]
  · rcases CborRawIdealBeaconConverse.beacon_converse setup wire parse checks phase1 phase2 setup.serverKeyId target
      parameters transcript pre rest split state.2 world origins holds.prov holds.shadow facts linked with
      ⟨coordinates, slot, beacon, allocated⟩ | early
    · left
      change (origins.owners target.kem.val).isSome = true
      rw [ghost]
      simp only [PqxdhDeploymentIdealTrace.ghostOrigins, ite_true, beacon, Option.bind_some, allocated, Option.isSome_some]
    · exact Or.inr early

/-- Complete raw native designation satisfies all four slot conditions, with exactly the existing early-finish anomaly as alternative. -/
theorem slots_or_anomaly (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborTaggedSimulation.boundaryWire wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    {count : Nat} (target : Target count) (parameters : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (transcript : List Entry)
    (state : Public × EnvState KemSK SplitBk) (world : PqxdhRecordLiftWorld.State 2) (origins : Origins 2)
    (holds : CborRawIdealProvenanceOutcome.Holds (CborRawCompile.sourceCodec wire parse) target parameters created
      transcript state world origins)
    (facts : KeyFacts setup (CborTaggedSimulation.boundaryWire wire parse) checks target parameters transcript
      state.2.backend.2.2) :
    IdealSlots setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId target
      (originSlots origins) transcript ∨
      Anomaly setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId target transcript := by
  obtain ⟨server, beacon, converse, beaconConverse⟩ := slots_prefix setup wire parse checks phase1 phase2 target parameters
    created transcript transcript [] (List.append_nil _).symm state world origins holds facts
  by_cases linked : BeaconLinked setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId
      target transcript
  · rcases beaconConverse linked with slotted | early
    · exact Or.inl ⟨server, beacon, converse, fun _ => slotted⟩
    · exact Or.inr ⟨linked, early⟩
  · exact Or.inl ⟨server, beacon, converse, fun claimed => absurd claimed linked⟩

end BeaconcryptCore.Computational.CborRawIdealSlots

/-- info: 'BeaconcryptCore.Computational.CborRawIdealSlots.slots_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealSlots.slots_prefix

/-- info: 'BeaconcryptCore.Computational.CborRawIdealSlots.slots_or_anomaly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealSlots.slots_or_anomaly
