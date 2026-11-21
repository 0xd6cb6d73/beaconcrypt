-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicationBundlePrekey
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordExecution
/-! Successful current Word bundle bytes come from the actual source-backed serializer and the captured owner's PQ field. The common platform and all private/query poststates remain on the original supported execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyPublication
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

/-- The actual current dynamic Word bundle recovers the retained owner's signed PQ field using the concrete writer internally. -/
theorem word_bundle (setup : Setup base KemSK) (selectedOwner index : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (before after : RegistrationNativePlatformSecretWordOrdinary.State source Platform) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some bytes), after) ∈ support ((RegistrationNativePlatformSecretWordOrdinary.handler
      (n := n) (KemSK := KemSK) setup source selectedOwner publicPrekey reserveFrame
      (RegistrationNativePlatformConcreteSource.writer reservePackets) (.inr (.bundle index))).run before)) :
    ∃ owner packet, before.1.beacons[index]? = some owner ∧
      RegistrationNativeWire.readInit RegistrationNativePlatformConcreteSource.wire bytes = some packet ∧
      (PqxdhRefinement.absBytes packet.pre_key).drop 64 = PqxdhEd25519EufCma.prekeyMessage (PqxdhPhase2InputBytes.word owner.view.prekeyPublic) := by
  simp only [RegistrationNativePlatformSecretWordOrdinary.handler, StateT.run_map, support_map] at supported
  obtain ⟨raw, called, same⟩ := supported
  simp only [RegistrationNativePlatformSecretWordOrdinary.beacon, StateT.run, support_map] at called
  obtain ⟨middle, interpreted, equal⟩ := called
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ interpreted
  have output := congrArg Prod.fst same
  rw [← equal] at output
  dsimp only at output
  cases encoded : middle.1.1.1 with
  | fail error | div =>
    simp only [encoded, RegistrationNativePlatformPublicFrontend.bundleBytes, bind_tc_fail, bind_tc_div] at output
    cases output
  | ok optional => cases optional with
    | none => simp [encoded, RegistrationNativePlatformPublicFrontend.bundleBytes] at output
    | some vector =>
      have bytesEq : TranscriptAuthParts.absSlice vector = bytes := by
        have sameBytes : RustM.ok (some (TranscriptAuthParts.absSlice vector)) = RustM.ok (some bytes) := by
          simpa only [encoded, RegistrationNativePlatformPublicFrontend.bundleBytes, bind_tc_ok, Option.map_some] using output
        exact Option.some.inj (RustM.ok.inj sameBytes)
      obtain ⟨owner, packet, found, decoded, key⟩ := RegistrationNativePlatformPublicationBundlePrekey.public_bundle
        reservePackets setup RegistrationNativePlatformPublicFrontend.trusted selectedOwner index publicPrekey
        before.1.beacons before.1.environment before.2 middle vector encoded original
      exact ⟨owner, packet, found, bytesEq ▸ decoded, key⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyPublication


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyPublication.word_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyPublication.word_bundle
