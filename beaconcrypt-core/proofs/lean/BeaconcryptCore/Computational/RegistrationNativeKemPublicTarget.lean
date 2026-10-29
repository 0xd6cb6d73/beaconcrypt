-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemPublication
import BeaconcryptCore.Computational.RegistrationWorldAuthentication
import BeaconcryptCore.Computational.PqxdhDeploymentTranscript

/-! Broad CE designation compares the verified accepted PQ key with an owner's published PQ key. Actual native authentication and actual publication identify both public projections with their native getter/generated key. Consequently a changed valid signature need not be treated as an unchanged bundle to establish KEM target membership. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhKemIndCca (MlKem768PublicKey)
open BeaconcryptCore.Refinement.RegistrationAuthenticationFlow (Event)
variable {ι KemSK Reader Response : Type} {base : OracleSpec ι} {n : Nat}
attribute [local irreducible] RegistrationWorldAuthentication.begin
  RegistrationAuthenticationShared.begin RegistrationAuthenticationExecutor.begin

/-- Reading actual six-field native bytes selects their original four classical public fields for the CE designation. -/
theorem candidate_read (wire : RegistrationNativeWire.Wire) (raw : Pqxdh.Bytes) (packet : registration.InitPacket)
    (decoded : RegistrationNativeWire.readInit wire raw = some packet) :
    PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec wire) raw =
      some (RegistrationRootInput.candidate packet) := by
  simp only [PqxdhDeploymentTranscript.candidateOf, PqxdhRegistrationJointRawSignatures.candidate,
    RegistrationNativeWire.ledgerCodec, decoded, RegistrationRootInput.candidate]
  rfl

/-- The exact native attached PQ field has the public generated-key parser result used by CE designation. -/
theorem published_key (packet : registration.InitPacket) (key : MlKem768PublicKey)
    (published : RegistrationNativeKemTarget.PacketKey packet key) :
    PqxdhDeploymentTranscript.publishedPq (RegistrationRootInput.candidate packet) = some key := by
  have width : 64 ≤ (absBytes packet.pq_key).length := by simp
  simp only [PqxdhDeploymentTranscript.publishedPq, RegistrationRootInput.candidate,
    PqxdhEd25519EufCma.splitAttachedSignature]
  simp only [dite_eq_left width, Option.bind_some]
  rw [published]
  exact PqxdhEd25519EufCma.parsePqMessage_pqMessage key

/-- Actual native global-World authentication yields the same public verified tuple used by broad CE eligibility. -/
theorem world_accepted (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : PqxdhRecordLiftWorld.State n) (events : List Event) (accepted : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted accepted), after) ∈ support
      ((RegistrationWorldAuthentication.begin setup codec route verify pin packet).run before)) :
    PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet) =
      some (RegistrationRootInput.identity accepted.registration, RegistrationRootInput.keys accepted.registration) := by
  exact RegistrationRootInput.accepted_source setup.source.crypto verify codec.frameWrite
    (RawCtxSourceHkdf.kdfImpl setup.source) pin packet _ _ events accepted
    (RegistrationWorldAuthentication.begin_native_support setup codec route verify pin packet before after events accepted supported)

/-- Broad public PQ-key matching identifies the literal actual getter even when the accepted signed packet differs from the owner's publication. -/
theorem matched_getter (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet publishedPacket : registration.InitPacket)
    (before after : PqxdhRecordLiftWorld.State n) (events : List Event) (accepted : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted accepted), after) ∈ support
      ((RegistrationWorldAuthentication.begin setup codec route verify pin packet).run before))
    (bornKey : MlKem768PublicKey) (published : RegistrationNativeKemTarget.PacketKey publishedPacket bornKey)
    (matching : (PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto
      (RegistrationRootInput.candidate packet)).map (fun value => value.2.pqKey) =
        PqxdhDeploymentTranscript.publishedPq (RegistrationRootInput.candidate publishedPacket)) :
    RegistrationRootInput.pqKey accepted.registration.beacon_pq_public_key = bornKey := by
  rw [world_accepted setup codec route verify pin packet before after events accepted supported,
    published_key publishedPacket bornKey published] at matching
  exact Option.some.inj matching

end BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget.candidate_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget.candidate_read

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget.published_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget.published_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget.world_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget.world_accepted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget.matched_getter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget.matched_getter
