-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOneTimePublication
import BeaconcryptCore.Computational.RegistrationNativeKemPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicationConcrete
import BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple
/-! Successful concrete Init publication preserves the original unsigned three-key tuple. Decoder readback aligns the three source payload receipts without identifying any signature bytes or assuming their uniqueness. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeConcreteTuplePublication
open PqxdhEd25519EufCma
local notation "encode" => (fun view => core.option.Option.Some (RegistrationNativeSourceWriterReadback.initVector view))

private theorem packets_same (left right : registration.InitView)
    (same : RegistrationNativeSourceWriterReadback.initVector left = RegistrationNativeSourceWriterReadback.initVector right) :
    RegistrationNativeWire.initPacket left = RegistrationNativeWire.initPacket right := by
  apply Option.some.inj
  rw [← RegistrationNativePlatformPublicationConcrete.decoded left,
    ← RegistrationNativePlatformPublicationConcrete.decoded right,same]

/-- The actual ordered Ed3 and mandatory ML-signing source pipeline writes its original unsigned prekey, one-time and PQ inputs. -/
theorem begin_tuple (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (published : registration.PublishedBeaconInit (alloc.vec.Vec U8))
    (supported : .ok (.Ok published) ∈ support (RegistrationBeaconInitExecutor.begin encode control inputs coins pin)) :
    (PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec RegistrationNativePlatformConcreteSource.wire)
      (TranscriptAuthParts.absSlice published.encoded)).bind PqxdhDeploymentPublishedTuple.candidateTuple =
      some ⟨PqxdhPhase2InputBytes.word inputs.prekey_public_key,
        PqxdhPhase2InputBytes.word coins.one_time_public_key, RegistrationRootInput.pqKey inputs.pq_public_key⟩ := by
  obtain ⟨pre, preWritten, prePayload⟩ := RegistrationNativePrekeyPublication.begin_key encode control inputs coins pin published supported
  obtain ⟨one, oneWritten, onePayload⟩ := RegistrationNativeOneTimePublication.begin_key encode control inputs coins pin published supported
  obtain ⟨pq, pqWritten, pqPayload⟩ := RegistrationNativeKemPublication.begin_key encode control inputs coins pin published supported
  have preEq := Option.some.inj preWritten
  have oneSame := packets_same pre one (preEq.trans (Option.some.inj oneWritten).symm)
  have pqSame := packets_same pre pq (preEq.trans (Option.some.inj pqWritten).symm)
  have oneTail : (absBytes pre.fields.one_time_key).drop 64 = oneTimeMessage (PqxdhPhase2InputBytes.word coins.one_time_public_key) := by
    rw [show pre.fields.one_time_key = one.fields.one_time_key from congrArg (fun packet => packet.one_time_key) oneSame]
    exact onePayload
  have pqTail : (absBytes pre.fields.pq_key).drop 64 = pqMessage (RegistrationRootInput.pqKey inputs.pq_public_key) := by
    rw [show pre.fields.pq_key = pq.fields.pq_key from congrArg (fun packet => packet.pq_key) pqSame]
    exact pqPayload
  rw [← preEq]
  simp only [PqxdhDeploymentTranscript.candidateOf,PqxdhRegistrationJointRawSignatures.candidate,
    RegistrationNativeWire.ledgerCodec,RegistrationNativePlatformPublicationConcrete.decoded,
    Option.bind_eq_bind,Option.bind_some,RegistrationNativeWire.initPacket,Option.pure_def]
  simp only [PqxdhDeploymentPublishedTuple.candidateTuple,splitAttachedSignature,
    absBytes,List.length_map,Std.Array.length_eq]
  norm_num only at *
  simp only [Option.bind_eq_bind]
  change (do
    let prekey ← parsePrekeyMessage ((absBytes pre.fields.pre_key).drop 64)
    let oneTime ← parseOneTimeMessage ((absBytes pre.fields.one_time_key).drop 64)
    let pqKey ← parsePqMessage ((absBytes pre.fields.pq_key).drop 64)
    pure (Phase1KeyTuple.mk prekey oneTime pqKey)) = _
  rw [prePayload,oneTail,pqTail]
  simp
end BeaconcryptCore.Computational.RegistrationNativeConcreteTuplePublication
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcreteTuplePublication.begin_tuple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcreteTuplePublication.begin_tuple
