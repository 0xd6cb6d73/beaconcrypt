-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawCompile
import BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon

/-! Native ciphertext provenance of the actual tagged registration representation. The proofs use the fixed codec's mathematical prefix inverse and ordinary Phase-2 read-back; no response-origin or whole-game equality is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawIdealProvenanceCodec
open PqxdhServerAuthExperiment (Codec)
open PqxdhDeploymentIdealBeacon (ChallengeWritten ChallengeRead)
variable {Reader Response : Type}

/-- Successful inverse parsing retains exactly the bytes after the eight-byte public prefix. -/
theorem untag_payload (bytes : Pqxdh.Bytes) (sender : Std.U64) (payload : Pqxdh.Bytes)
    (found : CborTaggedCodec.untag bytes = some (sender, payload)) : payload = bytes.drop 8 := by
  unfold CborTaggedCodec.untag at found
  split_ifs at found
  · exact (congrArg Prod.snd (Option.some.inj found)).symm

/-- The source response parse recovers the same native reader result on the stripped response. -/
theorem read_strip (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (bytes : Pqxdh.Bytes)
    (response : Std.U64 × Response) (found : (CborRawCompile.sourceCodec wire parse).read2 bytes = some response) :
    (CborTaggedSimulation.boundaryWire wire parse).read2 (bytes.drop 8) = some response.2 := by
  simp only [CborRawCompile.sourceCodec, CborTaggedCodec.codec, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at found
  obtain ⟨⟨sender, raw⟩, tagged, parsed, read, same⟩ := found
  cases Option.some.inj same
  rw [← untag_payload bytes sender raw tagged]
  exact read

/-- A marked source response carrying the challenge has that exact challenge in its native stripped representation. -/
theorem written_read_strip (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (response : PqxdhServerRegistrationPublication.Response)
    (written : ChallengeWritten (CborRawCompile.sourceCodec wire parse) challenge response)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext)
    (found : ((CborTaggedSimulation.boundaryWire wire parse).read2 (CborPublicClient.strip response).serialized).bind
      (CborTaggedSimulation.boundaryWire wire parse).ciphertext = some ciphertext) :
    PqxdhPhase2InputBytes.ciphertext ciphertext = challenge := by
  obtain ⟨candidate, encrypted, carried, write⟩ := written
  obtain ⟨parsed, read, ciphertextEq, -⟩ := phase2 _ _ write
  have native := read_strip wire parse response.serialized parsed read
  change ((CborTaggedSimulation.boundaryWire wire parse).read2 (response.serialized.drop 8)).bind
    (CborTaggedSimulation.boundaryWire wire parse).ciphertext = some ciphertext at found
  rw [native, Option.bind_some] at found
  change (CborTaggedSimulation.boundaryWire wire parse).ciphertext parsed.2 = some candidate.kem_ciphertext at ciphertextEq
  rw [ciphertextEq, Option.some.injEq] at found
  rw [← found, carried]
  exact (PqxdhPhase2InputBytes.ciphertext_roundtrip ciphertext challenge).2

/-- Tagging an actual native challenge input with any public sender preserves its challenge ciphertext. -/
theorem challenge_read_tag (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (sender : Std.U64) (raw : Pqxdh.Bytes)
    (found : ChallengeRead (CborTaggedSimulation.boundaryWire wire parse) challenge raw) :
    ChallengeRead (CborRawCompile.sourceCodec wire parse) challenge (CborTaggedCodec.tag sender raw) := by
  obtain ⟨ciphertext, read, same⟩ := found
  refine ⟨ciphertext, ?_, same⟩
  cases parsed : (CborTaggedSimulation.boundaryWire wire parse).read2 raw with
  | none => simp [parsed] at read
  | some response =>
      simpa [CborRawCompile.sourceCodec, CborTaggedCodec.codec, CborTaggedCodec.untag_tag,
        CborRawCanonicalBuild.canonical, parsed] using read

end BeaconcryptCore.Computational.CborRawIdealProvenanceCodec

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceCodec.untag_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceCodec.untag_payload

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceCodec.read_strip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceCodec.read_strip

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceCodec.written_read_strip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceCodec.written_read_strip

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceCodec.challenge_read_tag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceCodec.challenge_read_tag
