-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationPreflightSix
import BeaconcryptCore.Refinement.RegistrationSchemaAtoms
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Actual source prefix stripping and all six original primitive-field checks accept each complete source Init or Response serializer payload when the original complete-message size gate admits it. The concrete source field arrays, literal prefix arrays and final empty borrowed tail are preserved. Application bytes and U64 key identifiers are arbitrary. -/
namespace BeaconcryptCore.Refinement.RegistrationPreflightRecords
open beaconcrypt_parse cbordetveraux
open RegistrationHeaderCanonical RegistrationCanonicalTrace RegistrationSchemaAtoms RegistrationPreflightSix

def initStart : Slice U8 := (Array.make 3#usize [136#u8, 2#u8, 0#u8]).to_slice
def responseStart : Slice U8 := (Array.make 3#usize [136#u8, 2#u8, 1#u8]).to_slice

def initKinds : Array U8 6#usize := kinds 2#u8 2#u8 2#u8 2#u8 2#u8 2#u8
def responseKinds : Array U8 6#usize := kinds 2#u8 2#u8 2#u8 2#u8 0#u8 2#u8

theorem init_start_bytes : initStart.val = [136#u8, 2#u8, 0#u8] := rfl
theorem response_start_bytes : responseStart.val = [136#u8, 2#u8, 1#u8] := rfl

theorem init_kinds_source : initKinds = Array.repeat 6#usize 2#u8 := rfl
theorem response_kinds_source : responseKinds = Array.make 6#usize [2#u8, 2#u8, 2#u8, 2#u8, 0#u8, 2#u8] := rfl

structure InitRun (input : Slice U8) where
  begin : Start input initStart
  fields : Chain begin.tail 2#u8 2#u8 2#u8 2#u8 2#u8 2#u8

set_option backward.isDefEq.respectTransparency false in
theorem build_init (input : Slice U8) (value : transport.initkex)
    (contents : input.val = 136#u8 :: RegistrationSerializerInitBytes.payload value) :
    Nonempty (InitRun input) := by
  have whole : input.val = initStart.val ++ atomsBytes
    [ .bytes value.identity_key, .bytes value.pre_key, .bytes value.one_time_key, .bytes value.pq_key, .bytes value.mldsa_public_key, .bytes value.signature ] := by
    simpa [init_start_bytes, RegistrationSerializerInitBytes.payload, RegistrationSerializerInitBytes.fieldBytes,
      atomsBytes, atomBytes, List.append_assoc] using contents
  obtain ⟨begin, beginBytes⟩ := start input initStart
    (atomsBytes [ .bytes value.identity_key, .bytes value.pre_key, .bytes value.one_time_key, .bytes value.pq_key, .bytes value.mldsa_public_key, .bytes value.signature ]) whole
  obtain ⟨first, firstBytes⟩ := bytes_stage begin.tail value.identity_key
    (atomsBytes [ .bytes value.pre_key, .bytes value.one_time_key, .bytes value.pq_key, .bytes value.mldsa_public_key, .bytes value.signature ]) (by simpa only [atomsBytes, atomBytes] using beginBytes)
  obtain ⟨second, secondBytes⟩ := bytes_stage first.tail value.pre_key
    (atomsBytes [ .bytes value.one_time_key, .bytes value.pq_key, .bytes value.mldsa_public_key, .bytes value.signature ]) (by simpa only [atomsBytes, atomBytes] using firstBytes)
  obtain ⟨third, thirdBytes⟩ := bytes_stage second.tail value.one_time_key
    (atomsBytes [ .bytes value.pq_key, .bytes value.mldsa_public_key, .bytes value.signature ]) (by simpa only [atomsBytes, atomBytes] using secondBytes)
  obtain ⟨fourth, fourthBytes⟩ := bytes_stage third.tail value.pq_key
    (atomsBytes [ .bytes value.mldsa_public_key, .bytes value.signature ]) (by simpa only [atomsBytes, atomBytes] using thirdBytes)
  obtain ⟨fifth, fifthBytes⟩ := bytes_stage fourth.tail value.mldsa_public_key
    (atomsBytes [ .bytes value.signature ]) (by simpa only [atomsBytes, atomBytes] using fourthBytes)
  obtain ⟨sixth, sixthBytes⟩ := bytes_stage fifth.tail value.signature
    (atomsBytes []) (by simpa only [atomsBytes, atomBytes] using fifthBytes)
  exact ⟨{ begin := begin, fields := { first := first, second := second, third := third, fourth := fourth, fifth := fifth, sixth := sixth, consumed := sixthBytes } }⟩

theorem init (input : Slice U8) (value : transport.initkex)
    (contents : input.val = 136#u8 :: RegistrationSerializerInitBytes.payload value)
    (admitted : input.length ≤ 33_554_432) :
    preflight input initStart initKinds = .ok (.Some ()) := by
  obtain ⟨work⟩ := build_init input value contents
  exact run input initStart 2#u8 2#u8 2#u8 2#u8 2#u8 2#u8 work.begin work.fields admitted

structure ResponseRun (input : Slice U8) where
  begin : Start input responseStart
  fields : Chain begin.tail 2#u8 2#u8 2#u8 2#u8 0#u8 2#u8

set_option backward.isDefEq.respectTransparency false in
theorem build_response (input : Slice U8) (value : transport.kexresponse)
    (contents : input.val = 136#u8 :: RegistrationSerializerResponseBytes.payload value) :
    Nonempty (ResponseRun input) := by
  have whole : input.val = responseStart.val ++ atomsBytes
    [ .bytes value.identity_key, .bytes value.ephemeral_key, .bytes value.kem_cipher_text, .bytes value.app_cipher_text, .uint value.key_id, .bytes value.signature ] := by
    simpa [response_start_bytes, RegistrationSerializerResponseBytes.payload, RegistrationSerializerInitBytes.fieldBytes,
      atomsBytes, atomBytes, List.append_assoc] using contents
  obtain ⟨begin, beginBytes⟩ := start input responseStart
    (atomsBytes [ .bytes value.identity_key, .bytes value.ephemeral_key, .bytes value.kem_cipher_text, .bytes value.app_cipher_text, .uint value.key_id, .bytes value.signature ]) whole
  obtain ⟨first, firstBytes⟩ := bytes_stage begin.tail value.identity_key
    (atomsBytes [ .bytes value.ephemeral_key, .bytes value.kem_cipher_text, .bytes value.app_cipher_text, .uint value.key_id, .bytes value.signature ]) (by simpa only [atomsBytes, atomBytes] using beginBytes)
  obtain ⟨second, secondBytes⟩ := bytes_stage first.tail value.ephemeral_key
    (atomsBytes [ .bytes value.kem_cipher_text, .bytes value.app_cipher_text, .uint value.key_id, .bytes value.signature ]) (by simpa only [atomsBytes, atomBytes] using firstBytes)
  obtain ⟨third, thirdBytes⟩ := bytes_stage second.tail value.kem_cipher_text
    (atomsBytes [ .bytes value.app_cipher_text, .uint value.key_id, .bytes value.signature ]) (by simpa only [atomsBytes, atomBytes] using secondBytes)
  obtain ⟨fourth, fourthBytes⟩ := bytes_stage third.tail value.app_cipher_text
    (atomsBytes [ .uint value.key_id, .bytes value.signature ]) (by simpa only [atomsBytes, atomBytes] using thirdBytes)
  obtain ⟨fifth, fifthBytes⟩ := uint_stage fourth.tail value.key_id
    (atomsBytes [ .bytes value.signature ]) (by simpa only [atomsBytes, atomBytes] using fourthBytes)
  obtain ⟨sixth, sixthBytes⟩ := bytes_stage fifth.tail value.signature
    (atomsBytes []) (by simpa only [atomsBytes, atomBytes] using fifthBytes)
  exact ⟨{ begin := begin, fields := { first := first, second := second, third := third, fourth := fourth, fifth := fifth, sixth := sixth, consumed := sixthBytes } }⟩

theorem response (input : Slice U8) (value : transport.kexresponse)
    (contents : input.val = 136#u8 :: RegistrationSerializerResponseBytes.payload value)
    (admitted : input.length ≤ 33_554_432) :
    preflight input responseStart responseKinds = .ok (.Some ()) := by
  obtain ⟨work⟩ := build_response input value contents
  exact run input responseStart 2#u8 2#u8 2#u8 2#u8 0#u8 2#u8 work.begin work.fields admitted

end BeaconcryptCore.Refinement.RegistrationPreflightRecords

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightRecords.init_start_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightRecords.init_start_bytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightRecords.response_start_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightRecords.response_start_bytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightRecords.init_kinds_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightRecords.init_kinds_source

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightRecords.response_kinds_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightRecords.response_kinds_source

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightRecords.build_init' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightRecords.build_init

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightRecords.init' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightRecords.init

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightRecords.build_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightRecords.build_response

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightRecords.response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightRecords.response
