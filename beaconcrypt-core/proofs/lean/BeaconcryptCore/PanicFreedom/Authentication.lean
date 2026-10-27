-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.TranscriptAuth

/-!
The full-crate authentication extraction returns normally for arbitrary represented inputs. The byte-building certificates reuse the exact transcript refinements of those same generated operations, without assumptions about hashing or signatures.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false

namespace BeaconcryptCore.PanicFreedom.Authentication

/-- Every fixed-width request transcript returns normally. -/
theorem build_init_transcript_total (fields : authentication.InitFields) (serverId : Std.U64)
    (serverEd : Std.Array Std.U8 32#usize) (serverMldsa : Std.Array Std.U8 1952#usize) :
    ∃ result, authentication.build_init_transcript fields serverId serverEd serverMldsa = ok result := by
  exact (TranscriptAuthRefinement.build_init_transcript_abs fields serverId serverEd serverMldsa).imp
    (fun _ h => h.1)

/-- Every represented response body has a normal return, including its checked length conversion. -/
theorem build_response_transcript_total (initHash : Std.Array Std.U8 64#usize)
    (fields : authentication.ResponseFields) :
    ∃ result, authentication.build_response_transcript initHash fields = ok result :=
  (TranscriptAuthRefinement.build_response_transcript_abs initHash fields).elim fun response h =>
    h.elim fun _ h => ⟨.Some response, h.1⟩

/-- Every response prefix returns normally for any application length. -/
theorem build_response_prefix_total (initHash : Std.Array Std.U8 64#usize)
    (identity ephemeral : Std.Array Std.U8 32#usize) (kem : Std.Array Std.U8 1088#usize)
    (appLength : Std.U64) :
    ∃ result, authentication.build_response_prefix initHash identity ephemeral kem appLength = ok result :=
  (TranscriptAuthRefinement.build_response_prefix_abs initHash identity ephemeral kem appLength).imp
    (fun _ h => h.1)

/-- Taking the three ordered transcript slices cannot fail. -/
theorem response_parts_total (response : authentication.ResponseTranscript) :
    ∃ result, authentication.ResponseTranscript.parts response = ok result :=
  (TranscriptAuthParts.ordered_parts response).imp (fun _ h => h.1)

/-- Both signing roles produce their fixed-width input without a panic. -/
theorem build_signature_input_total (role : authentication.AuthRole)
    (digest : Std.Array Std.U8 64#usize) :
    ∃ result, authentication.build_signature_input role digest = ok result :=
  (TranscriptAuthInputsRefinement.build_signature_input_abs role digest).imp (fun _ h => h.1)

/-- Both hash slots can be filled for any base buffer and fingerprint bytes. -/
theorem bind_associated_data_total (base : Std.Array Std.U8 281#usize)
    (server beacon : Std.Array Std.U8 64#usize) :
    ∃ result, authentication.bind_associated_data base server beacon = ok result :=
  (TranscriptAuthInputsRefinement.bind_associated_data_abs base server beacon).imp (fun _ h => h.1)

/-- Little-endian encoding covers every represented unsigned 64-bit value. -/
theorem encode_u64_le_total (value : Std.U64) :
    ∃ result, authentication.encode_u64_le value = ok result :=
  (TranscriptAuthRefinement.encode_u64_le_abs value).imp (fun _ h => h.1)

/-- Cloning either role is a normal return. -/
theorem role_clone_total (role : authentication.AuthRole) :
    ∃ result, authentication.AuthRole.Insts.CoreCloneClone.clone role = ok result :=
  ⟨role, rfl⟩

/-- The public-key width assertion holds on every supported word width. -/
theorem public_key_width_total : ∃ result, authentication._ = ok result := by
  simp [authentication._, authentication.MLDSA_PUBLIC_KEY_LEN]

/-- The transcript-hash width assertion holds on every supported word width. -/
theorem transcript_hash_width_total : ∃ result, authentication.__1 = ok result := by
  simp [authentication.__1, authentication.TRANSCRIPT_HASH_LEN]

/-- The associated-data width assertion holds on every supported word width. -/
theorem associated_data_width_total : ∃ result, authentication.__2 = ok result := by
  simp [authentication.__2, constants.ASSOCIATED_DATA_SIZE]

end BeaconcryptCore.PanicFreedom.Authentication

/-- info: 'BeaconcryptCore.PanicFreedom.Authentication.build_init_transcript_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Authentication.build_init_transcript_total
/-- info: 'BeaconcryptCore.PanicFreedom.Authentication.build_response_transcript_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Authentication.build_response_transcript_total
/-- info: 'BeaconcryptCore.PanicFreedom.Authentication.build_response_prefix_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Authentication.build_response_prefix_total
/-- info: 'BeaconcryptCore.PanicFreedom.Authentication.response_parts_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Authentication.response_parts_total
/-- info: 'BeaconcryptCore.PanicFreedom.Authentication.build_signature_input_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Authentication.build_signature_input_total
/-- info: 'BeaconcryptCore.PanicFreedom.Authentication.bind_associated_data_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Authentication.bind_associated_data_total
/-- info: 'BeaconcryptCore.PanicFreedom.Authentication.encode_u64_le_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Authentication.encode_u64_le_total
/-- info: 'BeaconcryptCore.PanicFreedom.Authentication.role_clone_total' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Authentication.role_clone_total
/-- info: 'BeaconcryptCore.PanicFreedom.Authentication.public_key_width_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Authentication.public_key_width_total
/-- info: 'BeaconcryptCore.PanicFreedom.Authentication.transcript_hash_width_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Authentication.transcript_hash_width_total
/-- info: 'BeaconcryptCore.PanicFreedom.Authentication.associated_data_width_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Authentication.associated_data_width_total
