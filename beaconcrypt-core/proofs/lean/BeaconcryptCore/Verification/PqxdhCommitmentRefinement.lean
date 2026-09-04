import BeaconcryptCore.Refinement.PqxdhCommitment

/-!
# PQXDH commitment refinement contract

This module pins the public statements and trust dependencies of the two extracted commitment refinement capstones.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
open beaconcrypt_core

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PqxdhRefinement

/-- The extracted integer encoder remains connected to the ideal little-endian encoding with its full public contract. -/
example (x : Std.U64) :
    ∃ bytes : Std.Array Std.U8 8#usize,
      commitment.encode_u64_le x = ok bytes ∧
        absBytes bytes = Pqxdh.LE64 x.val :=
  commitment_encode_u64_le_abs x

/-- The extracted transcript builder remains connected to the complete ideal CTX preimage with its full public contract. -/
example
    (key : Std.Array Std.U8 32#usize)
    (nonce : Std.Array Std.U8 12#usize)
    (associatedData : Std.Array Std.U8 153#usize)
    (tag : Std.Array Std.U8 16#usize)
    (sequence senderId : Std.U64) :
    ∃ transcript : commitment.CommitmentTranscript,
      commitment.build_commitment_transcript key nonce associatedData tag sequence senderId =
          ok transcript ∧
        absBytes transcript.bytes =
          Pqxdh.ctxPreimage (absBytes key, absBytes nonce)
            ⟨absBytes associatedData, sequence.val, senderId.val⟩ (absBytes tag) :=
  build_commitment_transcript_abs key nonce associatedData tag sequence senderId

/--
info: 'PqxdhRefinement.commitment_encode_u64_le_abs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms commitment_encode_u64_le_abs

/--
info: 'PqxdhRefinement.build_commitment_transcript_abs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms build_commitment_transcript_abs

end PqxdhRefinement
