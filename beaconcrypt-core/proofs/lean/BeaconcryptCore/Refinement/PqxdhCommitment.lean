import BeaconcryptCore.Refinement.PqxdhCore

/-!
# PQXDH commitment refinement

This module connects the current Hax-extracted commitment helpers to the ideal
PQXDH commitment representation.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result
open beaconcrypt_core

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PqxdhRefinement

/-- The commitment and registration helpers use the same extracted little-endian
encoding implementation. -/
theorem commitment_encode_u64_le_eq_registration (x : Std.U64) :
    commitment.encode_u64_le x =
      pqxdh.registration_key_id_binding x >>= fun b => ok b.bytes := by
  rfl

/-- **Extracted commitment integer refinement.** The eight bytes returned by the
current extracted commitment helper are exactly the ideal `Pqxdh.LE64` encoding. -/
theorem commitment_encode_u64_le_abs (x : Std.U64) :
    ∃ bytes : Std.Array Std.U8 8#usize,
      commitment.encode_u64_le x = ok bytes ∧
        absBytes bytes = Pqxdh.LE64 x.val := by
  obtain ⟨binding, hbinding, habs⟩ := registration_key_id_binding_abs x
  refine ⟨binding.bytes, ?_, habs⟩
  rw [commitment_encode_u64_le_eq_registration, hbinding]
  rfl

end PqxdhRefinement
