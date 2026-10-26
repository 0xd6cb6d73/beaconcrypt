import BeaconcryptCore.Model.Pqxdh.Protocol

/-!
# Response encodings with identical X25519 evaluations

The response carries raw public-key bytes. Those bytes affect the modeled beacon only through its three X25519 evaluations. Replacing them by a distinct accepted encoding with identical evaluations preserves the entire result and final state.

The functional equality below is an explicit primitive interface condition; this module does not prove X25519 internals or assume protocol authentication. The native registration alias regression separately exercises production decoding, sequence-one completion, and subsequent traffic for the high-bit alias.
-/

set_option autoImplicit false

namespace Pqxdh.ResponseEncodingAlias

/-- Change exactly the decoded ephemeral field, retaining every other response field. -/
def replaceEphemeral (response : KexResponse) (alternative : Bytes) : KexResponse :=
  { response with ephemeralKey := alternative }

/-- Equal raw-DH replies for the two encodings; this does not assert injective encodings. -/
def SameDhReplies (c : Crypto) (left right : Bytes) : Prop :=
  ∀ secret, c.x25519 secret left = c.x25519 secret right

/-- All four role-shaped contributions agree, including the unchanged static DH1. -/
theorem beaconDHs_eq (c : Crypto) (left right : Bytes)
    (h : SameDhReplies c left right) (identity prekey oneTime server : Bytes) :
    beaconDHs c identity prekey oneTime server left =
      beaconDHs c identity prekey oneTime server right := by
  simp only [beaconDHs, h (c.xsk identity), h prekey, h oneTime]

/-- The complete optional-registration result and full retained state agree on every path. -/
theorem beaconFinish_eq (c : Crypto) (state : BeaconState) (response : KexResponse)
    (alternative : Bytes) (h : SameDhReplies c alternative response.ephemeralKey) :
    beaconFinish c state (replaceEphemeral response alternative) = beaconFinish c state response := by
  cases state <;>
    simp only [beaconFinish, replaceEphemeral, beaconRoot, beaconDHs_eq c alternative response.ephemeralKey h]

/-- Equal protocol outcomes do not imply equal decoded responses under this ordinary functional alternative. -/
theorem distinct_response_same_outcome (c : Crypto) (state : BeaconState)
    (response : KexResponse) (alternative : Bytes)
    (hne : alternative ≠ response.ephemeralKey)
    (h : SameDhReplies c alternative response.ephemeralKey) :
    replaceEphemeral response alternative ≠ response ∧
      beaconFinish c state (replaceEphemeral response alternative) = beaconFinish c state response := by
  refine ⟨?_, beaconFinish_eq c state response alternative h⟩
  intro heq
  exact hne (congrArg KexResponse.ephemeralKey heq)

end Pqxdh.ResponseEncodingAlias

/--
info: 'Pqxdh.ResponseEncodingAlias.beaconFinish_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Pqxdh.ResponseEncodingAlias.beaconFinish_eq

/--
info: 'Pqxdh.ResponseEncodingAlias.distinct_response_same_outcome' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Pqxdh.ResponseEncodingAlias.distinct_response_same_outcome
