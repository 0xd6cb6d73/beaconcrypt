import BeaconcryptCore.Model.Pqxdh.Theorems

/-!
# A concrete instance of the PQXDH primitive interface

The ideal model of `pqxdh_spec.md` is parametric in `Pqxdh.Crypto`, a bundle of
cryptographic operations together with the correctness and length assumptions the
protocol relies on.  This file exhibits a concrete (toy, deliberately insecure)
instance `Pqxdh.Toy.toyCrypto` satisfying every one of those assumptions.

Its purpose is non-vacuity: it shows that the assumption bundle is consistent, so
none of the results proved about the model holds merely because no `Crypto` exists.
It is *not* a model of the real primitives and must never be used for anything else.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxRecDepth 4000

namespace Pqxdh
namespace Toy

/-- Pad (or truncate) a byte string to exactly `n` bytes. -/
def padTo (n : ℕ) (b : Bytes) : Bytes := (b ++ List.replicate n 0).take n

@[simp] theorem padTo_length (n : ℕ) (b : Bytes) : (padTo n b).length = n := by
  simp only [padTo, List.length_take, List.length_append, List.length_replicate]
  omega

theorem padTo_of_length {n : ℕ} {b : Bytes} (h : b.length = n) : padTo n b = b := by
  rw [padTo, ← h, List.take_left]

@[simp] theorem padTo_idem (n : ℕ) (b : Bytes) : padTo n (padTo n b) = padTo n b :=
  padTo_of_length (padTo_length n b)

theorem take_padTo_append (n : ℕ) (b m : Bytes) : (padTo n b ++ m).take n = padTo n b :=
  List.take_left' (padTo_length n b)

theorem drop_padTo_append (n : ℕ) (b m : Bytes) : (padTo n b ++ m).drop n = m :=
  List.drop_left' (padTo_length n b)

/-- Toy primitives satisfying all the ideal assumptions of `Pqxdh.Crypto`.  They are
completely insecure: "keys" are paddings of their inputs, "encryption" is the
identity and the "hashes" are truncations.  The instance exists only to show that the
assumptions of the model are jointly satisfiable. -/
def toyCrypto : Crypto where
  edPub sk := padTo 32 sk
  sign sk m := padTo 32 sk ++ m
  verify pk att := if att.take 32 = pk ∧ 32 ≤ att.length then some (att.drop 32) else none
  xsk sk := padTo 32 sk
  xpkConv p := some (padTo 32 p)
  xpub s := padTo 32 s
  x25519 a b := List.zipWith (· ^^^ ·) (padTo 32 a) (padTo 32 b)
  kemPub sk := padTo 1184 sk
  encap pk coins :=
    (padTo 32 (pk ++ coins) ++ List.replicate 1056 0, padTo 32 (pk ++ coins))
  decap _ ct := if 32 ≤ ct.length then some (ct.take 32) else none
  hkdf ikm info L := padTo L (ikm ++ info)
  aeadSeal k n ad pt := (pt, padTo 16 (k ++ n ++ ad ++ pt))
  aeadOpen k n ad ct tag := if tag = padTo 16 (k ++ n ++ ad ++ ct) then some ct else none
  blake2b x := padTo 64 x
  verify_sign := by
    intro sk m
    simp only [take_padTo_append, true_and, List.length_append, padTo_length]
    rw [if_pos (by omega), drop_padTo_append]
  conv_agree := by intro sk; simp
  dh_comm := by
    intro a b
    show List.zipWith (· ^^^ ·) (padTo 32 a) (padTo 32 (padTo 32 b))
      = List.zipWith (· ^^^ ·) (padTo 32 b) (padTo 32 (padTo 32 a))
    rw [padTo_idem, padTo_idem, List.zipWith_comm]
    exact congrArg (fun f => List.zipWith f (padTo 32 b) (padTo 32 a))
      (funext fun x => funext fun y => UInt8.xor_comm y x)
  decap_encap := by
    intro sk coins
    show (if 32 ≤ (padTo 32 (padTo 1184 sk ++ coins) ++ List.replicate 1056 0).length then
        some ((padTo 32 (padTo 1184 sk ++ coins) ++ List.replicate 1056 0).take 32)
      else none) = some (padTo 32 (padTo 1184 sk ++ coins))
    rw [if_pos (by simp), take_padTo_append]
  aead_open_seal := by
    intro k n ad pt
    show (if padTo 16 (k ++ n ++ ad ++ pt) = padTo 16 (k ++ n ++ ad ++ pt) then some pt
      else none) = some pt
    rw [if_pos rfl]
  edPub_length := by intro sk; simp
  xpub_length := by intro sk; simp
  x25519_length := by intro a b; simp
  kemPub_length := by intro sk; simp
  encap_ss_length := by intro pk coins; simp
  decap_length := by
    intro sk ct ss h
    by_cases hc : 32 ≤ ct.length
    · rw [if_pos hc] at h
      have : ss = ct.take 32 := by simpa using h.symm
      simp [this, hc]
    · rw [if_neg hc] at h
      exact absurd h (by simp)
  hkdf_length := by intro ikm info L; simp
  aeadSeal_tag_length := by intro k n ad pt; simp
  blake2b_length := by intro x; simp

/-- The assumptions bundled in `Pqxdh.Crypto` are satisfiable, so the ideal model is
not vacuous. -/
theorem crypto_nonempty : Nonempty Crypto := ⟨toyCrypto⟩

/-! ## A concrete honest run

The side conditions of `Pqxdh.HonestRun.Ok` are satisfiable as well, so the honest
agreement results apply to an actual run. -/

/-- A concrete honest registration over the toy primitives. -/
def demo : HonestRun where
  c := toyCrypto
  ikSkS := [1]
  sid := 7
  n := 3
  peers := []
  consumed := []
  ikSkB := [2]
  preSkB := [3]
  otSkB := [4]
  kemSkB := [9]
  eSk := [5]
  coins := [6]
  app := [65]

/-- The concrete run satisfies every side condition of an honest run. -/
theorem demo_ok : demo.Ok :=
  ⟨by decide, by decide, by decide, rfl, by decide⟩

/-- On the concrete run the server emits its response and commits the peer. -/
example :
    serverRespond demo.c demo.server demo.initMsg demo.eSk demo.coins (some demo.app)
      = (.ok demo.response, demo.server') :=
  demo.serverStep demo_ok

/-- On the concrete run the beacon accepts and becomes established with identifier
`4 = n_S + 1`. -/
example :
    beaconFinish demo.c demo.beaconInitSent demo.response
      = (.ok 4, demo.beaconEstablished) :=
  demo.beaconStep demo_ok

end Toy
end Pqxdh
