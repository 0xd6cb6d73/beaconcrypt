import BeaconcryptCore.Computational.PqxdhFullSecretInputKdf
import BeaconcryptCore.Computational.PqxdhRootTableInitialization
import BeaconcryptCore.Computational.RawCtxSourceHkdf

/-!
# Separation of the zero-salt, 192-byte Extract random oracle

This module is the first stage of the server-authentication proof (Milestone B, route R1). Route R1 adds one idealization to the existing BLAKE2b random oracle of the CTX proofs: HMAC-SHA-512 under the 64-byte all-zero key, restricted to 192-byte messages, which is zero-salt HKDF-Extract on inputs of the width of the PQXDH root input. That restricted function is modelled as a programmable random oracle, and every other HMAC evaluation stays the real function, including every HKDF-Expand call and the zero-salt Extract calls of the symmetric ratchet. This module defines the patched HMAC and proves that the restriction is coherent: patching the root slice changes no other HMAC evaluation that the protocol makes.

The patch. `romHmac hmac table` answers `table message` when the key is `zeroSalt` and the message is 192 bytes long, and `hmac.eval key message` otherwise (`eval_other`). Outside that slice the patch is the real function for every table (`eval_other`), so the idealization reprograms that slice and nothing else; the real function is the patch at its own values (`romHmac_extract`). The table and the real HMAC are parameters, and every statement holds for every table; only `production_ratchet_unchanged` relates the HMAC to the production source. The lazily sampled table, and its sharing between the honest root derivations and the adversary's HMAC queries, belong to the later family module `PqxdhExtractRomFamily`. The model has a single zero key, because RFC 5869 defines an absent salt as HashLen zero bytes and RFC 2104 pads shorter keys with zero bytes, so the empty salt, the 64-byte zero salt and the all-zero block key define the same function.

Separation by length, from the extracted code. The extracted core hands the adapter exactly two kinds of Extract input. The root input `pqxdh.RootKeyInput` holds 192 bytes (`root_input_eq`; `Extraction/Types.lean:149-150`, Rust `beaconcrypt-core/src/pqxdh.rs:358-360`). The ratchet request `ratchet.SymmetricRatchetKdfRequest` holds a 32-byte input and a 41-byte label (`ratchet_input_ne`; `Extraction/Types.lean:40-42`, Rust `beaconcrypt-core/src/ratchet.rs:162-165`), and it serves both the 64-byte initial derivation and the 76-byte ongoing step. So a zero-salt Extract lands in the table exactly for root inputs (`extract_root`) and is real for every ratchet input (`extract_other`). Expand queries are keyed by a PRK and have 47 bytes (the root block `INFO_PQ ‖ 1`), 42 or 106 bytes (the two ratchet blocks under the 41-byte `INFO_R`) or 111 bytes (the second block under `INFO_PQ`). None is 192 bytes long, so no Expand query enters the table even when a PRK happens to equal `zeroSalt` (`expandRoot_same`, `expandFull_same`).

Consequences for the protocol. `production_ratchet_unchanged`: under the existing functional contracts `SourceFullCorrect` and the ratchet prefix contract carried by the `FixedHkdfSha512NoSaltSource` bundle (`ProductionHkdfPrefixConsistent.ratchetPrefix`), the 76-byte and 64-byte production ratchet responses at every request the extracted core issues equal HKDF over the patched HMAC, for every table. These are `RawCtxSourceHkdf.response`, the ongoing response used by the record sealing and opening handlers, and `PqxdhRootTableInitialization.initialResponse`, the initial response of the Server's registration build (`PqxdhServerRegistrationPublication.build`), which the planned experiment (stage B4a) assigns to the Beacon's initialization callback. `RawCtxSourceHkdf.initialResponse`, which the existing live Beacon Phase 2 module uses, has the same definition, so the statement applies to it by `rfl`. The idealized world therefore computes the same ratchet as production, and the adversary can recompute it locally with the real function. `root_under_patch`: over the patched HMAC, the root derived from any root input is the real 32-byte Expand of that input's table entry. This is the shape of the family's root request, one table lookup followed by one real Expand query.

Trust boundary. That production performs exactly one zero-salt Extract per request, with the request bytes as input keying material, is adapter-level trust and is not proved here. The Rust adapter has two call sites of `crypto_kdf::hkdf::sha512::extract` outside tests: `derive_root_key_input` (`beaconcrypt/src/pqxdh.rs:46-58`, called by the Server at `beaconcrypt/src/server.rs:414` and by the Beacon at `beaconcrypt/src/beacon.rs:458`) extracts from the 192-byte root input and expands 32 bytes under `PQXDH_INFO`, and `symmetric_ratchet_hkdf` (`beaconcrypt/src/ratchet.rs:86-98`, reached through `ratchet_hkdf` and `initial_ratchet_hkdf`) extracts from the 32-byte request input and expands under the request's own label. libsodium is a correct black box, and nothing about it, SHA-512 or HMAC is proved. The justification of the idealization (it is implied by modelling the whole zero-key HMAC-SHA-512 as a random oracle, which is where the HMAC indifferentiability results apply) will be argued in the documentation (stage B11) and is not proved.

Premises. No security law appears. The only premises are in `production_ratchet_unchanged`: `SourceFullCorrect`, the existing functional equation between the fixed production HKDF and the two-block HMAC expansion, and the ratchet prefix contract of the production source bundle, which ties the 64-byte initial response to the 76-byte stream. Neither is a security law. The axioms used are `propext`, `Classical.choice` and `Quot.sound` only.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhExtractRomSeparation

open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf

/-- HMAC-SHA-512 with the zero-key, 192-byte slice reprogrammed by `table`. Every other key or message length is answered by the real `hmac`. -/
def romHmac (hmac : HmacSha512) (table : Pqxdh.Bytes → HmacBlock) : HmacSha512 where
  eval key message :=
    if key = zeroSalt ∧ message.length = 192 then table message else hmac.eval key message

/-- Outside the zero-key, 192-byte slice the patched HMAC is the real function. -/
theorem eval_other (hmac : HmacSha512) (table : Pqxdh.Bytes → HmacBlock) (key : HmacBlock)
    (message : Pqxdh.Bytes) (outside : ¬(key = zeroSalt ∧ message.length = 192)) :
    (romHmac hmac table).eval key message = hmac.eval key message := by
  simp only [romHmac, outside, ↓reduceIte]

/-- Patching with the real function's own values gives back the real function; that the patch leaves every evaluation outside the zero-key, 192-byte slice unchanged for every table is `eval_other`. -/
theorem romHmac_extract (hmac : HmacSha512) : romHmac hmac (extract hmac) = hmac := by
  cases hmac with
  | mk eval =>
    simp only [romHmac, extract, HmacSha512.mk.injEq]
    funext key message
    split
    · next hit => rw [hit.1]
    · rfl

/-- Every ratchet request of the extracted core has a 32-byte input (`Extraction/Types.lean:40-42`), so it is never a 192-byte Extract input. -/
theorem ratchet_input_ne (request : beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest) :
    (absBytes request.input).length ≠ 192 := by
  simp

/-- Every root input assembled by the extracted core has exactly 192 bytes (`Extraction/Types.lean:149-150`). -/
theorem root_input_eq (input : beaconcrypt_core.pqxdh.RootKeyInput) :
    (absBytes input.bytes).length = 192 := by
  simp

/-- A zero-salt Extract of any input that is not 192 bytes long is the real Extract. -/
theorem extract_other (hmac : HmacSha512) (table : Pqxdh.Bytes → HmacBlock) (input : Pqxdh.Bytes)
    (other : input.length ≠ 192) : extract (romHmac hmac table) input = extract hmac input := by
  simp [extract, romHmac, other]

/-- A zero-salt Extract of a 192-byte input is the table entry at that input. -/
theorem extract_root (hmac : HmacSha512) (table : Pqxdh.Bytes → HmacBlock) (input : Pqxdh.Bytes)
    (width : input.length = 192) : extract (romHmac hmac table) input = table input := by
  simp [extract, romHmac, width]

/-- The 32-byte root Expand is unchanged for every PRK, including a PRK equal to the zero key, because its 47-byte message is outside the table. -/
theorem expandRoot_same (hmac : HmacSha512) (table : Pqxdh.Bytes → HmacBlock) (prk : HmacBlock) :
    expandRoot (romHmac hmac table) prk = expandRoot hmac prk := by
  simp [expandRoot, romHmac, rootExpandInput, Pqxdh.INFO_PQ]

/-- The two-block 76-byte Expand is unchanged in both production domains and for every PRK, because its messages have 42, 47, 106 or 111 bytes. -/
theorem expandFull_same (hmac : HmacSha512) (table : Pqxdh.Bytes → HmacBlock)
    (domain : FixedHkdfDomain) (prk : HmacBlock) :
    expandFull (romHmac hmac table) domain prk = expandFull hmac domain prk := by
  cases domain <;>
    simp [expandFull, romHmac, firstExpandInput, secondExpandInput, FixedHkdfDomain.info,
      Pqxdh.INFO_PQ, Pqxdh.INFO_R]

/-- The production ratchet responses at every request the extracted core issues (its 32-byte input under the fixed ratchet label) are HKDF over the patched HMAC, for every table: the 76-byte ongoing response and the 64-byte initial response alike. -/
theorem production_ratchet_unchanged (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceFullCorrect source hmac) (table : Pqxdh.Bytes → HmacBlock)
    (input : Std.Array Std.U8 32#usize) :
    absBytes (RawCtxSourceHkdf.response source.crypto
        ⟨input, beaconcrypt_core.ratchet.SYM_RATCHET_INFO⟩).bytes =
      (expandFull (romHmac hmac table) .ratchet
        (extract (romHmac hmac table) (absBytes input))).toList ∧
    absBytes (PqxdhRootTableInitialization.initialResponse source.crypto
        ⟨input, beaconcrypt_core.ratchet.SYM_RATCHET_INFO⟩).bytes =
      (initialPrefix (expandFull (romHmac hmac table) .ratchet
        (extract (romHmac hmac table) (absBytes input)))).toList := by
  have other : (absBytes input).length ≠ 192 := by simp
  have patched :
      expandFull (romHmac hmac table) .ratchet (extract (romHmac hmac table) (absBytes input)) =
        expandFull hmac .ratchet (extract hmac (absBytes input)) := by
    rw [extract_other hmac table (absBytes input) other, expandFull_same]
  have full : source.crypto.hkdf (absBytes input) Pqxdh.INFO_R 76 =
      (expandFull hmac .ratchet (extract hmac (absBytes input))).toList :=
    congrArg List.Vector.toList (correct .ratchet (absBytes input))
  have info : absBytes beaconcrypt_core.ratchet.SYM_RATCHET_INFO = Pqxdh.INFO_R :=
    PqxdhInitialRatchetComplementarity.absBytes_ratchetSymmetricInfo
  rw [patched]
  constructor
  · rw [RawCtxSourceHkdf.response_bytes]
    simpa only [info] using full
  · rw [PqxdhRootTableInitialization.initialResponse_bytes]
    simp only [info, source.prefixConsistent.ratchetPrefix, full, initialPrefix,
      List.Vector.toList_take]

/-- Over the patched HMAC the 32-byte root derived from any extracted root input is the real Expand of that input's table entry. -/
theorem root_under_patch (hmac : HmacSha512) (table : Pqxdh.Bytes → HmacBlock)
    (input : beaconcrypt_core.pqxdh.RootKeyInput) :
    expandRoot (romHmac hmac table) (extract (romHmac hmac table) (absBytes input.bytes)) =
      expandRoot hmac (table (absBytes input.bytes)) := by
  rw [extract_root hmac table _ (root_input_eq input), expandRoot_same]

end BeaconcryptCore.Computational.PqxdhExtractRomSeparation

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomSeparation.eval_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomSeparation.eval_other

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomSeparation.romHmac_extract' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomSeparation.romHmac_extract

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomSeparation.ratchet_input_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomSeparation.ratchet_input_ne

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomSeparation.root_input_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomSeparation.root_input_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomSeparation.extract_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomSeparation.extract_other

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomSeparation.extract_root' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomSeparation.extract_root

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomSeparation.expandRoot_same' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomSeparation.expandRoot_same

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomSeparation.expandFull_same' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomSeparation.expandFull_same

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomSeparation.production_ratchet_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomSeparation.production_ratchet_unchanged

/-- info: 'BeaconcryptCore.Computational.PqxdhExtractRomSeparation.root_under_patch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhExtractRomSeparation.root_under_patch
