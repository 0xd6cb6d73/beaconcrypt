import BeaconcryptCore.Model.Pqxdh.Kdf
import VCVio.OracleComp.QueryTracking.Structures

/-!
# Exact joint HKDF stream for BeaconCrypt PQXDH

This module gives the three production HKDF-SHA-512 domains a 76-byte stream surface indexed by the exact domain bytes and input bytes.
The PQXDH root is the first 32-byte projection under `INFO_PQ`.
Initial ratchet chains use `INFO_INIT`; record key, next chain and nonce use the distinct `INFO_R` message domain. Prefix consistency applies only within one input and label address.

`ProductionHkdfPrefixConsistent` is only the functional prefix contract supplied by the fixed no-salt HKDF-SHA-512 source implementation.
It is separate from `Pqxdh.Crypto` and states no primitive-security assumption.
Replacing the public deterministic stream by a cached random stream yields valid game inequalities, but its distinguishing gap is efficiently large, as checked by `PqxdhPublicKdfCounterexample`. It is not a sound negligibility assumption. `PqxdhSecretInputKdf` instead isolates one secret-input root without randomizing public evaluations.
-/

open OracleSpec

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhJointKdf

/-- The single maximum-width stream that jointly backs every production projection. -/
abbrev JointKdfStream := List.Vector UInt8 76

/-- A canonical joint-HKDF address containing exactly the public domain bytes and input bytes. -/
structure JointKdfAddress where
  /-- The exact HKDF info string. -/
  info : Pqxdh.Bytes
  /-- The exact HKDF input keying material. -/
  input : Pqxdh.Bytes
deriving DecidableEq

/-- The private stream oracle used to back the public projection interface. -/
abbrev JointKdfRO := (JointKdfAddress →ₒ JointKdfStream)

/-- The exact no-salt PQXDH-root address. -/
def rootAddress (input : Pqxdh.Bytes) : JointKdfAddress :=
  ⟨Pqxdh.INFO_PQ, input⟩

/-- The exact no-salt initial directional-chain address. -/
def initialAddress (input : Pqxdh.Bytes) : JointKdfAddress :=
  ⟨Pqxdh.INFO_INIT, input⟩

/-- Initial and message addresses remain distinct even for identical input bytes. -/
theorem initialAddress_ne_ratchetAddress_value (initialInput messageInput : Pqxdh.Bytes) :
    initialAddress initialInput ≠ (⟨Pqxdh.INFO_R, messageInput⟩ : JointKdfAddress) :=
  fun same => Pqxdh.INFO_INIT_ne_INFO_R (congrArg JointKdfAddress.info same)

/-- The exact no-salt message-ratchet address. -/
def ratchetAddress (input : Pqxdh.Bytes) : JointKdfAddress :=
  ⟨Pqxdh.INFO_R, input⟩

/-- The two exact production domains yield distinct cache addresses for every pair of inputs. -/
theorem rootAddress_ne_ratchetAddress (rootInput ratchetInput : Pqxdh.Bytes) :
    rootAddress rootInput ≠ ratchetAddress ratchetInput := by
  intro equality
  have domainEquality := congrArg JointKdfAddress.info equality
  exact Pqxdh.INFO_PQ_ne_INFO_R domainEquality

/-- A PQXDH-root address determines its complete input bytes. -/
theorem rootAddress_injective : Function.Injective rootAddress := by
  intro left right equality
  exact congrArg JointKdfAddress.input equality

/-- A symmetric-ratchet address determines its complete input bytes. -/
theorem ratchetAddress_injective : Function.Injective ratchetAddress := by
  intro left right equality
  exact congrArg JointKdfAddress.input equality

/-- Expose the byte-list representation of one fixed-width joint stream. -/
def streamBytes (stream : JointKdfStream) : Pqxdh.Bytes :=
  stream.toList

/-- The first 32-byte projection used as a root, initial chain, or message key. -/
def first32 (stream : JointKdfStream) : Pqxdh.Bytes :=
  streamBytes stream |>.take 32

/-- The second 32-byte projection used as an initial or next chain. -/
def second32 (stream : JointKdfStream) : Pqxdh.Bytes :=
  (streamBytes stream).drop 32 |>.take 32

/-- The final 12-byte projection used as a record nonce. -/
def final12 (stream : JointKdfStream) : Pqxdh.Bytes :=
  streamBytes stream |>.drop 64

/-- The initialization-width prefix shared with the 76-byte record expansion. -/
def first64 (stream : JointKdfStream) : Pqxdh.Bytes :=
  streamBytes stream |>.take 64

/-- A joint stream has exactly the maximum 76-byte production width. -/
@[simp] theorem streamBytes_length (stream : JointKdfStream) :
    (streamBytes stream).length = 76 := by
  exact stream.toList_length

/-- The first projection has exactly the root, chain, and key width. -/
@[simp] theorem first32_length (stream : JointKdfStream) :
    (first32 stream).length = 32 := by
  simp [first32]

/-- The second projection has exactly the chain width. -/
@[simp] theorem second32_length (stream : JointKdfStream) :
    (second32 stream).length = 32 := by
  simp [second32]

/-- The final projection has exactly the IETF ChaCha20-Poly1305 nonce width. -/
@[simp] theorem final12_length (stream : JointKdfStream) :
    (final12 stream).length = 12 := by
  simp [final12]

/-- The initialization prefix has exactly two chain widths. -/
@[simp] theorem first64_length (stream : JointKdfStream) :
    (first64 stream).length = 64 := by
  simp [first64]

/-- The 64-byte initialization prefix is exactly the two shared 32-byte projections. -/
theorem first64_eq_first32_append_second32 (stream : JointKdfStream) :
    first64 stream = first32 stream ++ second32 stream := by
  simpa only [first64, first32, second32, Nat.reduceAdd] using
    (List.take_add (l := streamBytes stream) (i := 32) (j := 32))

/-- The initialization prefix followed by the nonce suffix reconstructs the complete stream. -/
theorem first64_append_final12 (stream : JointKdfStream) :
    first64 stream ++ final12 stream = streamBytes stream := by
  exact List.take_append_drop 64 (streamBytes stream)

/-- The PQXDH-root projection of a stream. -/
def rootProjection (stream : JointKdfStream) : Pqxdh.Bytes :=
  first32 stream

/-- The two initial directional chain projections of a symmetric stream. -/
def initialProjection (stream : JointKdfStream) : Pqxdh.Bytes × Pqxdh.Bytes :=
  (first32 stream, second32 stream)

/-- The message-key projection of a symmetric record-step stream. -/
def stepKey (stream : JointKdfStream) : Pqxdh.Bytes :=
  first32 stream

/-- The next-chain projection of a symmetric record-step stream. -/
def stepNext (stream : JointKdfStream) : Pqxdh.Bytes :=
  second32 stream

/-- The nonce projection of a symmetric record-step stream. -/
def stepNonce (stream : JointKdfStream) : Pqxdh.Bytes :=
  final12 stream

/-- The record-step projections exactly partition the complete stream. -/
theorem streamBytes_eq_step_parts (stream : JointKdfStream) :
    streamBytes stream = stepKey stream ++ stepNext stream ++ stepNonce stream := by
  rw [← first64_append_final12, first64_eq_first32_append_second32]
  rfl

/-- The first projection of one fixed stream is independent of the view name. This does not identify different KDF addresses. -/
@[simp] theorem initial_left_eq_stepKey (stream : JointKdfStream) :
    (initialProjection stream).1 = stepKey stream := by
  rfl

/-- The second projection of one fixed stream is independent of the view name. This does not identify different KDF addresses. -/
@[simp] theorem initial_right_eq_stepNext (stream : JointKdfStream) :
    (initialProjection stream).2 = stepNext stream := by
  rfl

/-- A canonical cache cannot assign two different streams to one repeated address. -/
theorem cached_stream_unique (cache : JointKdfRO.QueryCache)
    {address : JointKdfAddress} {left right : JointKdfStream}
    (hleft : cache address = some left) (hright : cache address = some right) :
    left = right := by
  exact Option.some.inj (hleft.symm.trans hright)

/-- Updating the canonical cache installs one complete stream at the exact address. -/
@[simp] theorem cacheQuery_same (cache : JointKdfRO.QueryCache)
    (address : JointKdfAddress) (stream : JointKdfStream) :
    (cache.cacheQuery address stream) address = some stream := by
  exact QueryCache.cacheQuery_self cache address stream

/-- Interpret the fixed production HKDF-SHA-512 implementation as one 76-byte stream answer. -/
def productionStream (c : Pqxdh.Crypto) (address : JointKdfAddress) : JointKdfStream :=
  ⟨c.hkdf address.input address.info 76, c.hkdf_length _ _ _⟩

/-- Functional source contract saying that the fixed 32- and 64-byte production calls are exact prefixes of the call returning 76 bytes.

This predicate is not a security assumption and does not strengthen the generic `Pqxdh.Crypto` interface.
It isolates the standard HKDF-Expand prefix behavior required to connect the existing length-indexed wrappers to one joint stream.
-/
structure ProductionHkdfPrefixConsistent (c : Pqxdh.Crypto) : Prop where
  /-- The 32-byte root call is the first projection of the root-domain stream. -/
  rootPrefix : ∀ input,
    c.hkdf input Pqxdh.INFO_PQ 32 = (c.hkdf input Pqxdh.INFO_PQ 76).take 32
  /-- Initialization is a prefix of the complete expansion under the same initial label. -/
  initialPrefix : ∀ input,
    c.hkdf input Pqxdh.INFO_INIT 64 = (c.hkdf input Pqxdh.INFO_INIT 76).take 64
  /-- Prefix consistency for the separate message label; never a cross-phase equality. -/
  ratchetPrefix : ∀ input,
    c.hkdf input Pqxdh.INFO_R 64 = (c.hkdf input Pqxdh.INFO_R 76).take 64

/-- The existing root wrapper is exactly the first projection at the root-domain address. -/
theorem rootSecret_eq_rootProjection (c : Pqxdh.Crypto)
    (hprefix : ProductionHkdfPrefixConsistent c) (input : Pqxdh.Bytes) :
    Pqxdh.rootSecret c input = rootProjection (productionStream c (rootAddress input)) := by
  rw [Pqxdh.rootSecret, hprefix.rootPrefix]
  rfl

/-- The existing initial-chain wrapper is exactly the two shared symmetric projections. -/
theorem rootChains_eq_initialProjection (c : Pqxdh.Crypto)
    (hprefix : ProductionHkdfPrefixConsistent c) (input : Pqxdh.Bytes) :
    Pqxdh.rootChains c input = initialProjection (productionStream c (initialAddress input)) := by
  apply Prod.ext
  · rw [Pqxdh.rootChains, hprefix.initialPrefix]
    simp [initialProjection, first32, productionStream, streamBytes, initialAddress,
      List.take_take]
  · rw [Pqxdh.rootChains, hprefix.initialPrefix]
    simp [initialProjection, second32, productionStream, streamBytes, initialAddress,
      List.drop_take]

/-- The initial output is the prefix of the stream at its own exact initial-label address. -/
theorem initialOutput_eq_initialStream_prefix (c : Pqxdh.Crypto)
    (hprefix : ProductionHkdfPrefixConsistent c) (input : Pqxdh.Bytes) :
    c.hkdf input Pqxdh.INFO_INIT 64 =
      (streamBytes (productionStream c (initialAddress input))).take 64 :=
  hprefix.initialPrefix input

/-- The existing record expansion is definitionally the complete symmetric stream. -/
theorem ratchetOut_eq_streamBytes (c : Pqxdh.Crypto) (input : Pqxdh.Bytes) :
    Pqxdh.ratchetOut c input = streamBytes (productionStream c (ratchetAddress input)) := by
  rfl

/-- The existing next-chain wrapper is definitionally the shared second projection. -/
theorem nextChain_eq_stepNext (c : Pqxdh.Crypto) (input : Pqxdh.Bytes) :
    Pqxdh.nextChain c input = stepNext (productionStream c (ratchetAddress input)) := by
  rfl

/-- The existing material wrapper is definitionally the shared first projection and final nonce projection. -/
theorem msgMaterial_eq_stepKey_stepNonce (c : Pqxdh.Crypto) (input : Pqxdh.Bytes) :
    Pqxdh.msgMaterial c input =
      (stepKey (productionStream c (ratchetAddress input)),
        stepNonce (productionStream c (ratchetAddress input))) := by
  rfl

/-- Current initial and message requests use different actual domain addresses. Their output values need not be assumed unequal. -/
theorem initialAddress_ne_ratchetAddress (initialInput messageInput : Pqxdh.Bytes) :
    initialAddress initialInput ≠ ratchetAddress messageInput :=
  initialAddress_ne_ratchetAddress_value initialInput messageInput

/-- The exact PQXDH transcript wrapper feeds the canonical root-domain stream without adding any field. -/
theorem pqxdhIKM_rootSecret_eq_rootProjection (c : Pqxdh.Crypto)
    (hprefix : ProductionHkdfPrefixConsistent c) (dh1 dh2 dh3 dh4 ss : Pqxdh.Bytes) :
    Pqxdh.rootSecret c (Pqxdh.pqxdhIKM dh1 dh2 dh3 dh4 ss) =
      rootProjection
        (productionStream c (rootAddress (Pqxdh.pqxdhIKM dh1 dh2 dh3 dh4 ss))) := by
  exact rootSecret_eq_rootProjection c hprefix _

end BeaconcryptCore.Computational.PqxdhJointKdf
