import BeaconcryptCore.Model.Pqxdh.Primitives
import VCVio.CryptoFoundations.SignatureAlg
import VCVio.OracleComp.QueryTracking.SubSpec
import VCVio.OracleComp.SimSemantics.StateT.StateSeparating

/-!
# One-shot Phase-1 Ed25519 EUF-CMA bridge

This module models one target honest Beacon identity and the sole successfully returned Phase-1 bundle permitted by the source lifecycle. The public transcript contains the tagged identity, attached prekey/one-time/PQ fields, and arbitrary public context, but never the identity secret key or an Ed25519-derived X25519 secret.

The honest wrapper signs the exact source messages in prekey, one-time, PQ order. Acceptance parses the identity, checks attached signatures in PQ, prekey, one-time order, and then applies the core identity/prekey/one-time/PQ tag and width parsers. The bad event is restricted to the target honest identity and compares the decoded key tuple, so attacker-owned self-signed registrations and new signatures on an already signed message are not misclassified as weak-EUF forgeries.

The reduction selects the first changed canonical message in server verification order and therefore charges exactly one generic VCVio weak EUF-CMA advantage, with no three-way guess. Successful wrapper outputs contain exactly the three canonical signing messages; structurally the wrapper makes at most three signing-interface calls. Material-generation and source-adversary base caps are tracked separately, while key generation, signing, and verification work internal to the opaque signature scheme remains inside the named primitive endpoint.

No Ed25519 algorithm or implementation security, Cap'n Proto/libsodium/FFI refinement, signature uniqueness or strong EUF, public-key uniqueness, multiple successful bundle coherence, multi-user lifting, attacker-owned registration exclusion, reveal safety, QPT claim, or end-to-end protocol theorem is proved here. In particular, generic EUF-CMA does not simulate production's later Ed25519-to-X25519 related-key conversion; this stage stops at attached-field origin authentication. The equality between production attached verification and exact 64-byte splitting plus detached verification is an explicit adapter premise.
-/

open OracleSpec OracleComp ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhEd25519EufCma

abbrev Ed25519PublicKey := List.Vector UInt8 32
abbrev Ed25519Signature := List.Vector UInt8 64
abbrev X25519PublicKey := List.Vector UInt8 32
abbrev MlKem768PublicKey := List.Vector UInt8 1184

def attachSignature (signature : Ed25519Signature)
    (message : Pqxdh.Bytes) : Pqxdh.Bytes :=
  signature.toList ++ message

def splitAttachedSignature (buffer : Pqxdh.Bytes) :
    Option (Ed25519Signature × Pqxdh.Bytes) :=
  if h : 64 ≤ buffer.length then
    some (⟨buffer.take 64, by simp [h]⟩, buffer.drop 64)
  else
    none

@[simp] theorem splitAttachedSignature_attach
    (signature : Ed25519Signature) (message : Pqxdh.Bytes) :
    splitAttachedSignature (attachSignature signature message) =
      some (signature, message) := by
  unfold splitAttachedSignature attachSignature
  simp

theorem splitAttachedSignature_eq_none_iff (buffer : Pqxdh.Bytes) :
    splitAttachedSignature buffer = none ↔ buffer.length < 64 := by
  unfold splitAttachedSignature
  split <;> simp_all

theorem splitAttachedSignature_eq_some_iff
    (buffer : Pqxdh.Bytes) (signature : Ed25519Signature)
    (message : Pqxdh.Bytes) :
    splitAttachedSignature buffer = some (signature, message) ↔
      buffer = attachSignature signature message := by
  constructor
  · intro parsed
    unfold splitAttachedSignature at parsed
    split at parsed
    · rename_i enough
      have pairEquality :
          ((⟨buffer.take 64, by simp [enough]⟩ : Ed25519Signature),
            buffer.drop 64) = (signature, message) :=
        Option.some.inj parsed
      have signatureEquality : buffer.take 64 = signature.toList :=
        congrArg (fun pair : Ed25519Signature × Pqxdh.Bytes => pair.1.1)
          pairEquality
      have messageEquality : buffer.drop 64 = message :=
        congrArg Prod.snd pairEquality
      calc
        buffer = buffer.take 64 ++ buffer.drop 64 :=
          (List.take_append_drop 64 buffer).symm
        _ = signature.toList ++ message := by
          rw [signatureEquality, messageEquality]
        _ = attachSignature signature message := rfl
    · simp at parsed
  · rintro rfl
    exact splitAttachedSignature_attach signature message

theorem attachSignature_injective :
    Function.Injective (fun pair : Ed25519Signature × Pqxdh.Bytes =>
      attachSignature pair.1 pair.2) := by
  intro left right equality
  apply Option.some.inj
  simpa only [splitAttachedSignature_attach] using
    congrArg splitAttachedSignature equality

structure Phase1Material (Context : Type) where
  prekey : X25519PublicKey
  oneTime : X25519PublicKey
  pqKey : MlKem768PublicKey
  context : Context

structure Phase1KeyTuple where
  prekey : X25519PublicKey
  oneTime : X25519PublicKey
  pqKey : MlKem768PublicKey
deriving DecidableEq

theorem Phase1KeyTuple.ext' {left right : Phase1KeyTuple}
    (prekey : left.prekey = right.prekey)
    (oneTime : left.oneTime = right.oneTime)
    (pqKey : left.pqKey = right.pqKey) : left = right := by
  cases left
  cases right
  simp_all

def Phase1Material.keyTuple {Context : Type} (material : Phase1Material Context) :
    Phase1KeyTuple :=
  ⟨material.prekey, material.oneTime, material.pqKey⟩

def encodedIdentity (pk : Ed25519PublicKey) : Pqxdh.Bytes :=
  Pqxdh.tagSig pk.toList

def prekeyMessage (prekey : X25519PublicKey) : Pqxdh.Bytes :=
  Pqxdh.tagX Pqxdh.rolePre prekey.toList

def oneTimeMessage (oneTime : X25519PublicKey) : Pqxdh.Bytes :=
  Pqxdh.tagX Pqxdh.roleOtk oneTime.toList

def pqMessage (pqKey : MlKem768PublicKey) : Pqxdh.Bytes :=
  Pqxdh.tagPQ pqKey.toList

@[simp] theorem encodedIdentity_length (pk : Ed25519PublicKey) :
    (encodedIdentity pk).length = 33 := by
  exact Pqxdh.tagSig_length pk.toList_length

@[simp] theorem prekeyMessage_length (prekey : X25519PublicKey) :
    (prekeyMessage prekey).length = 34 := by
  exact Pqxdh.tagX_length prekey.toList_length

@[simp] theorem oneTimeMessage_length (oneTime : X25519PublicKey) :
    (oneTimeMessage oneTime).length = 34 := by
  exact Pqxdh.tagX_length oneTime.toList_length

@[simp] theorem pqMessage_length (pqKey : MlKem768PublicKey) :
    (pqMessage pqKey).length = 1185 := by
  exact Pqxdh.tagPQ_length pqKey.toList_length

theorem prekeyMessage_ne_oneTimeMessage
    (prekey oneTime : X25519PublicKey) :
    prekeyMessage prekey ≠ oneTimeMessage oneTime := by
  simp [prekeyMessage, oneTimeMessage, Pqxdh.tagX,
    Pqxdh.rolePre, Pqxdh.roleOtk]

theorem prekeyMessage_ne_pqMessage
    (prekey : X25519PublicKey) (pqKey : MlKem768PublicKey) :
    prekeyMessage prekey ≠ pqMessage pqKey := by
  exact Pqxdh.tagX_ne_tagPQ _ _ _

theorem oneTimeMessage_ne_pqMessage
    (oneTime : X25519PublicKey) (pqKey : MlKem768PublicKey) :
    oneTimeMessage oneTime ≠ pqMessage pqKey := by
  exact Pqxdh.tagX_ne_tagPQ _ _ _

def vectorOfLength? (n : ℕ) (bytes : Pqxdh.Bytes) :
    Option (List.Vector UInt8 n) :=
  if h : bytes.length = n then some ⟨bytes, h⟩ else none

@[simp] theorem vectorOfLength?_toList {n : ℕ} (value : List.Vector UInt8 n) :
    vectorOfLength? n value.toList = some value := by
  unfold vectorOfLength?
  simp

theorem vectorOfLength?_eq_some_iff {n : ℕ} (bytes : Pqxdh.Bytes)
    (value : List.Vector UInt8 n) :
    vectorOfLength? n bytes = some value ↔ bytes = value.toList := by
  unfold vectorOfLength?
  split
  · rename_i lengthEquality
    constructor
    · intro parsed
      have vectorEquality : (⟨bytes, lengthEquality⟩ : List.Vector UInt8 n) = value :=
        Option.some.inj parsed
      exact congrArg List.Vector.toList vectorEquality
    · intro equality
      subst bytes
      simp
  · rename_i wrongLength
    constructor
    · simp
    · intro equality
      subst bytes
      exact (wrongLength value.toList_length).elim

def parseIdentity (encoded : Pqxdh.Bytes) : Option Ed25519PublicKey :=
  (Pqxdh.parseSigTag encoded).bind (vectorOfLength? 32)

def parsePrekeyMessage (message : Pqxdh.Bytes) : Option X25519PublicKey :=
  (Pqxdh.parseXTag Pqxdh.rolePre message).bind (vectorOfLength? 32)

def parseOneTimeMessage (message : Pqxdh.Bytes) : Option X25519PublicKey :=
  (Pqxdh.parseXTag Pqxdh.roleOtk message).bind (vectorOfLength? 32)

def parsePqMessage (message : Pqxdh.Bytes) : Option MlKem768PublicKey :=
  (Pqxdh.parsePQTag message).bind (vectorOfLength? 1184)

@[simp] theorem parseIdentity_encodedIdentity (pk : Ed25519PublicKey) :
    parseIdentity (encodedIdentity pk) = some pk := by
  simp [parseIdentity, encodedIdentity]

@[simp] theorem parsePrekeyMessage_prekeyMessage (prekey : X25519PublicKey) :
    parsePrekeyMessage (prekeyMessage prekey) = some prekey := by
  simp [parsePrekeyMessage, prekeyMessage]

@[simp] theorem parseOneTimeMessage_oneTimeMessage (oneTime : X25519PublicKey) :
    parseOneTimeMessage (oneTimeMessage oneTime) = some oneTime := by
  simp [parseOneTimeMessage, oneTimeMessage]

@[simp] theorem parsePqMessage_pqMessage (pqKey : MlKem768PublicKey) :
    parsePqMessage (pqMessage pqKey) = some pqKey := by
  simp [parsePqMessage, pqMessage]

theorem parseIdentity_eq_some_iff (encoded : Pqxdh.Bytes)
    (pk : Ed25519PublicKey) :
    parseIdentity encoded = some pk ↔ encoded = encodedIdentity pk := by
  cases encoded with
  | nil => simp [parseIdentity, Pqxdh.parseSigTag, encodedIdentity, Pqxdh.tagSig]
  | cons head rest =>
    by_cases marker : head = 1
    · subst head
      by_cases lengthEquality : rest.length = 32
      · simp [parseIdentity, Pqxdh.parseSigTag, lengthEquality,
          vectorOfLength?_eq_some_iff, encodedIdentity, Pqxdh.tagSig]
      · simp [parseIdentity, Pqxdh.parseSigTag, lengthEquality,
          encodedIdentity, Pqxdh.tagSig]
        intro equality
        apply lengthEquality
        simp [equality]
    · simp [parseIdentity, Pqxdh.parseSigTag, marker, encodedIdentity,
        Pqxdh.tagSig]

theorem parsePrekeyMessage_eq_some_iff (message : Pqxdh.Bytes)
    (prekey : X25519PublicKey) :
    parsePrekeyMessage message = some prekey ↔
      message = prekeyMessage prekey := by
  cases message with
  | nil => simp [parsePrekeyMessage, Pqxdh.parseXTag, prekeyMessage, Pqxdh.tagX]
  | cons head tail =>
    cases tail with
    | nil => simp [parsePrekeyMessage, Pqxdh.parseXTag, prekeyMessage, Pqxdh.tagX]
    | cons role rest =>
      by_cases marker : head = 4
      · subst head
        by_cases roleEquality : role = Pqxdh.rolePre
        · subst role
          by_cases lengthEquality : rest.length = 32
          · simp [parsePrekeyMessage, Pqxdh.parseXTag, lengthEquality,
              vectorOfLength?_eq_some_iff, prekeyMessage, Pqxdh.tagX]
          · simp [parsePrekeyMessage, Pqxdh.parseXTag, lengthEquality,
              prekeyMessage, Pqxdh.tagX]
            intro equality
            apply lengthEquality
            simp [equality]
        · simp [parsePrekeyMessage, Pqxdh.parseXTag, roleEquality,
            prekeyMessage, Pqxdh.tagX]
      · simp [parsePrekeyMessage, Pqxdh.parseXTag, marker,
          prekeyMessage, Pqxdh.tagX]

theorem parseOneTimeMessage_eq_some_iff (message : Pqxdh.Bytes)
    (oneTime : X25519PublicKey) :
    parseOneTimeMessage message = some oneTime ↔
      message = oneTimeMessage oneTime := by
  cases message with
  | nil => simp [parseOneTimeMessage, Pqxdh.parseXTag, oneTimeMessage, Pqxdh.tagX]
  | cons head tail =>
    cases tail with
    | nil => simp [parseOneTimeMessage, Pqxdh.parseXTag, oneTimeMessage, Pqxdh.tagX]
    | cons role rest =>
      by_cases marker : head = 4
      · subst head
        by_cases roleEquality : role = Pqxdh.roleOtk
        · subst role
          by_cases lengthEquality : rest.length = 32
          · simp [parseOneTimeMessage, Pqxdh.parseXTag, lengthEquality,
              vectorOfLength?_eq_some_iff, oneTimeMessage, Pqxdh.tagX]
          · simp [parseOneTimeMessage, Pqxdh.parseXTag, lengthEquality,
              oneTimeMessage, Pqxdh.tagX]
            intro equality
            apply lengthEquality
            simp [equality]
        · simp [parseOneTimeMessage, Pqxdh.parseXTag, roleEquality,
            oneTimeMessage, Pqxdh.tagX]
      · simp [parseOneTimeMessage, Pqxdh.parseXTag, marker,
          oneTimeMessage, Pqxdh.tagX]

theorem parsePqMessage_eq_some_iff (message : Pqxdh.Bytes)
    (pqKey : MlKem768PublicKey) :
    parsePqMessage message = some pqKey ↔ message = pqMessage pqKey := by
  cases message with
  | nil => simp [parsePqMessage, Pqxdh.parsePQTag, pqMessage, Pqxdh.tagPQ]
  | cons head rest =>
    by_cases marker : head = 3
    · subst head
      by_cases lengthEquality : rest.length = 1184
      · simp [parsePqMessage, Pqxdh.parsePQTag, lengthEquality,
          vectorOfLength?_eq_some_iff, pqMessage, Pqxdh.tagPQ]
      · simp [parsePqMessage, Pqxdh.parsePQTag, lengthEquality,
          pqMessage, Pqxdh.tagPQ]
        intro equality
        apply lengthEquality
        simp [equality]
    · simp [parsePqMessage, Pqxdh.parsePQTag, marker, pqMessage,
        Pqxdh.tagPQ]

theorem prekeyMessage_injective : Function.Injective prekeyMessage := by
  intro left right equality
  have parsedEquality := congrArg parsePrekeyMessage equality
  simpa only [parsePrekeyMessage_prekeyMessage, Option.some.injEq] using
    parsedEquality

theorem oneTimeMessage_injective : Function.Injective oneTimeMessage := by
  intro left right equality
  have parsedEquality := congrArg parseOneTimeMessage equality
  simpa only [parseOneTimeMessage_oneTimeMessage, Option.some.injEq] using
    parsedEquality

theorem pqMessage_injective : Function.Injective pqMessage := by
  intro left right equality
  have parsedEquality := congrArg parsePqMessage equality
  simpa only [parsePqMessage_pqMessage, Option.some.injEq] using parsedEquality

def honestPhase1Messages {Context : Type} (material : Phase1Material Context) :
    List Pqxdh.Bytes :=
  [prekeyMessage material.prekey, oneTimeMessage material.oneTime,
    pqMessage material.pqKey]

theorem pqMessage_not_mem_honestPhase1Messages_of_ne {Context : Type}
    (material : Phase1Material Context) (pqKey : MlKem768PublicKey)
    (changed : pqKey ≠ material.pqKey) :
    pqMessage pqKey ∉ honestPhase1Messages material := by
  simp only [honestPhase1Messages, List.mem_cons, not_or]
  exact ⟨(prekeyMessage_ne_pqMessage material.prekey pqKey).symm,
    (oneTimeMessage_ne_pqMessage material.oneTime pqKey).symm,
    fun equality => changed (pqMessage_injective equality), by simp⟩

theorem prekeyMessage_not_mem_honestPhase1Messages_of_ne {Context : Type}
    (material : Phase1Material Context) (prekey : X25519PublicKey)
    (changed : prekey ≠ material.prekey) :
    prekeyMessage prekey ∉ honestPhase1Messages material := by
  simp only [honestPhase1Messages, List.mem_cons, not_or]
  exact ⟨fun equality => changed (prekeyMessage_injective equality),
    prekeyMessage_ne_oneTimeMessage prekey material.oneTime,
    prekeyMessage_ne_pqMessage prekey material.pqKey, by simp⟩

theorem oneTimeMessage_not_mem_honestPhase1Messages_of_ne {Context : Type}
    (material : Phase1Material Context) (oneTime : X25519PublicKey)
    (changed : oneTime ≠ material.oneTime) :
    oneTimeMessage oneTime ∉ honestPhase1Messages material := by
  simp only [honestPhase1Messages, List.mem_cons, not_or]
  exact ⟨(prekeyMessage_ne_oneTimeMessage material.prekey oneTime).symm,
    fun equality => changed (oneTimeMessage_injective equality),
    oneTimeMessage_ne_pqMessage oneTime material.pqKey, by simp⟩

/-- Four fields delivered by successful Cap'n Proto decoding, in schema order. -/
structure Phase1Candidate where
  identityKey : Pqxdh.Bytes
  preKey : Pqxdh.Bytes
  oneTimeKey : Pqxdh.Bytes
  pqKey : Pqxdh.Bytes
deriving DecidableEq

/-- The public one-bundle transcript; no identity secret key or derived X25519 secret occurs here. -/
structure Phase1PublicTranscript (Context : Type) where
  identityKey : Pqxdh.Bytes
  preKey : Pqxdh.Bytes
  oneTimeKey : Pqxdh.Bytes
  pqKey : Pqxdh.Bytes
  context : Context

def openAttached
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (pk : Ed25519PublicKey) (buffer : Pqxdh.Bytes) : Option Pqxdh.Bytes := do
  let (signature, message) ← splitAttachedSignature buffer
  if verifyFn pk message signature then some message else none

theorem openAttached_eq_some_iff
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (pk : Ed25519PublicKey) (buffer message : Pqxdh.Bytes) :
    openAttached verifyFn pk buffer = some message ↔
      ∃ signature : Ed25519Signature,
        buffer = attachSignature signature message ∧
          verifyFn pk message signature = true := by
  rcases splitEquality : splitAttachedSignature buffer with _ | pair
  · constructor
    · intro opened
      simp [openAttached, splitEquality] at opened
    · rintro ⟨signature, rfl, _⟩
      rw [splitAttachedSignature_attach] at splitEquality
      contradiction
  · rcases pair with ⟨signature, parsedMessage⟩
    have bufferEquality :
        buffer = attachSignature signature parsedMessage :=
      (splitAttachedSignature_eq_some_iff buffer signature parsedMessage).mp
        splitEquality
    subst buffer
    constructor
    · intro opened
      by_cases verified : verifyFn pk parsedMessage signature = true
      · simp [openAttached, verified] at opened
        subst message
        exact ⟨signature, rfl, verified⟩
      · simp [openAttached, verified] at opened
    · rintro ⟨otherSignature, attachedEquality, verified⟩
      have pairEquality :
          (signature, parsedMessage) = (otherSignature, message) :=
        attachSignature_injective attachedEquality
      cases pairEquality
      simp [openAttached, verified]

/-- The source-facing detached verification and core parsing tail after the Server parsed the candidate identity. -/
def decodePhase1Candidate
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (candidatePk : Ed25519PublicKey) (candidate : Phase1Candidate) :
    Option Phase1KeyTuple := do
  let pqPayload ← openAttached verifyFn candidatePk candidate.pqKey
  let prePayload ← openAttached verifyFn candidatePk candidate.preKey
  let onePayload ← openAttached verifyFn candidatePk candidate.oneTimeKey
  let _corePk ← parseIdentity candidate.identityKey
  let prekey ← parsePrekeyMessage prePayload
  let oneTime ← parseOneTimeMessage onePayload
  let pqKey ← parsePqMessage pqPayload
  return ⟨prekey, oneTime, pqKey⟩

/-- Pure detached-verification view of the production acceptance order: parse the candidate identity, verify PQ/prekey/one-time, then parse identity/prekey/one-time/PQ for the core tuple. -/
def acceptPhase1Candidate
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (candidate : Phase1Candidate) :
    Option (Ed25519PublicKey × Phase1KeyTuple) := do
  let candidatePk ← parseIdentity candidate.identityKey
  let decoded ← decodePhase1Candidate verifyFn candidatePk candidate
  return (candidatePk, decoded)

theorem acceptPhase1Candidate_eq_some_iff
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (candidate : Phase1Candidate) (pk : Ed25519PublicKey)
    (decoded : Phase1KeyTuple) :
    acceptPhase1Candidate verifyFn candidate = some (pk, decoded) ↔
      parseIdentity candidate.identityKey = some pk ∧
        decodePhase1Candidate verifyFn pk candidate = some decoded := by
  rcases identityResult : parseIdentity candidate.identityKey with _ | candidatePk
  · simp [acceptPhase1Candidate, identityResult]
  · rcases decodeResult : decodePhase1Candidate verifyFn candidatePk candidate with
      _ | candidateDecoded
    · simp [acceptPhase1Candidate, identityResult, decodeResult]
      intro equality
      subst pk
      simp [decodeResult]
    · simp [acceptPhase1Candidate, identityResult, decodeResult]
      intro equality
      subst pk
      simp [decodeResult]

theorem acceptPhase1Candidate_some_witness
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (candidate : Phase1Candidate) (pk : Ed25519PublicKey)
    (decoded : Phase1KeyTuple)
    (accepted : acceptPhase1Candidate verifyFn candidate = some (pk, decoded)) :
    candidate.identityKey = encodedIdentity pk ∧
      ∃ pqSignature preSignature oneTimeSignature : Ed25519Signature,
        candidate.pqKey = attachSignature pqSignature (pqMessage decoded.pqKey) ∧
        verifyFn pk (pqMessage decoded.pqKey) pqSignature = true ∧
        candidate.preKey = attachSignature preSignature
          (prekeyMessage decoded.prekey) ∧
        verifyFn pk (prekeyMessage decoded.prekey) preSignature = true ∧
        candidate.oneTimeKey = attachSignature oneTimeSignature
          (oneTimeMessage decoded.oneTime) ∧
        verifyFn pk (oneTimeMessage decoded.oneTime) oneTimeSignature = true := by
  obtain ⟨identityParsed, decodedResult⟩ :=
    (acceptPhase1Candidate_eq_some_iff verifyFn candidate pk decoded).mp accepted
  have identityEncoded :=
    (parseIdentity_eq_some_iff candidate.identityKey pk).mp identityParsed
  unfold decodePhase1Candidate at decodedResult
  rcases pqOpened : openAttached verifyFn pk candidate.pqKey with _ | pqPayload
  · simp [pqOpened] at decodedResult
  · simp only [pqOpened] at decodedResult
    rcases preOpened : openAttached verifyFn pk candidate.preKey with _ | prePayload
    · simp [preOpened] at decodedResult
    · simp only [preOpened] at decodedResult
      rcases oneOpened : openAttached verifyFn pk candidate.oneTimeKey with _ | onePayload
      · simp [oneOpened] at decodedResult
      · simp only [oneOpened] at decodedResult
        simp only [identityParsed] at decodedResult
        rcases preParsed : parsePrekeyMessage prePayload with _ | prekey
        · simp [preParsed] at decodedResult
        · rcases oneParsed : parseOneTimeMessage onePayload with _ | oneTime
          · simp [oneParsed] at decodedResult
          · rcases pqParsed : parsePqMessage pqPayload with _ | pqKey
            · simp [pqParsed] at decodedResult
            · simp at decodedResult
              rw [preParsed, oneParsed, pqParsed] at decodedResult
              simp at decodedResult
              have decodedEquality :
                  (⟨prekey, oneTime, pqKey⟩ : Phase1KeyTuple) = decoded :=
                decodedResult
              subst decoded
              obtain ⟨pqSignature, pqAttached, pqVerified⟩ :=
                (openAttached_eq_some_iff verifyFn pk candidate.pqKey pqPayload).mp
                  pqOpened
              obtain ⟨preSignature, preAttached, preVerified⟩ :=
                (openAttached_eq_some_iff verifyFn pk candidate.preKey prePayload).mp
                  preOpened
              obtain ⟨oneTimeSignature, oneAttached, oneVerified⟩ :=
                (openAttached_eq_some_iff verifyFn pk candidate.oneTimeKey onePayload).mp
                  oneOpened
              have preCanonical :=
                (parsePrekeyMessage_eq_some_iff prePayload prekey).mp preParsed
              have oneCanonical :=
                (parseOneTimeMessage_eq_some_iff onePayload oneTime).mp oneParsed
              have pqCanonical :=
                (parsePqMessage_eq_some_iff pqPayload pqKey).mp pqParsed
              subst prePayload
              subst onePayload
              subst pqPayload
              exact ⟨identityEncoded, pqSignature, preSignature,
                oneTimeSignature, pqAttached, pqVerified, preAttached,
                preVerified, oneAttached, oneVerified⟩
def phase1FieldSubstitutionBit {Context : Type}
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (targetPk : Ed25519PublicKey) (material : Phase1Material Context)
    (candidate : Phase1Candidate) : Bool :=
  match acceptPhase1Candidate verifyFn candidate with
  | some (candidatePk, decoded) =>
      decide (candidatePk = targetPk ∧ decoded ≠ material.keyTuple)
  | none => false

theorem phase1FieldSubstitutionBit_eq_true_iff {Context : Type}
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (targetPk : Ed25519PublicKey) (material : Phase1Material Context)
    (candidate : Phase1Candidate) :
    phase1FieldSubstitutionBit verifyFn targetPk material candidate = true ↔
      ∃ decoded : Phase1KeyTuple,
        acceptPhase1Candidate verifyFn candidate = some (targetPk, decoded) ∧
          decoded ≠ material.keyTuple := by
  rcases accepted : acceptPhase1Candidate verifyFn candidate with _ | result
  · simp [phase1FieldSubstitutionBit, accepted]
  · rcases result with ⟨candidatePk, decoded⟩
    simp [phase1FieldSubstitutionBit, accepted]

/-- Fallback pair from the first honest signing query; it is deliberately non-fresh. -/
def honestPrekeyPair {Context : Type} (material : Phase1Material Context)
    (transcript : Phase1PublicTranscript Context) : Pqxdh.Bytes × Ed25519Signature :=
  match splitAttachedSignature transcript.preKey with
  | some pair => (pair.2, pair.1)
  | none => (prekeyMessage material.prekey,
      ⟨List.replicate 64 0, by simp⟩)

/-- First syntactically typed changed field in server verification order PQ, prekey, one-time; every malformed/no-change case returns an honest queried fallback. -/
def selectPhase1Forgery {Context : Type} (material : Phase1Material Context)
    (transcript : Phase1PublicTranscript Context)
    (candidate : Phase1Candidate) : Pqxdh.Bytes × Ed25519Signature :=
  match splitAttachedSignature candidate.pqKey with
  | some (signature, message) =>
      match parsePqMessage message with
      | some pqKey =>
          if pqKey ≠ material.pqKey then (message, signature) else
            match splitAttachedSignature candidate.preKey with
            | some (signature, message) =>
                match parsePrekeyMessage message with
                | some prekey =>
                    if prekey ≠ material.prekey then (message, signature) else
                      match splitAttachedSignature candidate.oneTimeKey with
                      | some (signature, message) =>
                          match parseOneTimeMessage message with
                          | some oneTime =>
                              if oneTime ≠ material.oneTime then (message, signature)
                              else honestPrekeyPair material transcript
                          | none => honestPrekeyPair material transcript
                      | none => honestPrekeyPair material transcript
                | none => honestPrekeyPair material transcript
            | none => honestPrekeyPair material transcript
      | none => honestPrekeyPair material transcript
  | none => honestPrekeyPair material transcript

abbrev Ed25519Scheme {ι : Type} (baseSpec : OracleSpec ι) (SecretKey : Type) :=
  SignatureAlg (OracleComp baseSpec) Pqxdh.Bytes Ed25519PublicKey SecretKey
    Ed25519Signature

/-- The source adapter exposes detached verification as one pure deterministic relation. -/
def HasDeterministicVerification {ι : Type} {baseSpec : OracleSpec ι}
    {SecretKey : Type} (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool) : Prop :=
  ∀ pk message signature,
    sigAlg.verify pk message signature = pure (verifyFn pk message signature)

/-- Honest Phase-1 public values and caller context, selected after the target public key is known. -/
structure Phase1MaterialGenerator {ι : Type} (baseSpec : OracleSpec ι)
    (Context : Type) where
  main (pk : Ed25519PublicKey) : OracleComp baseSpec (Phase1Material Context)

/-- The source adversary sees only the one successful public bundle transcript. -/
structure Phase1Adversary {ι : Type} (baseSpec : OracleSpec ι)
    (Context : Type) where
  main (transcript : Phase1PublicTranscript Context) :
    OracleComp baseSpec Phase1Candidate

def honestPhase1Transcript {Context : Type} (pk : Ed25519PublicKey)
    (material : Phase1Material Context) (preSignature oneTimeSignature pqSignature :
      Ed25519Signature) : Phase1PublicTranscript Context where
  identityKey := encodedIdentity pk
  preKey := attachSignature preSignature (prekeyMessage material.prekey)
  oneTimeKey := attachSignature oneTimeSignature (oneTimeMessage material.oneTime)
  pqKey := attachSignature pqSignature (pqMessage material.pqKey)
  context := material.context

@[simp] theorem honestPrekeyPair_honestPhase1Transcript {Context : Type}
    (pk : Ed25519PublicKey) (material : Phase1Material Context)
    (preSignature oneTimeSignature pqSignature : Ed25519Signature) :
    honestPrekeyPair material
        (honestPhase1Transcript pk material preSignature oneTimeSignature pqSignature) =
      (prekeyMessage material.prekey, preSignature) := by
  simp [honestPrekeyPair, honestPhase1Transcript]

theorem phase1FieldSubstitution_selects_fresh_valid {Context : Type}
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (pk : Ed25519PublicKey) (material : Phase1Material Context)
    (transcript : Phase1PublicTranscript Context) (candidate : Phase1Candidate)
    (bad : phase1FieldSubstitutionBit verifyFn pk material candidate = true) :
    let selected := selectPhase1Forgery material transcript candidate
    verifyFn pk selected.1 selected.2 = true ∧
      selected.1 ∉ honestPhase1Messages material := by
  obtain ⟨decoded, accepted, changed⟩ :=
    (phase1FieldSubstitutionBit_eq_true_iff verifyFn pk material candidate).mp bad
  obtain ⟨_, pqCandidateSignature, preCandidateSignature,
      oneCandidateSignature, pqAttached, pqVerified, preAttached,
      preVerified, oneAttached, oneVerified⟩ :=
    acceptPhase1Candidate_some_witness verifyFn candidate pk decoded accepted
  by_cases pqChanged : decoded.pqKey ≠ material.pqKey
  · simpa [selectPhase1Forgery, pqAttached, pqChanged] using
      And.intro pqVerified
        (pqMessage_not_mem_honestPhase1Messages_of_ne material decoded.pqKey
          pqChanged)
  · by_cases preChanged : decoded.prekey ≠ material.prekey
    · simpa [selectPhase1Forgery, pqAttached, pqChanged, preAttached,
        preChanged] using
        And.intro preVerified
          (prekeyMessage_not_mem_honestPhase1Messages_of_ne material
            decoded.prekey preChanged)
    · have oneChanged : decoded.oneTime ≠ material.oneTime := by
        intro oneTimeEquality
        apply changed
        exact Phase1KeyTuple.ext' (not_ne_iff.mp preChanged) oneTimeEquality
          (not_ne_iff.mp pqChanged)
      simpa [selectPhase1Forgery, pqAttached, pqChanged, preAttached,
        preChanged, oneAttached, oneChanged] using
        And.intro oneVerified
          (oneTimeMessage_not_mem_honestPhase1Messages_of_ne material
            decoded.oneTime oneChanged)

structure Phase1ClientResult (Context : Type) where
  material : Phase1Material Context
  transcript : Phase1PublicTranscript Context
  candidate : Phase1Candidate

/-- Exactly the Beacon signing order prekey, one-time, PQ, with all source computations on the base oracle. -/
def phase1ClientMain {ι : Type} {baseSpec : OracleSpec ι} {Context : Type}
    (materialGenerator : Phase1MaterialGenerator baseSpec Context)
    (adversary : Phase1Adversary baseSpec Context) (pk : Ed25519PublicKey) :
    OracleComp (baseSpec + (Pqxdh.Bytes →ₒ Ed25519Signature))
      (Phase1ClientResult Context) := do
  let material ← OracleComp.liftComp (materialGenerator.main pk)
    (baseSpec + (Pqxdh.Bytes →ₒ Ed25519Signature))
  let preSignature ← liftM
    ((Pqxdh.Bytes →ₒ Ed25519Signature).query
      (prekeyMessage material.prekey))
  let oneTimeSignature ← liftM
    ((Pqxdh.Bytes →ₒ Ed25519Signature).query
      (oneTimeMessage material.oneTime))
  let pqSignature ← liftM
    ((Pqxdh.Bytes →ₒ Ed25519Signature).query
      (pqMessage material.pqKey))
  let transcript := honestPhase1Transcript pk material preSignature
    oneTimeSignature pqSignature
  let candidate ← OracleComp.liftComp (adversary.main transcript)
    (baseSpec + (Pqxdh.Bytes →ₒ Ed25519Signature))
  return ⟨material, transcript, candidate⟩

def phase1SigningImpl {ι : Type} {baseSpec : OracleSpec ι} {SecretKey : Type}
    (sigAlg : Ed25519Scheme baseSpec SecretKey) (pk : Ed25519PublicKey)
    (sk : SecretKey) :
    QueryImpl (baseSpec + (Pqxdh.Bytes →ₒ Ed25519Signature))
      (WriterT (QueryLog (Pqxdh.Bytes →ₒ Ed25519Signature))
        (OracleComp baseSpec)) :=
  (HasQuery.toQueryImpl (spec := baseSpec) (m := OracleComp baseSpec)).liftTarget
      (WriterT (QueryLog (Pqxdh.Bytes →ₒ Ed25519Signature))
        (OracleComp baseSpec)) +
    sigAlg.signingOracle pk sk

def phase1AppendSigningImpl {ι : Type} {baseSpec : OracleSpec ι}
    {SecretKey : Type} (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (pk : Ed25519PublicKey) (sk : SecretKey) :
    QueryImpl (baseSpec + (Pqxdh.Bytes →ₒ Ed25519Signature))
      (StateT (List Pqxdh.Bytes) (OracleComp baseSpec)) :=
  (HasQuery.toQueryImpl (spec := baseSpec) (m := OracleComp baseSpec)).liftTarget
      (StateT (List Pqxdh.Bytes) (OracleComp baseSpec)) +
    QueryImpl.appendInputLog (sigAlg.sign pk sk)

theorem phase1AppendSigningImpl_run_liftComp {ι : Type}
    {baseSpec : OracleSpec ι} {SecretKey α : Type}
    (sigAlg : Ed25519Scheme baseSpec SecretKey) (pk : Ed25519PublicKey)
    (sk : SecretKey) (computation : OracleComp baseSpec α)
    (messages : List Pqxdh.Bytes) :
    (simulateQ (phase1AppendSigningImpl sigAlg pk sk)
      (OracleComp.liftComp computation
        (baseSpec + (Pqxdh.Bytes →ₒ Ed25519Signature)))).run messages =
      (fun output => (output, messages)) <$> computation := by
  apply QueryImpl.Stateful.simulateQ_liftComp_run_of_query
  intro query state
  change ((phase1AppendSigningImpl sigAlg pk sk (.inl query)).run state) =
    (fun answer => (answer, state)) <$>
      (liftM (baseSpec.query query) : OracleComp baseSpec (baseSpec.Range query))
  simp [phase1AppendSigningImpl, HasQuery.toQueryImpl_apply]

theorem phase1AppendSigningImpl_run_liftM {ι : Type}
    {baseSpec : OracleSpec ι} {SecretKey α : Type}
    (sigAlg : Ed25519Scheme baseSpec SecretKey) (pk : Ed25519PublicKey)
    (sk : SecretKey) (computation : OracleComp baseSpec α)
    (messages : List Pqxdh.Bytes) :
    (simulateQ (phase1AppendSigningImpl sigAlg pk sk)
      (liftM computation : OracleComp
        (baseSpec + (Pqxdh.Bytes →ₒ Ed25519Signature)) α)).run messages =
      (fun output => (output, messages)) <$> computation := by
  rw [← OracleComp.liftComp_eq_liftM]
  exact phase1AppendSigningImpl_run_liftComp sigAlg pk sk computation messages

theorem phase1AppendSigningImpl_run_sign {ι : Type}
    {baseSpec : OracleSpec ι} {SecretKey : Type}
    (sigAlg : Ed25519Scheme baseSpec SecretKey) (pk : Ed25519PublicKey)
    (sk : SecretKey) (message : Pqxdh.Bytes) (messages : List Pqxdh.Bytes) :
    (phase1AppendSigningImpl sigAlg pk sk (.inr message)).run messages =
      (sigAlg.sign pk sk message >>= fun signature =>
        pure (signature, messages ++ [message])) := by
  simp [phase1AppendSigningImpl]

theorem phase1AppendSigningImpl_run_signQuery {ι : Type}
    {baseSpec : OracleSpec ι} {SecretKey : Type}
    (sigAlg : Ed25519Scheme baseSpec SecretKey) (pk : Ed25519PublicKey)
    (sk : SecretKey) (message : Pqxdh.Bytes) (messages : List Pqxdh.Bytes) :
    (simulateQ (phase1AppendSigningImpl sigAlg pk sk)
      (liftM ((Pqxdh.Bytes →ₒ Ed25519Signature).query message) :
        OracleComp (baseSpec + (Pqxdh.Bytes →ₒ Ed25519Signature))
          Ed25519Signature)).run messages =
      (sigAlg.sign pk sk message >>= fun signature =>
        pure (signature, messages ++ [message])) := by
  change (simulateQ (phase1AppendSigningImpl sigAlg pk sk)
    (liftM
      (liftM ((Pqxdh.Bytes →ₒ Ed25519Signature).query message) :
        OracleComp (Pqxdh.Bytes →ₒ Ed25519Signature) Ed25519Signature) :
      OracleComp (baseSpec + (Pqxdh.Bytes →ₒ Ed25519Signature))
        Ed25519Signature)).run messages = _
  unfold phase1AppendSigningImpl
  rw [QueryImpl.simulateQ_add_liftM_right, simulateQ_spec_query]
  simp

def phase1ClientReference {ι : Type} {baseSpec : OracleSpec ι}
    {Context SecretKey : Type} (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (materialGenerator : Phase1MaterialGenerator baseSpec Context)
    (adversary : Phase1Adversary baseSpec Context) (pk : Ed25519PublicKey)
    (sk : SecretKey) :
    OracleComp baseSpec (Phase1ClientResult Context × List Pqxdh.Bytes) := do
  let material ← materialGenerator.main pk
  let preSignature ← sigAlg.sign pk sk (prekeyMessage material.prekey)
  let oneTimeSignature ← sigAlg.sign pk sk (oneTimeMessage material.oneTime)
  let pqSignature ← sigAlg.sign pk sk (pqMessage material.pqKey)
  let transcript := honestPhase1Transcript pk material preSignature
    oneTimeSignature pqSignature
  let candidate ← adversary.main transcript
  return (⟨material, transcript, candidate⟩, honestPhase1Messages material)

theorem phase1ClientMain_logged_messages {ι : Type}
    {baseSpec : OracleSpec ι} {Context SecretKey : Type}
    (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (materialGenerator : Phase1MaterialGenerator baseSpec Context)
    (adversary : Phase1Adversary baseSpec Context) (pk : Ed25519PublicKey)
    (sk : SecretKey) :
    ((fun result : Phase1ClientResult Context ×
          QueryLog (Pqxdh.Bytes →ₒ Ed25519Signature) =>
        (result.1, result.2.map (fun entry => entry.1))) <$>
      ((simulateQ (phase1SigningImpl sigAlg pk sk)
        (phase1ClientMain materialGenerator adversary pk)).run :
          OracleComp baseSpec (Phase1ClientResult Context ×
            QueryLog (Pqxdh.Bytes →ₒ Ed25519Signature)))) =
      phase1ClientReference sigAlg materialGenerator adversary pk sk := by
  rw [show
    ((fun result : Phase1ClientResult Context ×
          QueryLog (Pqxdh.Bytes →ₒ Ed25519Signature) =>
        (result.1, result.2.map (fun entry => entry.1))) <$>
      ((simulateQ (phase1SigningImpl sigAlg pk sk)
        (phase1ClientMain materialGenerator adversary pk)).run :
          OracleComp baseSpec (Phase1ClientResult Context ×
            QueryLog (Pqxdh.Bytes →ₒ Ed25519Signature)))) =
      ((simulateQ
        (phase1AppendSigningImpl sigAlg pk sk)
        (phase1ClientMain materialGenerator adversary pk)).run [] :
          OracleComp baseSpec (Phase1ClientResult Context × List Pqxdh.Bytes)) by
      simpa [phase1SigningImpl, phase1AppendSigningImpl,
          SignatureAlg.signingOracle] using
        (QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog
          (spec₀ := baseSpec)
          (loggedSpec := Pqxdh.Bytes →ₒ Ed25519Signature)
          (m₀ := OracleComp baseSpec) (sigAlg.sign pk sk)
          (phase1ClientMain materialGenerator adversary pk) ([] : List Pqxdh.Bytes))]
  simp [phase1ClientMain, phase1ClientReference,
    phase1AppendSigningImpl_run_liftM,
    phase1AppendSigningImpl_run_signQuery, honestPhase1Messages]

def phase1ToEUFCMA {ι : Type} {baseSpec : OracleSpec ι} {Context SecretKey : Type}
    (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (materialGenerator : Phase1MaterialGenerator baseSpec Context)
    (adversary : Phase1Adversary baseSpec Context) :
    SignatureAlg.unforgeableAdv sigAlg where
  main pk := do
    let result ← phase1ClientMain materialGenerator adversary pk
    return selectPhase1Forgery result.material result.transcript result.candidate

structure Phase1SharedResult (Context : Type) where
  publicKey : Ed25519PublicKey
  client : Phase1ClientResult Context

noncomputable def phase1SharedJoint {ι : Type} {baseSpec : OracleSpec ι}
    {Context SecretKey : Type} (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (materialGenerator : Phase1MaterialGenerator baseSpec Context)
    (adversary : Phase1Adversary baseSpec Context) :
    OracleComp baseSpec (Phase1SharedResult Context) := do
  let (pk, sk) ← sigAlg.keygen
  let (result, _) ←
    phase1ClientReference sigAlg materialGenerator adversary pk sk
  return ⟨pk, result⟩

noncomputable def phase1WriterJoint {ι : Type} {baseSpec : OracleSpec ι}
    {Context SecretKey : Type} (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (materialGenerator : Phase1MaterialGenerator baseSpec Context)
    (adversary : Phase1Adversary baseSpec Context) :
    OracleComp baseSpec
      (Ed25519PublicKey × Phase1ClientResult Context ×
        QueryLog (Pqxdh.Bytes →ₒ Ed25519Signature)) := do
  let (pk, sk) ← sigAlg.keygen
  let (result, log) ←
    (simulateQ (phase1SigningImpl sigAlg pk sk)
      (phase1ClientMain materialGenerator adversary pk)).run
  return (pk, result, log)

def phase1WriterToShared {Context : Type}
    (result : Ed25519PublicKey × Phase1ClientResult Context ×
      QueryLog (Pqxdh.Bytes →ₒ Ed25519Signature)) :
    Phase1SharedResult Context :=
  ⟨result.1, result.2.1⟩

theorem phase1WriterJoint_toShared {ι : Type} {baseSpec : OracleSpec ι}
    {Context SecretKey : Type} (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (materialGenerator : Phase1MaterialGenerator baseSpec Context)
    (adversary : Phase1Adversary baseSpec Context) :
    phase1WriterToShared <$> phase1WriterJoint sigAlg materialGenerator adversary =
      phase1SharedJoint sigAlg materialGenerator adversary := by
  unfold phase1WriterJoint phase1SharedJoint phase1WriterToShared
  simp only [map_bind]
  apply bind_congr
  rintro ⟨pk, sk⟩
  rw [← phase1ClientMain_logged_messages sigAlg materialGenerator adversary pk sk]
  simp [Functor.map_map]

def phase1SourceBadBit {Context : Type}
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (joint : Phase1SharedResult Context) : Bool :=
  phase1FieldSubstitutionBit verifyFn joint.publicKey joint.client.material
    joint.client.candidate

def phase1EufBit {Context : Type}
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (joint : Phase1SharedResult Context) : Bool :=
  let selected := selectPhase1Forgery joint.client.material joint.client.transcript
    joint.client.candidate
  !decide (selected.1 ∈ honestPhase1Messages joint.client.material) &&
    verifyFn joint.publicKey selected.1 selected.2

def phase1ClientEufBit {Context : Type}
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (pk : Ed25519PublicKey)
    (result : Phase1ClientResult Context × List Pqxdh.Bytes) : Bool :=
  let selected := selectPhase1Forgery result.1.material result.1.transcript
    result.1.candidate
  !decide (selected.1 ∈ result.2) && verifyFn pk selected.1 selected.2

theorem phase1SourceBadBit_implies_eufBit {Context : Type}
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (joint : Phase1SharedResult Context)
    (bad : phase1SourceBadBit verifyFn joint = true) :
    phase1EufBit verifyFn joint = true := by
  obtain ⟨valid, fresh⟩ :=
    phase1FieldSubstitution_selects_fresh_valid verifyFn joint.publicKey
      joint.client.material joint.client.transcript joint.client.candidate bad
  simp [phase1EufBit, fresh, valid]

theorem phase1ClientEufBit_logged_eq_reference {ι : Type}
    {baseSpec : OracleSpec ι} {Context SecretKey : Type}
    (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (materialGenerator : Phase1MaterialGenerator baseSpec Context)
    (adversary : Phase1Adversary baseSpec Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (pk : Ed25519PublicKey) (sk : SecretKey) :
    ((fun result : Phase1ClientResult Context ×
          QueryLog (Pqxdh.Bytes →ₒ Ed25519Signature) =>
        let selected := selectPhase1Forgery result.1.material
          result.1.transcript result.1.candidate
        !result.2.wasQueried selected.1 &&
          verifyFn pk selected.1 selected.2) <$>
      ((simulateQ (phase1SigningImpl sigAlg pk sk)
        (phase1ClientMain materialGenerator adversary pk)).run :
          OracleComp baseSpec (Phase1ClientResult Context ×
            QueryLog (Pqxdh.Bytes →ₒ Ed25519Signature)))) =
      phase1ClientEufBit verifyFn pk <$>
        phase1ClientReference sigAlg materialGenerator adversary pk sk := by
  rw [← phase1ClientMain_logged_messages sigAlg materialGenerator adversary pk sk]
  rw [← LawfulFunctor.comp_map]
  congr 1
  funext result
  simp only [phase1ClientEufBit, Function.comp_apply,
    QueryLog.wasQueried_eq_decide_mem_map_fst]
  congr 2
  exact decide_eq_decide.mpr Iff.rfl

noncomputable def phase1FieldSubstitutionExp {ι : Type}
    {baseSpec : OracleSpec ι} {Context SecretKey : Type}
    (runtime : ProbCompRuntime (OracleComp baseSpec))
    (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (materialGenerator : Phase1MaterialGenerator baseSpec Context)
    (adversary : Phase1Adversary baseSpec Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool) :
    SPMF Bool :=
  runtime.evalDist
    (phase1WriterJoint sigAlg materialGenerator adversary >>= fun joint =>
      pure (phase1SourceBadBit verifyFn (phase1WriterToShared joint)))

noncomputable def Phase1FieldSubstitutionAdvantage {ι : Type}
    {baseSpec : OracleSpec ι} {Context SecretKey : Type}
    (runtime : ProbCompRuntime (OracleComp baseSpec))
    (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (materialGenerator : Phase1MaterialGenerator baseSpec Context)
    (adversary : Phase1Adversary baseSpec Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool) :
    ℝ≥0∞ :=
  Pr[= true | phase1FieldSubstitutionExp runtime sigAlg materialGenerator
    adversary verifyFn]

theorem phase1FieldSubstitutionExp_eq_shared {ι : Type}
    {baseSpec : OracleSpec ι} {Context SecretKey : Type}
    (runtime : ProbCompRuntime (OracleComp baseSpec))
    (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (materialGenerator : Phase1MaterialGenerator baseSpec Context)
    (adversary : Phase1Adversary baseSpec Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (h_pull : ∀ {α β : Type} (f : α → β) (mx : OracleComp baseSpec α),
      runtime.evalDist (mx >>= fun x => pure (f x)) =
        f <$> runtime.evalDist mx) :
    phase1FieldSubstitutionExp runtime sigAlg materialGenerator adversary verifyFn =
      phase1SourceBadBit verifyFn <$>
        runtime.evalDist
          (phase1SharedJoint sigAlg materialGenerator adversary) := by
  unfold phase1FieldSubstitutionExp
  rw [h_pull]
  change (phase1SourceBadBit verifyFn ∘ phase1WriterToShared) <$>
      runtime.evalDist (phase1WriterJoint sigAlg materialGenerator adversary) = _
  rw [LawfulFunctor.comp_map, ← h_pull]
  change phase1SourceBadBit verifyFn <$>
      runtime.evalDist
        (phase1WriterToShared <$>
          phase1WriterJoint sigAlg materialGenerator adversary) = _
  rw [phase1WriterJoint_toShared]

noncomputable def phase1EufBody {ι : Type} {baseSpec : OracleSpec ι}
    {Context SecretKey : Type} (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (materialGenerator : Phase1MaterialGenerator baseSpec Context)
    (adversary : Phase1Adversary baseSpec Context) :
    OracleComp baseSpec Bool := by
  letI : DecidableEq Pqxdh.Bytes := Classical.decEq Pqxdh.Bytes
  exact do
    let (pk, sk) ← sigAlg.keygen
    let (result, log) ←
      (simulateQ (phase1SigningImpl sigAlg pk sk)
        (phase1ClientMain materialGenerator adversary pk)).run
    let selected := selectPhase1Forgery result.material result.transcript
      result.candidate
    let verified ← sigAlg.verify pk selected.1 selected.2
    return !log.wasQueried selected.1 && verified

theorem unforgeableExp_phase1ToEUFCMA {ι : Type}
    {baseSpec : OracleSpec ι} {Context SecretKey : Type}
    (runtime : ProbCompRuntime (OracleComp baseSpec))
    (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (materialGenerator : Phase1MaterialGenerator baseSpec Context)
    (adversary : Phase1Adversary baseSpec Context) :
    SignatureAlg.unforgeableExp runtime
        (phase1ToEUFCMA sigAlg materialGenerator adversary) =
      runtime.evalDist
        (phase1EufBody sigAlg materialGenerator adversary) := by
  unfold SignatureAlg.unforgeableExp phase1EufBody phase1ToEUFCMA
  simp only [simulateQ_bind, WriterT.run_bind]
  simp [phase1SigningImpl, map_eq_bind_pure_comp]
  congr 1

theorem phase1EufBody_eq_shared {ι : Type} {baseSpec : OracleSpec ι}
    {Context SecretKey : Type} (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (materialGenerator : Phase1MaterialGenerator baseSpec Context)
    (adversary : Phase1Adversary baseSpec Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (deterministic : HasDeterministicVerification sigAlg verifyFn) :
    phase1EufBody sigAlg materialGenerator adversary =
      phase1EufBit verifyFn <$>
        phase1SharedJoint sigAlg materialGenerator adversary := by
  unfold phase1EufBody phase1SharedJoint
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  rintro ⟨pk, sk⟩
  simp_rw [deterministic pk]
  simp only [pure_bind]
  calc
    _ = phase1ClientEufBit verifyFn pk <$>
        phase1ClientReference sigAlg materialGenerator adversary pk sk := by
      have normalized := phase1ClientEufBit_logged_eq_reference sigAlg
        materialGenerator adversary verifyFn pk sk
      rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp] at normalized
      convert normalized using 1
      congr 1
      funext result
      simp only [Function.comp_apply]
      apply congrArg pure
      congr 2
      simp only [QueryLog.wasQueried_eq_decide_mem_map_fst]
      exact decide_eq_decide.mpr Iff.rfl
      exact map_eq_bind_pure_comp (OracleComp baseSpec)
        (phase1ClientEufBit verifyFn pk)
        (phase1ClientReference sigAlg materialGenerator adversary pk sk)
    _ = _ := by
      simp [phase1ClientReference, phase1EufBit, phase1ClientEufBit]

theorem unforgeableExp_phase1ToEUFCMA_eq_shared {ι : Type}
    {baseSpec : OracleSpec ι} {Context SecretKey : Type}
    (runtime : ProbCompRuntime (OracleComp baseSpec))
    (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (materialGenerator : Phase1MaterialGenerator baseSpec Context)
    (adversary : Phase1Adversary baseSpec Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (deterministic : HasDeterministicVerification sigAlg verifyFn)
    (h_pull : ∀ {α β : Type} (f : α → β) (mx : OracleComp baseSpec α),
      runtime.evalDist (mx >>= fun x => pure (f x)) =
        f <$> runtime.evalDist mx) :
    SignatureAlg.unforgeableExp runtime
        (phase1ToEUFCMA sigAlg materialGenerator adversary) =
      phase1EufBit verifyFn <$>
        runtime.evalDist
          (phase1SharedJoint sigAlg materialGenerator adversary) := by
  rw [unforgeableExp_phase1ToEUFCMA runtime sigAlg materialGenerator adversary,
    phase1EufBody_eq_shared sigAlg materialGenerator adversary verifyFn
      deterministic]
  rw [map_eq_bind_pure_comp]
  have bindEquality :
      (phase1SharedJoint sigAlg materialGenerator adversary >>=
          pure ∘ phase1EufBit verifyFn) =
        (phase1SharedJoint sigAlg materialGenerator adversary >>= fun joint =>
          pure (phase1EufBit verifyFn joint)) := by
    apply bind_congr
    intro joint
    rfl
  rw [bindEquality]
  exact h_pull (phase1EufBit verifyFn)
    (phase1SharedJoint sigAlg materialGenerator adversary)

/-- A same-target accepted field substitution is one weak-EUF-CMA forgery, with no guessed-field loss. -/
theorem phase1FieldSubstitutionAdvantage_le_eufCma {ι : Type}
    {baseSpec : OracleSpec ι} {Context SecretKey : Type}
    (runtime : ProbCompRuntime (OracleComp baseSpec))
    (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (materialGenerator : Phase1MaterialGenerator baseSpec Context)
    (adversary : Phase1Adversary baseSpec Context)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (deterministic : HasDeterministicVerification sigAlg verifyFn)
    (h_pull : ∀ {α β : Type} (f : α → β) (mx : OracleComp baseSpec α),
      runtime.evalDist (mx >>= fun x => pure (f x)) =
        f <$> runtime.evalDist mx) :
    Phase1FieldSubstitutionAdvantage runtime sigAlg materialGenerator adversary
        verifyFn ≤
      (phase1ToEUFCMA sigAlg materialGenerator adversary).advantage runtime := by
  unfold Phase1FieldSubstitutionAdvantage SignatureAlg.unforgeableAdv.advantage
  rw [phase1FieldSubstitutionExp_eq_shared runtime sigAlg materialGenerator
      adversary verifyFn h_pull,
    unforgeableExp_phase1ToEUFCMA_eq_shared runtime sigAlg materialGenerator
      adversary verifyFn deterministic h_pull,
    ← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput,
    probEvent_map, probEvent_map]
  exact probEvent_mono'' fun joint =>
    phase1SourceBadBit_implies_eufBit verifyFn joint

/-- Base-oracle queries made syntactically by the material generator or source adversary. -/
def IsPhase1BaseQuery {ι : Type} :
    (ι ⊕ Pqxdh.Bytes) → Prop
  | .inl _ => True
  | .inr _ => False

/-- Logical calls to the EUF-CMA signing interface. -/
def IsPhase1SigningQuery {ι : Type} :
    (ι ⊕ Pqxdh.Bytes) → Prop
  | .inl _ => False
  | .inr _ => True

instance instDecidablePredIsPhase1BaseQuery {ι : Type} :
    DecidablePred (@IsPhase1BaseQuery ι)
  | .inl _ => isTrue trivial
  | .inr _ => isFalse id

instance instDecidablePredIsPhase1SigningQuery {ι : Type} :
    DecidablePred (@IsPhase1SigningQuery ι)
  | .inl _ => isFalse id
  | .inr _ => isTrue trivial

/-- Material-generation base-query cap; opaque signature-algorithm work is outside it. -/
def Phase1MaterialGenerator.MakesAtMostQueries {ι : Type}
    {baseSpec : OracleSpec ι} {Context : Type}
    (materialGenerator : Phase1MaterialGenerator baseSpec Context) (qMaterial : ℕ) :
    Prop :=
  ∀ pk, (materialGenerator.main pk).IsTotalQueryBound qMaterial

/-- Source-adversary base-query cap; opaque signature-algorithm work is outside it. -/
def Phase1Adversary.MakesAtMostQueries {ι : Type}
    {baseSpec : OracleSpec ι} {Context : Type}
    (adversary : Phase1Adversary baseSpec Context) (qAdversary : ℕ) : Prop :=
  ∀ transcript, (adversary.main transcript).IsTotalQueryBound qAdversary

theorem liftPhase1Base_baseQueryBound {ι : Type} {baseSpec : OracleSpec ι}
    {α : Type} (computation : OracleComp baseSpec α) {q : ℕ}
    (bound : computation.IsTotalQueryBound q) :
    (OracleComp.liftComp computation
      (baseSpec + (Pqxdh.Bytes →ₒ Ed25519Signature))).IsQueryBoundP
        IsPhase1BaseQuery q := by
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := baseSpec)
    (superSpec := baseSpec + (Pqxdh.Bytes →ₒ Ed25519Signature))
    (p := fun _ => True) (q := IsPhase1BaseQuery)
    (hpq := by
      intro query
      simp [IsPhase1BaseQuery, SubSpec.onQuery])
    bound.isQueryBoundP

theorem liftPhase1Base_noSigningQuery {ι : Type} {baseSpec : OracleSpec ι}
    {α : Type} (computation : OracleComp baseSpec α) :
    (OracleComp.liftComp computation
      (baseSpec + (Pqxdh.Bytes →ₒ Ed25519Signature))).IsQueryBoundP
        IsPhase1SigningQuery 0 := by
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := baseSpec)
    (superSpec := baseSpec + (Pqxdh.Bytes →ₒ Ed25519Signature))
    (p := fun _ => False) (q := IsPhase1SigningQuery)
    (hpq := by
      intro query
      simp [IsPhase1SigningQuery, SubSpec.onQuery])
    (OracleComp.isQueryBoundP_false computation 0)

theorem phase1SignQuery_signingQueryBound {ι : Type}
    {baseSpec : OracleSpec ι} (message : Pqxdh.Bytes) :
    ((liftM ((Pqxdh.Bytes →ₒ Ed25519Signature).query message) :
      OracleComp (baseSpec + (Pqxdh.Bytes →ₒ Ed25519Signature))
        Ed25519Signature)).IsQueryBoundP IsPhase1SigningQuery 1 := by
  change ((liftM
    (liftM ((Pqxdh.Bytes →ₒ Ed25519Signature).query message) :
      OracleComp (Pqxdh.Bytes →ₒ Ed25519Signature) Ed25519Signature) :
        OracleComp (baseSpec + (Pqxdh.Bytes →ₒ Ed25519Signature))
          Ed25519Signature)).IsQueryBoundP IsPhase1SigningQuery 1
  rw [← OracleComp.liftComp_eq_liftM]
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := Pqxdh.Bytes →ₒ Ed25519Signature)
    (superSpec := baseSpec + (Pqxdh.Bytes →ₒ Ed25519Signature))
    (p := fun _ => True) (q := IsPhase1SigningQuery)
    (hpq := by
      intro query
      simp [IsPhase1SigningQuery, SubSpec.onQuery])
    ((OracleComp.isQueryBoundP_query_iff (fun _ => True) message 1).mpr
      (fun _ => Nat.zero_lt_one))

theorem phase1SignQuery_noBaseQuery {ι : Type}
    {baseSpec : OracleSpec ι} (message : Pqxdh.Bytes) :
    ((liftM ((Pqxdh.Bytes →ₒ Ed25519Signature).query message) :
      OracleComp (baseSpec + (Pqxdh.Bytes →ₒ Ed25519Signature))
        Ed25519Signature)).IsQueryBoundP IsPhase1BaseQuery 0 := by
  change ((liftM
    (liftM ((Pqxdh.Bytes →ₒ Ed25519Signature).query message) :
      OracleComp (Pqxdh.Bytes →ₒ Ed25519Signature) Ed25519Signature) :
        OracleComp (baseSpec + (Pqxdh.Bytes →ₒ Ed25519Signature))
          Ed25519Signature)).IsQueryBoundP IsPhase1BaseQuery 0
  rw [← OracleComp.liftComp_eq_liftM]
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := Pqxdh.Bytes →ₒ Ed25519Signature)
    (superSpec := baseSpec + (Pqxdh.Bytes →ₒ Ed25519Signature))
    (p := fun _ => False) (q := IsPhase1BaseQuery)
    (hpq := by
      intro query
      simp [IsPhase1BaseQuery, SubSpec.onQuery])
    (OracleComp.isQueryBoundP_false
      (liftM ((Pqxdh.Bytes →ₒ Ed25519Signature).query message) :
        OracleComp (Pqxdh.Bytes →ₒ Ed25519Signature) Ed25519Signature) 0)

@[simp] theorem honestPhase1Messages_length {Context : Type}
    (material : Phase1Material Context) :
    (honestPhase1Messages material).length = 3 := by
  rfl

/-- The source wrapper makes at most three logical signing calls; every returned path has the exact prekey/one-time/PQ log proved by `phase1ClientMain_logged_messages`. -/
theorem phase1ClientMain_signingQueryBound {ι : Type}
    {baseSpec : OracleSpec ι} {Context : Type}
    (materialGenerator : Phase1MaterialGenerator baseSpec Context)
    (adversary : Phase1Adversary baseSpec Context)
    (pk : Ed25519PublicKey) :
    (phase1ClientMain materialGenerator adversary pk).IsQueryBoundP
      IsPhase1SigningQuery 3 := by
  unfold phase1ClientMain
  refine OracleComp.isQueryBoundP_bind (n := 0) (m := 3)
    (liftPhase1Base_noSigningQuery (materialGenerator.main pk)) ?_
  intro material _
  refine OracleComp.isQueryBoundP_bind (n := 1) (m := 2)
    (phase1SignQuery_signingQueryBound (prekeyMessage material.prekey)) ?_
  intro preSignature _
  refine OracleComp.isQueryBoundP_bind (n := 1) (m := 1)
    (phase1SignQuery_signingQueryBound (oneTimeMessage material.oneTime)) ?_
  intro oneTimeSignature _
  refine OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
    (phase1SignQuery_signingQueryBound (pqMessage material.pqKey)) ?_
  intro pqSignature _
  refine OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (liftPhase1Base_noSigningQuery
      (adversary.main (honestPhase1Transcript pk material preSignature
        oneTimeSignature pqSignature))) ?_
  intro candidate _
  exact OracleComp.isQueryBoundP_pure IsPhase1SigningQuery
    (⟨material,
      honestPhase1Transcript pk material preSignature oneTimeSignature pqSignature,
      candidate⟩ : Phase1ClientResult Context) 0

/-- The wrapper preserves the material/source base caps additively; the three logical sign calls cost zero base queries. -/
theorem phase1ClientMain_baseQueryBound {ι : Type}
    {baseSpec : OracleSpec ι} {Context : Type}
    (materialGenerator : Phase1MaterialGenerator baseSpec Context)
    (adversary : Phase1Adversary baseSpec Context)
    {qMaterial qAdversary : ℕ}
    (materialBound : materialGenerator.MakesAtMostQueries qMaterial)
    (adversaryBound : adversary.MakesAtMostQueries qAdversary)
    (pk : Ed25519PublicKey) :
    (phase1ClientMain materialGenerator adversary pk).IsQueryBoundP
      IsPhase1BaseQuery (qMaterial + qAdversary) := by
  unfold phase1ClientMain
  refine OracleComp.isQueryBoundP_bind (n := qMaterial) (m := qAdversary)
    (liftPhase1Base_baseQueryBound (materialGenerator.main pk)
      (materialBound pk)) ?_
  intro material _
  refine (OracleComp.isQueryBoundP_bind (n := 0) (m := qAdversary)
    (phase1SignQuery_noBaseQuery (prekeyMessage material.prekey)) ?_).mono
      (by omega)
  intro preSignature _
  refine (OracleComp.isQueryBoundP_bind (n := 0) (m := qAdversary)
    (phase1SignQuery_noBaseQuery (oneTimeMessage material.oneTime)) ?_).mono
      (by omega)
  intro oneTimeSignature _
  refine (OracleComp.isQueryBoundP_bind (n := 0) (m := qAdversary)
    (phase1SignQuery_noBaseQuery (pqMessage material.pqKey)) ?_).mono
      (by omega)
  intro pqSignature _
  refine (OracleComp.isQueryBoundP_bind (n := qAdversary) (m := 0)
    (liftPhase1Base_baseQueryBound
      (adversary.main (honestPhase1Transcript pk material preSignature
        oneTimeSignature pqSignature)) (adversaryBound _)) ?_).mono (by omega)
  intro candidate _
  exact OracleComp.isQueryBoundP_pure IsPhase1BaseQuery
    (⟨material,
      honestPhase1Transcript pk material preSignature oneTimeSignature pqSignature,
      candidate⟩ : Phase1ClientResult Context) 0

theorem phase1ToEUFCMA_signingQueryBound {ι : Type}
    {baseSpec : OracleSpec ι} {Context SecretKey : Type}
    (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (materialGenerator : Phase1MaterialGenerator baseSpec Context)
    (adversary : Phase1Adversary baseSpec Context)
    (pk : Ed25519PublicKey) :
    ((phase1ToEUFCMA sigAlg materialGenerator adversary).main pk).IsQueryBoundP
      IsPhase1SigningQuery 3 := by
  unfold phase1ToEUFCMA
  refine (OracleComp.isQueryBoundP_bind (n := 3) (m := 0)
    (phase1ClientMain_signingQueryBound materialGenerator adversary pk) ?_).mono
      (by omega)
  intro result _
  exact OracleComp.isQueryBoundP_pure IsPhase1SigningQuery
    (selectPhase1Forgery result.material result.transcript result.candidate) 0

theorem phase1ToEUFCMA_baseQueryBound {ι : Type}
    {baseSpec : OracleSpec ι} {Context SecretKey : Type}
    (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (materialGenerator : Phase1MaterialGenerator baseSpec Context)
    (adversary : Phase1Adversary baseSpec Context)
    {qMaterial qAdversary : ℕ}
    (materialBound : materialGenerator.MakesAtMostQueries qMaterial)
    (adversaryBound : adversary.MakesAtMostQueries qAdversary)
    (pk : Ed25519PublicKey) :
    ((phase1ToEUFCMA sigAlg materialGenerator adversary).main pk).IsQueryBoundP
      IsPhase1BaseQuery (qMaterial + qAdversary) := by
  unfold phase1ToEUFCMA
  refine (OracleComp.isQueryBoundP_bind (n := qMaterial + qAdversary) (m := 0)
    (phase1ClientMain_baseQueryBound materialGenerator adversary
      materialBound adversaryBound pk) ?_).mono (by omega)
  intro result _
  exact OracleComp.isQueryBoundP_pure IsPhase1BaseQuery
    (selectPhase1Forgery result.material result.transcript result.candidate) 0

/-- Named source-adapter law: production attached verification agrees with exact 64-byte splitting followed by the detached relation. -/
def HasAttachedVerificationAdapter
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool) : Prop :=
  ∀ pk buffer, attachedVerify pk buffer = openAttached verifyFn pk buffer

/-- The attached-signature correctness premise is definitionally VCVio's generic signature perfect completeness. -/
def Ed25519AttachedSignatureCorrectness {ι : Type}
    {baseSpec : OracleSpec ι} {SecretKey : Type}
    (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (runtime : ProbCompRuntime (OracleComp baseSpec)) : Prop :=
  sigAlg.PerfectlyComplete runtime

theorem ed25519AttachedSignatureCorrectness_iff_perfectlyComplete {ι : Type}
    {baseSpec : OracleSpec ι} {SecretKey : Type}
    (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (runtime : ProbCompRuntime (OracleComp baseSpec)) :
    Ed25519AttachedSignatureCorrectness sigAlg runtime ↔
      sigAlg.PerfectlyComplete runtime := by
  rfl

/-- Every supported honest key/signature pair verifies and the exact attached adapter opens it to the original message. -/
theorem ed25519AttachedSignatureCorrectness_opens_supported {ι : Type}
    {baseSpec : OracleSpec ι} {SecretKey : Type}
    (sigAlg : Ed25519Scheme baseSpec SecretKey)
    (runtime : ProbCompRuntime (OracleComp baseSpec))
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (deterministic : HasDeterministicVerification sigAlg verifyFn)
    (heval_pure : ∀ {α : Type} (value : α),
      runtime.evalDist (pure value : OracleComp baseSpec α) = pure value)
    (heval_bind : ∀ {α β : Type} (computation : OracleComp baseSpec α)
      (continuation : α → OracleComp baseSpec β),
      runtime.evalDist (computation >>= continuation) =
        runtime.evalDist computation >>= fun value =>
          runtime.evalDist (continuation value))
    (correct : Ed25519AttachedSignatureCorrectness sigAlg runtime)
    {pk : Ed25519PublicKey} {sk : SecretKey}
    (keygenSupport : (pk, sk) ∈ support (runtime.evalDist sigAlg.keygen))
    {message : Pqxdh.Bytes} {signature : Ed25519Signature}
    (signSupport : signature ∈
      support (runtime.evalDist (sigAlg.sign pk sk message))) :
    verifyFn pk message signature = true ∧
      splitAttachedSignature (attachSignature signature message) =
        some (signature, message) ∧
      openAttached verifyFn pk (attachSignature signature message) = some message := by
  have verificationSupport : verifyFn pk message signature ∈
      support (runtime.evalDist (sigAlg.verify pk message signature)) := by
    rw [deterministic, heval_pure]
    simp
  have outputSupport : verifyFn pk message signature ∈ support
      (runtime.evalDist do
        let (generatedPk, generatedSk) ← sigAlg.keygen
        let generatedSignature ← sigAlg.sign generatedPk generatedSk message
        sigAlg.verify generatedPk message generatedSignature) := by
    simp only [heval_bind, support_bind, Set.mem_iUnion, exists_prop,
      Prod.exists]
    exact ⟨pk, sk, keygenSupport, signature, signSupport,
      verificationSupport⟩
  have verified : verifyFn pk message signature = true := by
    simpa [Ed25519AttachedSignatureCorrectness,
      ((probOutput_eq_one_iff (mx := runtime.evalDist do
        let (generatedPk, generatedSk) ← sigAlg.keygen
        let generatedSignature ← sigAlg.sign generatedPk generatedSk message
        sigAlg.verify generatedPk message generatedSignature)
        (x := true)).mp (correct message)).2] using outputSupport
  exact ⟨verified, splitAttachedSignature_attach signature message, by
    simp [openAttached, verified]⟩

theorem attachedVerificationAdapter_opens_honest
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (verifyFn : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (adapter : HasAttachedVerificationAdapter attachedVerify verifyFn)
    {pk : Ed25519PublicKey} {message : Pqxdh.Bytes}
    {signature : Ed25519Signature}
    (verified : verifyFn pk message signature = true) :
    attachedVerify pk (attachSignature signature message) = some message := by
  rw [adapter]
  simp [openAttached, verified]

/--
info: 'BeaconcryptCore.Computational.PqxdhEd25519EufCma.phase1FieldSubstitutionAdvantage_le_eufCma' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms phase1FieldSubstitutionAdvantage_le_eufCma

/--
info: 'BeaconcryptCore.Computational.PqxdhEd25519EufCma.ed25519AttachedSignatureCorrectness_opens_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ed25519AttachedSignatureCorrectness_opens_supported

end BeaconcryptCore.Computational.PqxdhEd25519EufCma
