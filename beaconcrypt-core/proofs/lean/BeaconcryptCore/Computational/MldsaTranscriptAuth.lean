-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Model.Pqxdh.TranscriptAuth
import BeaconcryptCore.Model.Pqxdh.SessionTranscript
import Mathlib.MeasureTheory.Measure.Basic

/-!
Transcript authentication conditional on explicit ML-DSA-65 unforgeability and
BLAKE2b-512 collision bounds. The primitives remain opaque. In particular, this
module imports neither a VCVio signature theorem nor an ML-DSA implementation.

The trace distribution is supplied by the caller. A post-quantum interpretation
requires the external assumptions to cover that attacker's classical signing
interface and trace distribution; no quantum execution semantics is claimed.
The current protected ML-DSA key is the pinned Server key. The generic signature experiment is used for Server response origin; it does not authenticate an enrolled Beacon principal. Attacker registrations remain admitted. Transcript AD instead binds the full selected request/response preimage up to the explicit hash-collision event below.
-/

set_option autoImplicit false

namespace BeaconcryptCore.Computational.MldsaTranscriptAuth

open MeasureTheory

abbrev Bytes := Pqxdh.Bytes
abbrev Role := Pqxdh.TranscriptAuth.Role
abbrev Hash512 := Pqxdh.TranscriptAuth.Hash512

/-- An unsigned transcript preimage and the role whose signing input it uses. -/
structure Payload where
  role : Role
  transcript : Bytes
  deriving DecidableEq

/-- The exact message argument to the context-aware ML-DSA operation. -/
def Payload.message (hash : Hash512) (payload : Payload) : Bytes :=
  Pqxdh.TranscriptAuth.signatureInput payload.role (hash payload.transcript)

/-- Log every signing call, including failure and calls followed by failed publication. -/
structure SigningCall where
  payload : Payload
  reply : Option Bytes

/-- Public observations at one verification attempt, with the target key's prior signing log. -/
structure Trial where
  publicKey : Bytes
  protectedKey : Bool
  history : List SigningCall
  candidate : Payload
  signature : Bytes

/-- Public-key, FIPS context, message and signature arguments, in that order. -/
abbrev Verify := Bytes → Bytes → Bytes → Bytes → Bool

/-- The source parser's fixed widths and the actual context-aware verification gate. -/
def Accepted (hash : Hash512) (verify : Verify) (trial : Trial) : Prop :=
  trial.protectedKey = true ∧ trial.publicKey.length = 1952 ∧
    trial.signature.length = 3309 ∧
    verify trial.publicKey Pqxdh.TranscriptAuth.signingContext
      (trial.candidate.message hash) trial.signature = true

/-- Unsigned transcript origin; signature-byte uniqueness is deliberately absent. -/
def Issued (trial : Trial) : Prop :=
  ∃ call ∈ trial.history, call.payload = trial.candidate

def OriginFailure (hash : Hash512) (verify : Verify) (trial : Trial) : Prop :=
  Accepted hash verify trial ∧ ¬ Issued trial

/-- Ordinary weak-EUF freshness concerns messages, including every attempted signing query. -/
def WeakForgery (hash : Hash512) (verify : Verify) (trial : Trial) : Prop :=
  Accepted hash verify trial ∧
    ∀ call ∈ trial.history, call.payload.message hash ≠ trial.candidate.message hash

/-- An actual pair of unequal BLAKE2b inputs with equal outputs, from the public trace. -/
def TranscriptCollision (hash : Hash512) (trial : Trial) : Prop :=
  ∃ call ∈ trial.history,
    call.payload.transcript ≠ trial.candidate.transcript ∧
      hash call.payload.transcript = hash trial.candidate.transcript

/-- The request payload uses the self-presented beacon ML key inside its signed preimage. -/
def initPayload (fields : Pqxdh.TranscriptAuth.InitFields) (serverId : UInt64)
    (serverEd serverMldsa : Bytes) : Payload :=
  ⟨.beacon, Pqxdh.TranscriptAuth.initTranscript fields serverId serverEd serverMldsa⟩

/-- The response signs raw application ciphertext and the request digest, not CBOR bytes. -/
def responsePayload (initDigest : Bytes)
    (fields : Pqxdh.TranscriptAuth.ResponseFields) : Payload :=
  ⟨.server, Pqxdh.TranscriptAuth.responseTranscript initDigest fields⟩

/-- Failure of unsigned transcript origin exposes a fresh message or an actual hash collision. -/
theorem origin_failure_split (hash : Hash512) (verify : Verify) (trial : Trial)
    (failure : OriginFailure hash verify trial) :
    WeakForgery hash verify trial ∨ TranscriptCollision hash trial := by
  classical
  by_cases fresh : ∀ call ∈ trial.history,
    call.payload.message hash ≠ trial.candidate.message hash
  · exact Or.inl ⟨failure.1, fresh⟩
  · push Not at fresh
    obtain ⟨call, inHistory, sameMessage⟩ := fresh
    have components := (Pqxdh.TranscriptAuth.signatureInput_eq_iff
      call.payload.role trial.candidate.role
      (hash call.payload.transcript) (hash trial.candidate.transcript)).mp sameMessage
    exact Or.inr ⟨call, inHistory,
      (fun sameTranscript => failure.2 ⟨call, inHistory,
        congrArg₂ Payload.mk components.1 sameTranscript⟩), components.2⟩

/-- A distribution-free event bound; primitive security has not yet been assumed. -/
theorem origin_failure_bound [MeasurableSpace Trial] (hash : Hash512) (verify : Verify)
    (traces : Measure Trial) :
    traces {trial | OriginFailure hash verify trial} ≤
      traces {trial | WeakForgery hash verify trial} +
        traces {trial | TranscriptCollision hash trial} :=
  (measure_mono (show {trial | OriginFailure hash verify trial} ⊆
      {trial | WeakForgery hash verify trial} ∪ {trial | TranscriptCollision hash trial}
    from fun trial failure => origin_failure_split hash verify trial failure)).trans
      (measure_union_le _ _)

/-- External security bounds for the supplied trace distribution, not primitive theorems.

The caller must justify the honest-key/signing-log interpretation of `Trial` and
instantiate these bounds for its attacker model. Neither quantum feasibility nor
the connection to a key-generation/signing implementation is proved here.
-/
structure AssumedSecurity [MeasurableSpace Trial] (hash : Hash512) (verify : Verify)
    (traces : Measure Trial) (signatureError hashError : ENNReal) : Prop where
  mldsa65_unforgeability : traces {trial | WeakForgery hash verify trial} ≤ signatureError
  blake2b512_collision_resistance : traces {trial | TranscriptCollision hash trial} ≤ hashError

/-- The protocol byte-origin bound is conditional on the explicitly supplied primitive bounds. -/
theorem origin_failure_le_assumed_errors [MeasurableSpace Trial]
    (hash : Hash512) (verify : Verify) (traces : Measure Trial)
    (signatureError hashError : ENNReal)
    (security : AssumedSecurity hash verify traces signatureError hashError) :
    traces {trial | OriginFailure hash verify trial} ≤ signatureError + hashError :=
  (origin_failure_bound hash verify traces).trans
    (add_le_add security.mldsa65_unforgeability security.blake2b512_collision_resistance)

/-- A concrete collision pair, rather than the existence of collisions in the hash's whole domain. -/
def CollisionPair (hash : Hash512) (left right : Bytes) : Prop :=
  left ≠ right ∧ hash left = hash right

/-- Equal complete AD identifies the exact transcript preimage unless that pair is a hash collision. No hash injectivity is assumed. -/
theorem transcript_ad_preimage_binding (hash : Hash512) (left right : Bytes)
    (same : Pqxdh.SessionTranscript.associatedData (hash left) =
      Pqxdh.SessionTranscript.associatedData (hash right)) :
    left = right ∨ CollisionPair hash left right := by
  by_cases equal : left = right
  · exact Or.inl equal
  · exact Or.inr ⟨equal, Pqxdh.SessionTranscript.associatedData_inj _ _ same⟩

/-- All exact signed Init fields and all pre-seal response fields agree, or their displayed encodings collide under the supplied hash. -/
theorem transcript_ad_fields_binding (hash : Hash512)
    (leftInit rightInit : Pqxdh.SessionTranscript.InitFields)
    (leftResponse rightResponse : Pqxdh.SessionTranscript.ResponseFields)
    (leftInitValid : leftInit.WellFormed) (rightInitValid : rightInit.WellFormed)
    (leftResponseValid : leftResponse.WellFormed) (rightResponseValid : rightResponse.WellFormed)
    (same : Pqxdh.SessionTranscript.associatedData (hash (Pqxdh.SessionTranscript.encode leftInit leftResponse)) =
      Pqxdh.SessionTranscript.associatedData (hash (Pqxdh.SessionTranscript.encode rightInit rightResponse))) :
    (leftInit = rightInit ∧ leftResponse = rightResponse) ∨
      CollisionPair hash (Pqxdh.SessionTranscript.encode leftInit leftResponse)
        (Pqxdh.SessionTranscript.encode rightInit rightResponse) := by
  rcases transcript_ad_preimage_binding hash _ _ same with identical | collision
  · exact Or.inl (Pqxdh.SessionTranscript.encode_inj leftInitValid rightInitValid
      leftResponseValid rightResponseValid identical)
  · exact Or.inr collision

/-- info: 'BeaconcryptCore.Computational.MldsaTranscriptAuth.origin_failure_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms origin_failure_split

/-- info: 'BeaconcryptCore.Computational.MldsaTranscriptAuth.origin_failure_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms origin_failure_bound

/-- info: 'BeaconcryptCore.Computational.MldsaTranscriptAuth.origin_failure_le_assumed_errors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms origin_failure_le_assumed_errors


/-- info: 'BeaconcryptCore.Computational.MldsaTranscriptAuth.transcript_ad_preimage_binding' depends on axioms: [propext] -/
#guard_msgs in
#print axioms transcript_ad_preimage_binding

/-- info: 'BeaconcryptCore.Computational.MldsaTranscriptAuth.transcript_ad_fields_binding' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms transcript_ad_fields_binding

end BeaconcryptCore.Computational.MldsaTranscriptAuth
