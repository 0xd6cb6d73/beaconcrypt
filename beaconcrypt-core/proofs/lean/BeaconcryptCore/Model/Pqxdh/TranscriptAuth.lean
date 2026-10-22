-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Model.Pqxdh.Primitives

/-!
Exact deterministic byte constructions from `beaconcrypt/src/auth.rs` and the
ML-DSA fingerprint slots in `beaconcrypt/src/pqxdh.rs`. Hashing remains an opaque
function supplied by the caller; no ML-DSA algorithm or security property is
asserted. These are unsigned decoded registration fields, not CBOR encodings.
Native primitive and allocation failures remain outside these pure byte functions.
-/
set_option autoImplicit false
namespace Pqxdh.TranscriptAuth

abbrev Hash512 := Bytes → Bytes

/-- Output-width contract only; this is neither collision resistance nor injectivity. -/
def HashWidth (hash : Hash512) : Prop := ∀ input, (hash input).length = 64

/-- ASCII `beaconcrypt registration auth v1`, without a terminal NUL. -/
def signingContext : Bytes :=
  [98, 101, 97, 99, 111, 110, 99, 114, 121, 112, 116, 32, 114, 101, 103, 105,
   115, 116, 114, 97, 116, 105, 111, 110, 32, 97, 117, 116, 104, 32, 118, 49]

/-- ASCII `beaconcrypt ML-DSA-65 init transcript v1` followed by NUL. -/
def initDomain : Bytes :=
  [98, 101, 97, 99, 111, 110, 99, 114, 121, 112, 116, 32, 77, 76, 45, 68, 83,
   65, 45, 54, 53, 32, 105, 110, 105, 116, 32, 116, 114, 97, 110, 115, 99,
   114, 105, 112, 116, 32, 118, 49, 0]

/-- ASCII `beaconcrypt ML-DSA-65 response transcript v1` followed by NUL. -/
def responseDomain : Bytes :=
  [98, 101, 97, 99, 111, 110, 99, 114, 121, 112, 116, 32, 77, 76, 45, 68, 83,
   65, 45, 54, 53, 32, 114, 101, 115, 112, 111, 110, 115, 101, 32, 116, 114,
   97, 110, 115, 99, 114, 105, 112, 116, 32, 118, 49, 0]

inductive Role where
  | beacon
  | server
  deriving DecidableEq

def roleLabel : Role → Bytes
  | .beacon =>
    [98, 101, 97, 99, 111, 110, 99, 114, 121, 112, 116, 32, 118, 49, 32, 98,
     101, 97, 99, 111, 110, 32, 114, 101, 103, 105, 115, 116, 114, 97, 116, 105, 111, 110]
  | .server =>
    [98, 101, 97, 99, 111, 110, 99, 114, 121, 112, 116, 32, 118, 49, 32, 115,
     101, 114, 118, 101, 114, 32, 114, 101, 103, 105, 115, 116, 114, 97, 116, 105, 111, 110]

/-- The TLS CertificateVerify-style input passed to ML-DSA, with a separate FIPS context. -/
def signatureInput (role : Role) (digest : Bytes) : Bytes :=
  List.replicate 64 0x20 ++ roleLabel role ++ [0] ++ digest

/-- Exact unsigned request fields. The three Ed25519 fields retain attached signatures. -/
@[ext]
structure InitFields where
  identityKey : Bytes
  preKey : Bytes
  oneTimeKey : Bytes
  pqKey : Bytes
  mldsaPublicKey : Bytes
  deriving DecidableEq

/-- Exact unsigned response fields; application bytes are raw `C || T || U`. -/
@[ext]
structure ResponseFields where
  identityKey : Bytes
  ephemeralKey : Bytes
  kemCipherText : Bytes
  appCipherText : Bytes
  keyId : UInt64
  deriving DecidableEq

/-- Fixed widths checked by the generated CBOR request decoder. -/
structure InitFields.WellFormed (init : InitFields) : Prop where
  identityWidth : init.identityKey.length = 33
  preWidth : init.preKey.length = 98
  oneTimeWidth : init.oneTimeKey.length = 98
  pqWidth : init.pqKey.length = 1249
  mldsaWidth : init.mldsaPublicKey.length = 1952

/-- Fixed response widths and the length conversion checked before transcript hashing. -/
structure ResponseFields.WellFormed (response : ResponseFields) : Prop where
  identityWidth : response.identityKey.length = 32
  ephemeralWidth : response.ephemeralKey.length = 32
  kemWidth : response.kemCipherText.length = 1088
  applicationFits : response.appCipherText.length < 2 ^ 64

/-- The detached signature is present on the wire but excluded from its own transcript. -/
structure Signed (Fields : Type) where
  fields : Fields
  signature : Bytes

/-- Rust checks conversion of each length to u64 before emitting this framing. -/
def hashField (field : Bytes) : Bytes := LE64 field.length ++ field

/-- Request bytes bind the numeric server pin, its Ed25519 pin, and both ML-DSA keys. -/
def initTranscript (init : InitFields) (serverId : UInt64)
    (serverEd serverMldsa : Bytes) : Bytes :=
  initDomain ++ LE64 serverId.toNat ++ serverEd ++ init.mldsaPublicKey ++ serverMldsa ++
    hashField init.identityKey ++ hashField init.preKey ++
    hashField init.oneTimeKey ++ hashField init.pqKey

/-- Response bytes bind the request digest, every unsigned field, and the assigned identifier. -/
def responseTranscript (initDigest : Bytes) (response : ResponseFields) : Bytes :=
  responseDomain ++ initDigest ++ hashField response.identityKey ++
    hashField response.ephemeralKey ++ hashField response.kemCipherText ++
    hashField response.appCipherText ++ LE64 response.keyId.toNat

def initHash (hash : Hash512) (init : InitFields) (serverId : UInt64)
    (serverEd serverMldsa : Bytes) : Bytes :=
  hash (initTranscript init serverId serverEd serverMldsa)

def responseHash (hash : Hash512) (initDigest : Bytes) (response : ResponseFields) : Bytes :=
  hash (responseTranscript initDigest response)

def signedInitHash (hash : Hash512) (init : Signed InitFields) (serverId : UInt64)
    (serverEd serverMldsa : Bytes) : Bytes :=
  initHash hash init.fields serverId serverEd serverMldsa

def signedResponseHash (hash : Hash512) (initDigest : Bytes)
    (response : Signed ResponseFields) : Bytes :=
  responseHash hash initDigest response.fields

/-- Width-checked raw public-key hashing, with the same opaque BLAKE2b function as the transcripts. -/
def publicKeyHash (hash : Hash512) (key : Bytes) : Option Bytes :=
  if key.length = 1952 then some (hash key) else none

/-- Extend the original ordered 153-byte identity/domain prefix with both 64-byte fingerprints. -/
def associatedData (base153 serverDigest beaconDigest : Bytes) : Bytes :=
  base153 ++ serverDigest ++ beaconDigest

/-- Model the native overwrite of slots 153..217 and 217..281 in its 281-byte array. -/
def fillAssociatedData (base281 serverDigest beaconDigest : Bytes) : Bytes :=
  associatedData (base281.take 153) serverDigest beaconDigest

/-- The deterministic current CTX preimage; this is not an extraction/refinement claim. -/
def commitmentInput (key nonce ad tag : Bytes) (sequence sender : UInt64) : Bytes :=
  key ++ nonce ++ ad ++ tag ++ LE64 sequence.toNat ++ LE64 sender.toNat

theorem roleLabel_length (role : Role) : (roleLabel role).length = 34 := by
  cases role <;> decide

/-- Role prefixes are disjoint, and within a role the complete digest is retained. -/
theorem signatureInput_eq_iff (leftRole rightRole : Role) (leftDigest rightDigest : Bytes) :
    signatureInput leftRole leftDigest = signatureInput rightRole rightDigest ↔
      leftRole = rightRole ∧ leftDigest = rightDigest := by
  cases leftRole
  all_goals cases rightRole
  all_goals simp [signatureInput, roleLabel]

/-- Length framing can be peeled inside a larger transcript when Rust's u64 conversion succeeds. -/
theorem hashField_append_inj {left right leftTail rightTail : Bytes}
    (leftFits : left.length < 2 ^ 64) (rightFits : right.length < 2 ^ 64)
    (same : hashField left ++ leftTail = hashField right ++ rightTail) :
    left = right ∧ leftTail = rightTail := by
  simp only [hashField, List.append_assoc] at same
  obtain ⟨lengths, tails⟩ := List.append_inj same (by simp)
  exact List.append_inj tails (LE64_inj leftFits rightFits lengths)

theorem literal_lengths :
    signingContext.length = 32 ∧ initDomain.length = 41 ∧ responseDomain.length = 45 := by
  decide

theorem signatureInput_length (role : Role) (digest : Bytes) :
    (signatureInput role digest).length = 99 + digest.length := by
  simp only [signatureInput, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil, roleLabel_length]

theorem signatures_excluded (hash : Hash512) (init : InitFields) (response : ResponseFields)
    (serverId : UInt64) (serverEd serverMldsa initDigest leftSignature rightSignature : Bytes) :
    signedInitHash hash ⟨init, leftSignature⟩ serverId serverEd serverMldsa =
      signedInitHash hash ⟨init, rightSignature⟩ serverId serverEd serverMldsa ∧
    signedResponseHash hash initDigest ⟨response, leftSignature⟩ =
      signedResponseHash hash initDigest ⟨response, rightSignature⟩ := ⟨rfl, rfl⟩

theorem associatedData_length (base serverDigest beaconDigest : Bytes)
    (baseWidth : base.length = 153) (serverWidth : serverDigest.length = 64)
    (beaconWidth : beaconDigest.length = 64) :
    (associatedData base serverDigest beaconDigest).length = 281 := by
  simp only [associatedData, List.length_append, baseWidth, serverWidth, beaconWidth]

/-- Existing slots are replaced; their previous fingerprint bytes do not survive. -/
theorem fillAssociatedData_overwrite (base oldServer oldBeacon serverDigest beaconDigest : Bytes)
    (baseWidth : base.length = 153) :
    fillAssociatedData (base ++ oldServer ++ oldBeacon) serverDigest beaconDigest =
      associatedData base serverDigest beaconDigest := by
  simp [fillAssociatedData, List.append_assoc, ← baseWidth]

/-- Equal associated data determines the ordered fingerprints, without asserting key/hash injectivity. -/
theorem associatedData_inj {leftBase rightBase leftServer rightServer leftBeacon rightBeacon : Bytes}
    (baseWidths : leftBase.length = rightBase.length)
    (serverWidths : leftServer.length = rightServer.length)
    (same : associatedData leftBase leftServer leftBeacon =
      associatedData rightBase rightServer rightBeacon) :
    leftBase = rightBase ∧ leftServer = rightServer ∧ leftBeacon = rightBeacon := by
  simp only [associatedData, List.append_assoc] at same
  exact ⟨(List.append_inj same baseWidths).1,
    List.append_inj (List.append_inj same baseWidths).2 serverWidths⟩

theorem le64_id_inj {left right : UInt64} (same : LE64 left.toNat = LE64 right.toNat) :
    left = right := by
  exact UInt64.toNat_inj.mp (LE64_inj left.toNat_lt right.toNat_lt same)

theorem initTranscript_length (init : InitFields) (serverId : UInt64)
    (serverEd serverMldsa : Bytes) (valid : init.WellFormed)
    (edWidth : serverEd.length = 32) (mldsaWidth : serverMldsa.length = 1952) :
    (initTranscript init serverId serverEd serverMldsa).length = 5495 := by
  simp only [initTranscript, hashField, List.length_append, LE64_length,
    literal_lengths.2.1, valid.identityWidth, valid.preWidth, valid.oneTimeWidth,
    valid.pqWidth, valid.mldsaWidth, edWidth, mldsaWidth]

theorem responseTranscript_length (initDigest : Bytes) (response : ResponseFields)
    (digestWidth : initDigest.length = 64) (valid : response.WellFormed) :
    (responseTranscript initDigest response).length = 1301 + response.appCipherText.length := by
  simp only [responseTranscript, hashField, List.length_append, LE64_length,
    literal_lengths.2.2, digestWidth, valid.identityWidth, valid.ephemeralWidth, valid.kemWidth]
  omega

theorem hashField_injective : Function.Injective hashField := by
  intro left right same
  have dropped := congrArg (List.drop 8) same
  simpa [hashField] using dropped

/-- Exact request preimages retain every field and both provisioned server pins. -/
theorem initTranscript_inj {left right : InitFields} {leftId rightId : UInt64}
    {leftEd rightEd leftServer rightServer : Bytes}
    (leftValid : left.WellFormed) (rightValid : right.WellFormed)
    (edWidths : leftEd.length = rightEd.length)
    (serverWidths : leftServer.length = rightServer.length)
    (same : initTranscript left leftId leftEd leftServer =
      initTranscript right rightId rightEd rightServer) :
    left = right ∧ leftId = rightId ∧ leftEd = rightEd ∧ leftServer = rightServer := by
  simp only [initTranscript, List.append_assoc, List.append_right_inj] at same
  obtain ⟨ids, same⟩ := List.append_inj same (by simp)
  obtain ⟨ed, same⟩ := List.append_inj same edWidths
  obtain ⟨mldsa, same⟩ := List.append_inj same
    (leftValid.mldsaWidth.trans rightValid.mldsaWidth.symm)
  obtain ⟨server, same⟩ := List.append_inj same serverWidths
  obtain ⟨identity, same⟩ := hashField_append_inj
    (by simp [leftValid.identityWidth]) (by simp [rightValid.identityWidth]) same
  obtain ⟨prekey, same⟩ := hashField_append_inj
    (by simp [leftValid.preWidth]) (by simp [rightValid.preWidth]) same
  obtain ⟨oneTime, pq⟩ := hashField_append_inj
    (by simp [leftValid.oneTimeWidth]) (by simp [rightValid.oneTimeWidth]) same
  exact ⟨InitFields.ext identity prekey oneTime (hashField_injective pq) mldsa,
    le64_id_inj ids, ed, server⟩

/-- Exact response preimages retain the request digest, raw application payload and assigned ID. -/
theorem responseTranscript_inj {left right : ResponseFields} {leftDigest rightDigest : Bytes}
    (leftValid : left.WellFormed) (rightValid : right.WellFormed)
    (digestWidths : leftDigest.length = rightDigest.length)
    (same : responseTranscript leftDigest left = responseTranscript rightDigest right) :
    left = right ∧ leftDigest = rightDigest := by
  simp only [responseTranscript] at same
  obtain ⟨same, ids⟩ := List.append_inj' same (by simp)
  simp only [List.append_assoc, List.append_right_inj] at same
  obtain ⟨digests, same⟩ := List.append_inj same digestWidths
  obtain ⟨identity, same⟩ := hashField_append_inj
    (by simp [leftValid.identityWidth]) (by simp [rightValid.identityWidth]) same
  obtain ⟨ephemeral, same⟩ := hashField_append_inj
    (by simp [leftValid.ephemeralWidth]) (by simp [rightValid.ephemeralWidth]) same
  obtain ⟨kem, application⟩ := hashField_append_inj
    (by simp [leftValid.kemWidth]) (by simp [rightValid.kemWidth]) same
  exact ⟨ResponseFields.ext identity ephemeral kem (hashField_injective application)
    (le64_id_inj ids), digests⟩

/-- Request and response domains are disjoint before hashing, even on arbitrary byte fields. -/
theorem initTranscript_ne_responseTranscript (init : InitFields) (serverId : UInt64)
    (serverEd serverMldsa digest : Bytes) (response : ResponseFields) :
    initTranscript init serverId serverEd serverMldsa ≠ responseTranscript digest response := by
  simp [initTranscript, responseTranscript, initDomain, responseDomain]

theorem commitmentInput_length (key nonce ad tag : Bytes) (sequence sender : UInt64)
    (keyWidth : key.length = 32) (nonceWidth : nonce.length = 12)
    (adWidth : ad.length = 281) (tagWidth : tag.length = 16) :
    (commitmentInput key nonce ad tag sequence sender).length = 357 := by
  simp only [commitmentInput, List.length_append, LE64_length, keyWidth,
    nonceWidth, adWidth, tagWidth]

theorem fillAssociatedData_length (base serverDigest beaconDigest : Bytes)
    (baseWidth : base.length = 281) (serverWidth : serverDigest.length = 64)
    (beaconWidth : beaconDigest.length = 64) :
    (fillAssociatedData base serverDigest beaconDigest).length = 281 := by
  simp only [fillAssociatedData, associatedData, List.length_append, List.length_take,
    baseWidth, serverWidth, beaconWidth]
  decide

theorem publicKeyHash_eq_some_iff (hash : Hash512) (key digest : Bytes) :
    publicKeyHash hash key = some digest ↔ key.length = 1952 ∧ hash key = digest := by
  simp [publicKeyHash]

end Pqxdh.TranscriptAuth

/-- info: 'Pqxdh.TranscriptAuth.roleLabel_length' does not depend on any axioms -/
#guard_msgs in
#print axioms Pqxdh.TranscriptAuth.roleLabel_length
/-- info: 'Pqxdh.TranscriptAuth.signatureInput_eq_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Pqxdh.TranscriptAuth.signatureInput_eq_iff
/-- info: 'Pqxdh.TranscriptAuth.hashField_append_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pqxdh.TranscriptAuth.hashField_append_inj
/-- info: 'Pqxdh.TranscriptAuth.literal_lengths' does not depend on any axioms -/
#guard_msgs in
#print axioms Pqxdh.TranscriptAuth.literal_lengths
/-- info: 'Pqxdh.TranscriptAuth.signatureInput_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Pqxdh.TranscriptAuth.signatureInput_length
/-- info: 'Pqxdh.TranscriptAuth.signatures_excluded' does not depend on any axioms -/
#guard_msgs in
#print axioms Pqxdh.TranscriptAuth.signatures_excluded
/-- info: 'Pqxdh.TranscriptAuth.associatedData_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Pqxdh.TranscriptAuth.associatedData_length
/-- info: 'Pqxdh.TranscriptAuth.fillAssociatedData_overwrite' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Pqxdh.TranscriptAuth.fillAssociatedData_overwrite
/-- info: 'Pqxdh.TranscriptAuth.associatedData_inj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Pqxdh.TranscriptAuth.associatedData_inj
/-- info: 'Pqxdh.TranscriptAuth.le64_id_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pqxdh.TranscriptAuth.le64_id_inj
/-- info: 'Pqxdh.TranscriptAuth.initTranscript_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Pqxdh.TranscriptAuth.initTranscript_length
/-- info: 'Pqxdh.TranscriptAuth.responseTranscript_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pqxdh.TranscriptAuth.responseTranscript_length
/-- info: 'Pqxdh.TranscriptAuth.hashField_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Pqxdh.TranscriptAuth.hashField_injective
/-- info: 'Pqxdh.TranscriptAuth.initTranscript_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pqxdh.TranscriptAuth.initTranscript_inj
/-- info: 'Pqxdh.TranscriptAuth.responseTranscript_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pqxdh.TranscriptAuth.responseTranscript_inj
/-- info: 'Pqxdh.TranscriptAuth.initTranscript_ne_responseTranscript' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Pqxdh.TranscriptAuth.initTranscript_ne_responseTranscript
/-- info: 'Pqxdh.TranscriptAuth.commitmentInput_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Pqxdh.TranscriptAuth.commitmentInput_length
/-- info: 'Pqxdh.TranscriptAuth.fillAssociatedData_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Pqxdh.TranscriptAuth.fillAssociatedData_length
/-- info: 'Pqxdh.TranscriptAuth.publicKeyHash_eq_some_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Pqxdh.TranscriptAuth.publicKeyHash_eq_some_iff
