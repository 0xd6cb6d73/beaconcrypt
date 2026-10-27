-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentEligibility

/-! Key match and ciphertext link of the public designation (CE-5, second part), under the approved codec contracts. The designation compares keys: the PQ key that the source attached verification yields from the accept bytes, and the PQ key read from the owner's published PQ field. A Server peer designated `(i, k)` was accepted under raw bytes whose verified PQ key is the KEM public key that owner `k` signed in its published bundle, and whose identity key is owner `k`'s identity key (`designate_keymatch`, with `Phase1ReadBack`). A Beacon owner `c` designated `(i, c)` is natively Established and pinned to the protected key ID and to the Server's own identity; the Phase 2 response of session `i` is the writer output of fields carrying the Server identity, the ciphertext read from `c`'s accepted finish input is the KEM ciphertext of those fields, and the PQ key verified at accept `i` is the one `c` signed in its published bundle (`owner_link`, with `Phase1ReadBack` and `Phase2ReadBack`). Both statements hold for every verification of the accept bytes by the native verification prefix `RawSignatures.verified`, whose candidate and source attached verification are exactly what the designation reads (`verified_keys`); no signature-scheme property and no wiring law is used for them. Owner `k`'s published key is tied to its native KEM pair only while the owner is not finished (`PublishedKey`): a finish or abort erases the KEM pair from the native state, so the tie to KEM creation index `k` of the pool after finish is not part of this module. No security assumption is made here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentInterface (Entry)
open PqxdhDeploymentTranscript (summarize candidateOf bundleOf buildOf acceptOf finishOf designate acceptedKeys publishedPq)
open PqxdhDeploymentEligibility (Agree BundleShaped BuildShaped kemPublic phaseClass pinnedKeyId)
open PqxdhServerAuthNegativeControl (Phase1ReadBack Phase2ReadBack)
open PqxdhEd25519EufCma (Phase1Candidate Phase1KeyTuple encodedIdentity)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Owner `k` published, in its honest bundle, the PQ key `pk` together with its own identity key, and still holds `pk` as its KEM public key unless it has finished. -/
def PublishedKey (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (transcript : List Entry)
    (native : PqxdhRegistrationSchedule.State KemSK) (k : Nat) (pk : PqxdhKemIndCca.MlKem768PublicKey) : Prop :=
  ∃ (owner : PqxdhRegistrationSchedule.Owner KemSK) (bytes : Pqxdh.Bytes) (keys : Phase1KeyTuple)
    (preSignature oneSignature pqSignature : PqxdhEd25519EufCma.Ed25519Signature),
    native.owners[k]? = some owner ∧ bundleOf transcript k = some bytes ∧
    codec.write1 (PqxdhJointPhase1SourceWriter.candidate (setup.joint.publicKeys owner.beacon.identity).ed25519 keys
      preSignature oneSignature pqSignature) = some bytes ∧
    keys.pqKey = pk ∧ (kemPublic owner.beacon.phase = none ∨ kemPublic owner.beacon.phase = some pk)

/-- The bundle bytes of an owner come from a successful bundle entry of the transcript. -/
theorem bundleOf_mem (transcript : List Entry) (k : Nat) (bytes : Pqxdh.Bytes) (found : bundleOf transcript k = some bytes) :
    (⟨.inl (.inr (.bundle k)), some bytes⟩ : Entry) ∈ transcript := by
  obtain ⟨entry, member, value⟩ := List.exists_of_findSome?_eq_some found
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · cases value
  · cases command with
    | bundle index =>
        cases reply with
        | none => cases value
        | some other =>
            simp only at value
            split at value
            · rename_i same
              simp only [Option.some.injEq] at value
              subst same value
              exact member
            · cases value
    | _ => cases value
  · cases value

/-- The response of a session comes from a successful build entry of the transcript. -/
theorem buildOf_mem (transcript : List Entry) (session : Nat) (response : PqxdhServerRegistrationPublication.Response)
    (found : buildOf transcript session = some response) :
    ∃ payload, (⟨.inl (.inr (.build session payload)), some response⟩ : Entry) ∈ transcript := by
  obtain ⟨entry, member, value⟩ := List.exists_of_findSome?_eq_some found
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · cases value
  · cases command with
    | build index payload =>
        cases reply with
        | none => cases value
        | some other =>
            simp only at value
            split at value
            · rename_i same
              simp only [Option.some.injEq] at value
              subst same value
              exact ⟨payload, member⟩
            · cases value
    | _ => cases value
  · cases value

/-- Under `Phase1ReadBack`, the raw candidate read from a Phase 1 writer output is the written candidate. -/
theorem candidateOf_written (codec : Codec Reader Response) (phase1 : Phase1ReadBack codec) (candidate : Phase1Candidate)
    (bytes : Pqxdh.Bytes) (written : codec.write1 candidate = some bytes) : candidateOf codec bytes = some candidate := by
  obtain ⟨reader, read, identity, pq, pre, one⟩ := phase1 candidate bytes written
  simp only [candidateOf, PqxdhRegistrationJointRawSignatures.candidate, read, identity, pq, pre, one,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def]

/-- A verified raw accept whose PQ field is an attached signature over the PQ message of `pk` verifies to `pk`. -/
theorem verified_signed_pq (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (raw : Pqxdh.Bytes) (value : PqxdhServerRootPreparation.Verified Reader)
    (accepted : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value)
    (signature : PqxdhEd25519EufCma.Ed25519Signature) (pk : PqxdhKemIndCca.MlKem768PublicKey)
    (field : value.candidate.pqKey = PqxdhEd25519EufCma.attachSignature signature (PqxdhEd25519EufCma.pqMessage pk)) :
    value.keys.pqKey = pk := by
  have origin := (PqxdhRegistrationJointRawSignatures.verified_origin setup codec checks raw value accepted).2
  simp only [PqxdhJointPhase1Reports.sourceAccept, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at origin
  obtain ⟨publicKey, _, pqPayload, pqVerified, _, _, _, _, _, _, _, _, _, _, pqKey, pqParsed, same⟩ := origin
  rw [field, setup.wiring.verifyAttached] at pqVerified
  split at pqVerified
  · simp only [Option.some.injEq] at pqVerified
    subst pqVerified
    rw [PqxdhEd25519EufCma.parsePqMessage_pqMessage, Option.some.injEq] at pqParsed
    subst pqParsed
    rw [Prod.mk.injEq] at same
    rw [← same.2]
  · cases pqVerified

/-- A verification of raw accept bytes by the native verification prefix reads exactly the raw candidate of the designation, and the source attached verification of that candidate yields the verified identity key and key tuple. -/
theorem verified_keys (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (raw : Pqxdh.Bytes) (value : PqxdhServerRootPreparation.Verified Reader)
    (accepted : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value) :
    candidateOf codec raw = some value.candidate ∧
      acceptedKeys setup.source.crypto value.candidate = some (value.identity, value.keys) :=
  PqxdhRegistrationJointRawSignatures.verified_origin setup codec checks raw value accepted

/-- The PQ key read from an honest published candidate is the key whose PQ message it signed. -/
theorem publishedPq_candidate (identity : PqxdhEd25519EufCma.Ed25519PublicKey) (keys : Phase1KeyTuple)
    (preSignature oneSignature pqSignature : PqxdhEd25519EufCma.Ed25519Signature) :
    publishedPq (PqxdhJointPhase1SourceWriter.candidate identity keys preSignature oneSignature pqSignature) =
      some keys.pqKey := by
  simp [publishedPq, PqxdhJointPhase1SourceWriter.candidate]

/-- The published bundle of a designated owner gives its honest candidate and its published key. -/
theorem published_candidate (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (phase1 : Phase1ReadBack codec) (server : RawCtxServerRouting.Identity) (transcript : List Entry)
    (native : PqxdhRegistrationSchedule.State KemSK) (agree : Agree setup codec server transcript native) (k : Nat)
    (published : Phase1Candidate) (found : (bundleOf transcript k).bind (candidateOf codec) = some published) :
    ∃ (owner : PqxdhRegistrationSchedule.Owner KemSK) (keys : Phase1KeyTuple)
      (preSignature oneSignature pqSignature : PqxdhEd25519EufCma.Ed25519Signature),
      published = PqxdhJointPhase1SourceWriter.candidate (setup.joint.publicKeys owner.beacon.identity).ed25519 keys
        preSignature oneSignature pqSignature ∧
      PublishedKey setup codec transcript native k keys.pqKey := by
  obtain ⟨bytes, bytesFound, read⟩ := Option.bind_eq_some_iff.mp found
  have shaped := agree.bundles _ (bundleOf_mem transcript k bytes bytesFound)
  obtain ⟨owner, keys, s1, s2, s3, ownerFound, written, kem⟩ := shaped
  rw [candidateOf_written codec phase1 _ bytes written, Option.some.injEq] at read
  exact ⟨owner, keys, s1, s2, s3, read.symm, owner, bytes, keys, s1, s2, s3, ownerFound, bytesFound, written, rfl, kem⟩

/-- Server-side key match: for a Server peer designated `(i, k)`, every verification of the accept bytes of session `i` yields owner `k`'s identity key and the PQ key owner `k` published in its honest bundle. -/
theorem designate_keymatch (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (phase1 : Phase1ReadBack codec) (server : RawCtxServerRouting.Identity) (serverKid : Std.U64)
    (transcript : List Entry) (native : PqxdhRegistrationSchedule.State KemSK)
    (agree : Agree setup codec server transcript native) (keyId : Std.U64) (session k : Nat)
    (designated : designate setup.source.crypto codec serverKid transcript (.peer keyId) = some (session, k))
    (raw : Pqxdh.Bytes) (accepted : acceptOf transcript session = some raw)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (verifiedRaw : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value) :
    PublishedKey setup codec transcript native k value.keys.pqKey ∧
      ∃ owner : PqxdhRegistrationSchedule.Owner KemSK, native.owners[k]? = some owner ∧
        value.candidate.identityKey = encodedIdentity (setup.joint.publicKeys owner.beacon.identity).ed25519 := by
  obtain ⟨_, raw', candidate, keys, _, rawFound, candidateFound, keysFound, _, publishes⟩ :=
    PqxdhDeploymentTranscript.designate_peer setup.source.crypto codec serverKid keyId transcript session k designated
  rw [accepted, Option.some.injEq] at rawFound
  subst rawFound
  obtain ⟨origin, sourced⟩ := verified_keys setup codec checks raw value verifiedRaw
  rw [candidateFound, Option.some.injEq] at origin
  subst origin
  rw [keysFound, Option.some.injEq] at sourced
  subst sourced
  obtain ⟨published, publishedFound, identityEq, pqEq⟩ := publishes
  obtain ⟨owner, keys', s1, s2, s3, honest, publishedKey⟩ :=
    published_candidate setup codec phase1 server transcript native agree k published publishedFound
  rw [honest, publishedPq_candidate, Option.some.injEq] at pqEq
  obtain ⟨owner', bytes, keys'', s1', s2', s3', ownerFound, rest⟩ := publishedKey
  refine ⟨by rw [← pqEq]; exact ⟨owner', bytes, keys'', s1', s2', s3', ownerFound, rest⟩, owner', ownerFound, ?_⟩
  obtain ⟨bytesFound, written, _⟩ := rest
  obtain ⟨bytes2, bytesFound2, read⟩ := Option.bind_eq_some_iff.mp publishedFound
  rw [bytesFound, Option.some.injEq] at bytesFound2
  subst bytesFound2
  rw [candidateOf_written codec phase1 _ bytes written, Option.some.injEq] at read
  rw [← identityEq, ← read]
  rfl

/-- Beacon-side ciphertext link: an owner designated `(i, c)` is natively Established and pinned to the protected key ID and to the Server's own identity; the response of session `i` is the Phase 2 writer output of fields carrying the Server identity; the ciphertext read from the owner's accepted finish input is the KEM ciphertext of those fields; and every verification of the accept bytes of session `i` yields the PQ key the owner published in its honest bundle. -/
theorem owner_link (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (phase1 : Phase1ReadBack codec) (phase2 : Phase2ReadBack codec) (server : RawCtxServerRouting.Identity)
    (serverKid : Std.U64) (transcript : List Entry) (native : PqxdhRegistrationSchedule.State KemSK)
    (agree : Agree setup codec server transcript native) (index session k : Nat)
    (designated : designate setup.source.crypto codec serverKid transcript (.owner index) = some (session, k)) :
    k = index ∧ ∃ (owner : PqxdhRegistrationSchedule.Owner KemSK) (response : PqxdhServerRegistrationPublication.Response)
      (fields : PqxdhServerRegistrationPublication.ResponseFields) (raw : Pqxdh.Bytes),
      native.owners[index]? = some owner ∧ phaseClass owner.beacon.phase = .established ∧
      pinnedKeyId owner.beacon.phase = serverKid ∧ owner.beacon.serverIdentity = server ∧
      buildOf transcript session = some response ∧ codec.write2 fields = some response.serialized ∧
      fields.identity = server ∧ finishOf transcript index = some raw ∧
      (codec.read2 raw).bind codec.ciphertext = some fields.kemCiphertext ∧
      ∀ accepted value, acceptOf transcript session = some accepted →
        PqxdhRegistrationJointRawSignatures.verified setup codec checks accepted = some value →
        PublishedKey setup codec transcript native index value.keys.pqKey := by
  obtain ⟨same, established, pin, raw, ciphertext, published, pqKey, binding, rawFound, ciphertextFound, publishedFound,
    pqKeyFound, _, linked⟩ :=
    PqxdhDeploymentTranscript.designate_owner setup.source.crypto codec serverKid transcript index session k designated
  obtain ⟨owner, ownerFound, pinEq, keyEq⟩ := agree.bindings index pin serverKid binding
  have phases := agree.phases index
  rw [established, ownerFound] at phases
  obtain ⟨response, acceptedCandidate, keys, responseFound, responseCiphertext, responseIdentity, acceptFound, keysFound,
    pqEq⟩ := linked
  obtain ⟨payload, member⟩ := buildOf_mem transcript session response responseFound
  obtain ⟨fields, written, fieldsIdentity⟩ := agree.builds _ member
  obtain ⟨decoded, read, cipherEq, _, identityEq, _, _⟩ := phase2 fields response.serialized written
  simp only [read, Option.bind_some] at responseCiphertext responseIdentity
  rw [cipherEq, Option.some.injEq] at responseCiphertext
  rw [identityEq, Option.some.injEq] at responseIdentity
  obtain ⟨owner', keys', s1, s2, s3, honest, publishedKey⟩ :=
    published_candidate setup codec phase1 server transcript native agree index published publishedFound
  rw [honest, publishedPq_candidate, Option.some.injEq] at pqKeyFound
  refine ⟨same, owner, response, fields, raw, ownerFound, phases.symm, keyEq, ?_, responseFound, written,
    fieldsIdentity, rawFound, ?_, ?_⟩
  · rw [pinEq, ← responseIdentity, fieldsIdentity]
  · rw [ciphertextFound, responseCiphertext]
  · intro accepted value acceptedFound verifiedRaw
    obtain ⟨acceptedBytes, acceptedBytesFound, acceptedRead⟩ := Option.bind_eq_some_iff.mp acceptFound
    rw [acceptedFound, Option.some.injEq] at acceptedBytesFound
    subst acceptedBytesFound
    obtain ⟨origin, sourced⟩ := verified_keys setup codec checks accepted value verifiedRaw
    rw [acceptedRead, Option.some.injEq] at origin
    subst origin
    rw [keysFound, Option.some.injEq] at sourced
    subst sourced
    rw [pqEq, ← pqKeyFound]
    exact publishedKey

/-- `designate_keymatch` on every outcome of the complete experiment, in either mode, for the protected Server key ID. -/
theorem keymatch_game {A X : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (phase1 : Phase1ReadBack codec) (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds
      mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (reached : outcome.1 = some (created, output, final))
    (keyId : Std.U64) (session k : Nat)
    (designated : designate setup.source.crypto codec setup.serverKeyId final.1.transcript (.peer keyId) =
      some (session, k))
    (raw : Pqxdh.Bytes) (accepted : acceptOf final.1.transcript session = some raw)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (verifiedRaw : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value) :
    PublishedKey setup codec final.1.transcript final.2.native k value.keys.pqKey ∧
      ∃ owner : PqxdhRegistrationSchedule.Owner KemSK, final.2.native.owners[k]? = some owner ∧
        value.candidate.identityKey = encodedIdentity (setup.joint.publicKeys owner.beacon.identity).ed25519 :=
  designate_keymatch setup codec checks phase1 _ setup.serverKeyId final.1.transcript final.2.native
    (PqxdhDeploymentEligibility.agree_game setup codec checks route ensureInit identityIndex bounds mode adversary
      runtime outcome supported created output final reached) keyId session k designated raw accepted value verifiedRaw

/-- `owner_link` on every outcome of the complete experiment, in either mode, for the protected Server key ID; the Server identity is the final native one, which never changes. -/
theorem link_game {A X : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (phase1 : Phase1ReadBack codec) (phase2 : Phase2ReadBack codec) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds
      mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (reached : outcome.1 = some (created, output, final))
    (index session k : Nat)
    (designated : designate setup.source.crypto codec setup.serverKeyId final.1.transcript (.owner index) =
      some (session, k)) :
    k = index ∧ ∃ (owner : PqxdhRegistrationSchedule.Owner KemSK) (response : PqxdhServerRegistrationPublication.Response)
      (fields : PqxdhServerRegistrationPublication.ResponseFields) (raw : Pqxdh.Bytes),
      final.2.native.owners[index]? = some owner ∧ phaseClass owner.beacon.phase = .established ∧
      pinnedKeyId owner.beacon.phase = setup.serverKeyId ∧
      owner.beacon.serverIdentity = final.2.native.shared.2.server.server.identity ∧
      buildOf final.1.transcript session = some response ∧ codec.write2 fields = some response.serialized ∧
      fields.identity = final.2.native.shared.2.server.server.identity ∧ finishOf final.1.transcript index = some raw ∧
      (codec.read2 raw).bind codec.ciphertext = some fields.kemCiphertext ∧
      ∀ accepted value, acceptOf final.1.transcript session = some accepted →
        PqxdhRegistrationJointRawSignatures.verified setup codec checks accepted = some value →
        PublishedKey setup codec final.1.transcript final.2.native index value.keys.pqKey :=
  owner_link setup codec checks phase1 phase2 _ setup.serverKeyId final.1.transcript final.2.native
    (PqxdhDeploymentEligibility.agree_game setup codec checks route ensureInit identityIndex bounds mode adversary
      runtime outcome supported created output final reached) index session k designated

end BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.bundleOf_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.bundleOf_mem

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.buildOf_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.buildOf_mem

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.candidateOf_written' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.candidateOf_written

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.verified_signed_pq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.verified_signed_pq

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.verified_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.verified_keys

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.publishedPq_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.publishedPq_candidate

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.published_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.published_candidate

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.designate_keymatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.designate_keymatch

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.owner_link' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.owner_link

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.keymatch_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.keymatch_game

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.link_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch.link_game
