-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant
import BeaconcryptCore.Computational.PqxdhDeploymentReplay
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTranscript

/-!
# Ten of the eleven session fields, read from the experiment's final state (O21, part 2)

`Fields` is `PqxdhServerAuthRootSession.Session` without `root`, with ServerAuth's one-constructor `Position` replaced by the CE creation index. On a final state of `PqxdhDeploymentSecrecy.game`:

- `serverFields` is the Server's production for a session handle: the live Server object's identity and key ID; the accept bytes looked up by the handle (`PqxdhDeploymentTranscript.acceptOf`), the identity key, key tuple and initial key exchange of their verified candidate, and the registration ID read from them (`PqxdhDeploymentReplay.registrationOf`); the Beacon identity that the Server's reader takes from those bytes (`PqxdhDeploymentCompile.identityOf`); and the associated data of the handle's first logged seal context, the context the Server sealed with (`PqxdhDeploymentSessionFieldsInvariant.sealOf`).
- `beaconFields` is owner `c`'s acceptance: its native pin, identity key (from its identity seed) and pinned key ID, its stored 151-byte associated data (`PqxdhTranscriptAd.adOf` of its transcript digest), and the prekey, one-time and PQ keys of its first published bundle (the finish drops the secrets, as in Rust).
- `FieldsAgree c session`: both are defined and equal, and the registration ID is in the Server's consumed list.

The fields are read from each party's state and from the transcript. The Server-side Beacon identity, initial key exchange, registration ID and keys are public-reader decodings of the accept bytes in the transcript, and the Beacon-side initial key exchange, registration ID and keys combine its identity key with its first published bundle in the transcript; the equality of the keys is a conjunct of CE-A1's `PinnedMatchAt` itself. The state-level content beyond CE-A1's matching is the equality of the associated data of the Server's first logged seal context with the Beacon's stored one, of the Beacon's pinned key ID with the Server's key ID, and of the accepted identity key with the owner's identity-seed key, and the Server's consumption of the registration ID.

`pinned_agree_transcript` (identity index 0, generated seed): on every outcome, a session that transcript-matches an accepted owner pinned to the protected binding (`PqxdhDeploymentServerAuthTranscript.TranscriptMatchAt`: CE-A1's pinned match plus one public registration transcript computed both from the session's accept bytes and a successful build response and from the owner's first published bundle and its accepting finish input) agrees with it on the ten fields. Both sides' associated data are `PqxdhTranscriptAd.adOf` of the digest that the final BLAKE2b cache holds for that one transcript, and the cache is a function. A pinned match alone no longer fixes the associated data: under the hashed associated data, two sessions with the same keys can have different transcripts. Ingredients: the run invariants of `PqxdhDeploymentSessionFieldsInvariant` (`inv_game`), positional session handles (`PqxdhDeploymentHeadlineGap.accept_positional`), `PqxdhDeploymentServerAuthInjectiveGame.keys_identity`, `PqxdhDeploymentEligibility.agree_game` and `PqxdhDeploymentReplay.replay_game`; premises: the approved Phase 1 and Phase 2 read-back contracts, which read the public transcripts back to the hashed ones. `established_end`: an accepted owner is established at the end. `identityOf_accepted`, `publishedKeys_prefix` and `finish_entry` are the public-reader facts used.

The root is not among the fields. The experiment retains no labelled Beacon root: the Server's session roots are in its touch log, the Extract entry from which the Beacon's root is expanded sits unlabelled in the shared HMAC cache, and the Beacon's evolving ratchet kernel is derived from that root, but no field of the outcome is the Beacon's root, so root equality is not a readout of the outcome. The payload and the assigned key ID are not among the eleven ServerAuth fields and are not stated.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentSessionFields
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentInterface (FreshBounds ModeSpec Mode Entry)
open PqxdhDeploymentServerAuthEvent (Reg regsOf accepted summarizeReg protectedBinding publishedKeys)
open PqxdhDeploymentServerAuthTranscript (TranscriptMatchAt)
open PqxdhDeploymentSessionFieldsInvariant (sealOf establishedAd)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The fields of `PqxdhServerAuthRootSession.Session` other than `root`, in the same order and with the same types, except that `origin` is the CE creation index; ServerAuth's `Position` has the single constructor `targetPhase1`, so `origin` is definitional on both sides there as here. -/
structure Fields where
  serverIdentity : PqxdhBeaconPhase2Preparation.Word32
  beaconIdentity : PqxdhBeaconPhase2Preparation.Word32
  initKex : beaconcrypt_core.pqxdh.InitKex
  registrationId : Pqxdh.Bytes
  prekey : PqxdhEd25519EufCma.X25519PublicKey
  oneTime : PqxdhEd25519EufCma.X25519PublicKey
  pqKey : PqxdhKemIndCca.MlKem768PublicKey
  associatedData : Pqxdh.Bytes
  pinnedServerId : Std.U64
  origin : Nat

/-- Forget the root of a ServerAuth session, with a CE creation index as origin. -/
def Fields.ofSession (session : PqxdhServerAuthRootSession.Session) (origin : Nat) : Fields :=
  ⟨session.serverIdentity, session.beaconIdentity, session.initKex, session.registrationId, session.prekey,
    session.oneTime, session.pqKey, session.associatedData, session.pinnedServerId, origin⟩

/-- The Server's production for handle `session`: its identity and key ID, the accept looked up by the handle, its registration-ID reader, and the handle's first logged seal context. -/
noncomputable def serverFields (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (final : PqxdhDeploymentSecrecy.State KemSK) (session origin : Nat) : Option Fields := do
  let raw ← PqxdhDeploymentTranscript.acceptOf final.1.transcript session
  let candidate ← PqxdhDeploymentTranscript.candidateOf codec raw
  let keys ← PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto candidate
  let beacon ← PqxdhDeploymentCompile.identityOf codec raw
  let registration ← PqxdhDeploymentReplay.registrationOf setup.source.crypto codec raw
  let context ← sealOf final.2.native.shared.2.ghost.seals session
  pure ⟨final.2.native.shared.2.server.server.identity, beacon, PqxdhServerAuthPhase1Projection.unsigned keys.1 keys.2,
    registration, keys.2.prekey, keys.2.oneTime, keys.2.pqKey, context.associatedData,
    final.2.native.shared.2.server.identityKeyId, origin⟩

/-- Owner `c`'s acceptance: its identity seed, pin, pinned key ID and stored associated data, and its first published bundle (the finish drops the prekey, one-time and KEM secrets). -/
noncomputable def beaconFields (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (final : PqxdhDeploymentSecrecy.State KemSK) (c : Nat) : Option Fields := do
  let owner ← final.2.native.owners[c]?
  let keys ← publishedKeys codec (regsOf final.1.transcript) c
  let associatedData ← establishedAd owner.beacon.phase
  let identity := (setup.joint.publicKeys owner.beacon.identity).ed25519
  pure ⟨owner.beacon.serverIdentity, PqxdhRootTableInitialization.rootArray identity,
    PqxdhServerAuthPhase1Projection.unsigned identity keys.2, identity.toList ++ keys.2.oneTime.toList,
    keys.2.prekey, keys.2.oneTime, keys.2.pqKey, PqxdhRefinement.absBytes associatedData,
    PqxdhDeploymentEligibility.pinnedKeyId owner.beacon.phase, c⟩

/-- Handle `session`'s production agrees with owner `c` on the ten fields, and the Server consumed its registration ID. -/
def FieldsAgree (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (final : PqxdhDeploymentSecrecy.State KemSK) (c session : Nat) : Prop :=
  ∃ fields, serverFields setup codec final session c = some fields ∧ beaconFields setup codec final c = some fields ∧
    fields.registrationId ∈ final.2.native.shared.2.server.consumed

/-- The identity key read from accept bytes is the 32-byte word of the identity key that the source attached verification accepted. -/
theorem identityOf_accepted (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (raw : Pqxdh.Bytes)
    (candidate : PqxdhEd25519EufCma.Phase1Candidate)
    (keys : PqxdhEd25519EufCma.Ed25519PublicKey × PqxdhEd25519EufCma.Phase1KeyTuple)
    (read : PqxdhDeploymentTranscript.candidateOf codec raw = some candidate)
    (verified : PqxdhDeploymentTranscript.acceptedKeys crypto candidate = some keys) :
    PqxdhDeploymentCompile.identityOf codec raw = some (PqxdhRootTableInitialization.rootArray keys.1) := by
  have encoded := PqxdhDeploymentHeadlineGap.acceptedKeys_identity crypto candidate keys.1 keys.2 verified
  unfold PqxdhDeploymentTranscript.candidateOf PqxdhRegistrationJointRawSignatures.candidate at read
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at read
  obtain ⟨reader, readerEq, identity, identityEq, _, _, _, _, _, _, rfl⟩ := read
  simp only [PqxdhDeploymentCompile.identityOf, readerEq, identityEq, Option.bind_eq_bind, Option.bind_some]
  rw [show identity = PqxdhEd25519EufCma.encodedIdentity keys.1 from encoded,
    PqxdhEd25519EufCma.parseIdentity_encodedIdentity]
  rfl

/-- The first published bundle's keys found in a prefix of the registration view are those of the whole view. -/
theorem publishedKeys_prefix (codec : Codec Reader Response) (before regs : List Reg) (prefixed : before <+: regs)
    (owner : Nat) (keys : PqxdhEd25519EufCma.Ed25519PublicKey × PqxdhEd25519EufCma.Phase1KeyTuple)
    (found : publishedKeys codec before owner = some keys) : publishedKeys codec regs owner = some keys := by
  unfold publishedKeys PqxdhDeploymentServerAuthEvent.keysOfBundle at found ⊢
  obtain ⟨bytes, bytesFound, rest⟩ := Option.bind_eq_some_iff.mp found
  rw [PqxdhDeploymentServerAuthInjectiveGame.bundleOfReg_prefix _ _ prefixed owner bytes bytesFound]
  exact rest

/-- On every outcome of the experiment, an owner that accepted in the registration view of the final transcript is natively established at the end (`PqxdhDeploymentSessionFieldsInvariant.inv_game`, `BeaconInv.accepts`). -/
theorem established_end (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) ×
      A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex
      bounds mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (reached : outcome.1 = some (created, output, final))
    (c : Nat) (before : List Reg) (raw : Pqxdh.Bytes)
    (found : accepted c (regsOf final.1.transcript) = some (before, raw)) :
    ∃ owner control associatedData kernel, final.2.native.owners[c]? = some owner ∧
      owner.beacon.phase = .established control associatedData kernel :=
  (PqxdhDeploymentSessionFieldsInvariant.inv_game setup codec checks route ensureInit identityIndex bounds mode
    adversary runtime outcome supported created output final reached).2.2.accepts c before raw found

/-- A successful or failed finish of the registration view of a transcript is a finish entry of the transcript with the same owner, input and reply. -/
theorem finish_entry (transcript : List Entry) (owner : Nat) (raw : Pqxdh.Bytes) (reply : Option Pqxdh.Bytes)
    (member : Reg.finish owner raw reply ∈ regsOf transcript) :
    (⟨.inl (.inr (.finish owner raw)), reply⟩ : Entry) ∈ transcript := by
  simp only [regsOf, List.mem_filterMap] at member
  obtain ⟨entry, entryMember, found⟩ := member
  rcases entry with ⟨(coin | command) | secrecy, entryReply⟩
  · cases found
  · cases command with
    | create pin keyId =>
        cases entryReply with
        | none => cases found
        | some index =>
            cases parsed : PqxdhDeploymentInterface.parsePin pin <;>
              simp [PqxdhDeploymentServerAuthEvent.regOfEntry, parsed] at found
    | finish index input =>
        simp only [PqxdhDeploymentServerAuthEvent.regOfEntry, Option.some.injEq, Reg.finish.injEq] at found
        obtain ⟨rfl, rfl, rfl⟩ := found
        exact entryMember
    | _ => simp [PqxdhDeploymentServerAuthEvent.regOfEntry] at found
  · cases found

/-- The deterministic core at identity index 0: a session that transcript-matches an accepted owner pinned to the protected binding agrees with it on the ten fields read from the experiment's final state, and the Server consumed its registration ID. The accept is looked up by the session handle (`PqxdhDeploymentHeadlineGap.accept_positional`); the Server's seal context is the handle's first logged one, sealed under `PqxdhTranscriptAd.adOf` of the cached digest of the transcript of the retained Init fields of that accept and the Phase 2 fields written to the build response (`ServerInv.sealedTranscript`); the owner's stored associated data is `PqxdhTranscriptAd.adOf` of the cached digest of the transcript of its retained bundle, which is its first published bundle, and its accepting finish input (`BeaconInv.installedTranscript`, `BeaconInv.bundled`). The Phase 1 and Phase 2 read-back contracts read the match's public transcripts back to these two hashed transcripts, so both are the one public transcript of the match and the two digests are the single value the final cache holds for it. The owner's identity key, pin and pinned key ID are read from its native state (`PqxdhDeploymentServerAuthInjectiveGame.keys_identity`, `PqxdhDeploymentEligibility.Agree`, `BeaconInv`); the consumed registration IDs are the transcript's (`PqxdhDeploymentReplay.replay_game`). Premises: the approved Phase 1 and Phase 2 read-back contracts. -/
theorem pinned_agree_transcript (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) ×
      A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (reached : outcome.1 = some (created, output, final)) (c : Nat)
    (before : List Reg) (raw : Pqxdh.Bytes) (found : accepted c (regsOf final.1.transcript) = some (before, raw))
    (bound : (summarizeReg before).owners[c]? = some (protectedBinding setup created)) (session : Nat)
    (matched : TranscriptMatchAt setup.source.crypto codec c session (protectedBinding setup created).1 before raw) :
    FieldsAgree setup codec final c session := by
  obtain ⟨identity, serverInv, beaconInv⟩ := PqxdhDeploymentSessionFieldsInvariant.inv_game setup codec checks route
    ensureInit 0 bounds mode adversary runtime outcome supported created output final reached
  have agree := PqxdhDeploymentEligibility.agree_game setup codec checks route ensureInit 0 bounds mode adversary
    runtime outcome supported created output final reached
  obtain ⟨acceptRaw, candidate, keys, _, _, _, transcriptPayload, transcriptReply, bundle, transcript, acceptMember,
    candidateEq, keysEq, publishedEq, _, _, _, _, transcriptBuild, bundleFound, serverTranscript, beaconTranscript⟩ :=
    matched
  have prefixed := PqxdhDeploymentServerAuthEvent.accepted_prefix c _ before raw found
  have acceptEntry := PqxdhDeploymentHeadlineGap.accept_entry final.1.transcript acceptRaw (some session)
    (prefixed.subset acceptMember)
  have buildEntry := PqxdhDeploymentServerAuth.build_entry final.1.transcript session transcriptPayload transcriptReply
    (prefixed.subset transcriptBuild)
  obtain ⟨_, acceptOfEq⟩ := PqxdhDeploymentHeadlineGap.accept_positional setup codec checks route ensureInit phase1
    phase2 bounds mode adversary runtime outcome supported created output final reached acceptRaw session acceptEntry
  have beaconId := identityOf_accepted setup.source.crypto codec acceptRaw candidate keys candidateEq keysEq
  have registrationEq : PqxdhDeploymentReplay.registrationOf setup.source.crypto codec acceptRaw =
      some (keys.1.toList ++ keys.2.oneTime.toList) := by
    simp [PqxdhDeploymentReplay.registrationOf, candidateEq, keysEq]
  -- The Server's seal: the transcript of the handle's accept and the written build response.
  obtain ⟨sealRaw, init, serverCandidate, frameBytes, serverDigest, context, sealAccept, sealInit, written,
    serverCached, sealEq, ad⟩ := serverInv.sealedTranscript session transcriptPayload transcriptReply buildEntry
  obtain ⟨_, sealAcceptOf⟩ := PqxdhDeploymentHeadlineGap.accept_positional setup codec checks route ensureInit phase1
    phase2 bounds mode adversary runtime outcome supported created output final reached sealRaw session sealAccept
  rw [acceptOfEq, Option.some.injEq] at sealAcceptOf
  rw [← sealAcceptOf] at sealInit
  obtain ⟨_, readReply, ciphertextRead, ephemeralRead, serverRead, assignedRead, _⟩ := phase2 _ _ written
  have serverReply : responseOf codec transcriptReply.serialized =
      some (PqxdhTranscriptAd.serverResponse serverCandidate) := by
    simp only [responseOf, readReply, ciphertextRead, ephemeralRead, serverRead, assignedRead, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]
    rfl
  simp only [PqxdhDeploymentCompile.publicTranscript, sealInit, serverReply, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.some.injEq] at serverTranscript
  rw [serverTranscript] at serverCached
  -- The owner's establishment: the transcript of its retained bundle and its accepting finish input.
  obtain ⟨finishPayload, rest, split⟩ := PqxdhDeploymentHeadlineGap.accepted_split c _ before raw found
  have finishEntry := finish_entry final.1.transcript c raw (some finishPayload) (by rw [split]; simp)
  obtain ⟨installed, retainedInit, response, beaconDigest, installedFound, initFound, decoded, beaconCached, stored⟩ :=
    beaconInv.installedTranscript c raw finishPayload finishEntry
  have bundleFull := PqxdhDeploymentServerAuthInjectiveGame.bundleOfReg_prefix before _ prefixed c bundle bundleFound
  rw [PqxdhDeploymentServerAuthInjectiveGame.bundleOfReg_regsOf] at bundleFull
  obtain ⟨bundled, bundledFound, bundleWritten⟩ :=
    beaconInv.bundled c bundle (PqxdhDeploymentKeyMatch.bundleOf_mem _ c bundle bundleFull)
  rw [initFound, Option.some.injEq] at bundledFound
  subst bundledFound
  have beaconInit := PqxdhDeploymentCompileInvariant.publicInit_bundle codec phase1 _ bundle bundleWritten
  simp only [PqxdhDeploymentCompile.publicTranscript, beaconInit, decoded, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.some.injEq] at beaconTranscript
  rw [beaconTranscript, serverCached, Option.some.injEq] at beaconCached
  subst beaconCached
  -- The remaining fields, as for the pinned match.
  obtain ⟨owner, control, associatedData, kernel, ownerFound, ownerPhase⟩ := beaconInv.accepts c before raw found
  rw [ownerFound, Option.some.injEq] at installedFound
  subst installedFound
  rw [ownerPhase] at stored
  simp only [PqxdhDeploymentSessionFieldsInvariant.establishedAd, Option.some.injEq] at stored
  subst stored
  obtain ⟨entry, entryFound, keysId⟩ := PqxdhDeploymentServerAuthInjectiveGame.keys_identity setup codec phase1 _
    final.1.transcript final.2.native agree before prefixed c keys publishedEq
  rw [ownerFound, Option.some.injEq] at entryFound
  subst entryFound
  have publishedFull := publishedKeys_prefix codec before _ prefixed c keys publishedEq
  have bindingFull := PqxdhDeploymentHeadlineGap.owners_prefix_get before (regsOf final.1.transcript) prefixed c _ bound
  rw [← PqxdhDeploymentServerAuthEvent.summarize_regs] at bindingFull
  obtain ⟨bound', boundFound, pinEq, keyEq⟩ := agree.bindings c _ _ bindingFull
  rw [ownerFound, Option.some.injEq] at boundFound
  subst boundFound
  rw [ownerPhase] at keyEq
  have consumed := (PqxdhDeploymentReplay.replay_game setup codec checks route ensureInit 0 bounds mode adversary
    runtime outcome supported created output final reached (keys.1.toList ++ keys.2.oneTime.toList)).2
  refine ⟨⟨(protectedBinding setup created).1, PqxdhRootTableInitialization.rootArray keys.1,
    PqxdhServerAuthPhase1Projection.unsigned keys.1 keys.2, keys.1.toList ++ keys.2.oneTime.toList, keys.2.prekey,
    keys.2.oneTime, keys.2.pqKey, PqxdhRefinement.absBytes (PqxdhTranscriptAd.adOf serverDigest), setup.serverKeyId,
    c⟩, ?_, ?_, ?_⟩
  · simp only [serverFields, acceptOfEq, candidateEq, keysEq, beaconId, registrationEq, sealEq, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, Option.some.injEq]
    rw [identity, serverInv.kid, ad]
  · simp only [beaconFields, ownerFound, publishedFull, ownerPhase, PqxdhDeploymentSessionFieldsInvariant.establishedAd,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq]
    rw [pinEq, keyEq, keysId]
    rfl
  · rw [consumed]
    exact List.mem_filterMap.mpr
      ⟨_, acceptEntry, by simpa [PqxdhDeploymentReplay.entryRegistration] using registrationEq⟩

end BeaconcryptCore.Computational.PqxdhDeploymentSessionFields

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFields.identityOf_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFields.identityOf_accepted

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFields.publishedKeys_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFields.publishedKeys_prefix

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFields.established_end' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFields.established_end

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFields.finish_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFields.finish_entry

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFields.pinned_agree_transcript' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFields.pinned_agree_transcript
