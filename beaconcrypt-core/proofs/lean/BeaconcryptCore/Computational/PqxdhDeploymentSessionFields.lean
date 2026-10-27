-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant
import BeaconcryptCore.Computational.PqxdhDeploymentReplay

/-!
# Ten of the eleven session fields, read from the experiment's final state (O21, part 2)

`Fields` is `PqxdhServerAuthRootSession.Session` without `root`, with ServerAuth's one-constructor `Position` replaced by the CE creation index. On a final state of `PqxdhDeploymentSecrecy.game`:

- `serverFields` is the Server's production for a session handle: the live Server object's identity and key ID; the accept bytes looked up by the handle (`PqxdhDeploymentTranscript.acceptOf`), the identity key, key tuple and initial key exchange of their verified candidate, and the registration ID read from them (`PqxdhDeploymentReplay.registrationOf`); the Beacon identity that the Server's reader takes from those bytes (`PqxdhDeploymentCompile.identityOf`); and the associated data of the handle's first logged seal context, the context the Server sealed with (`PqxdhDeploymentSessionFieldsInvariant.sealOf`).
- `beaconFields` is owner `c`'s acceptance: its native pin, identity key (from its identity seed) and pinned key ID, its stored 281-byte associated data, and the prekey, one-time and PQ keys of its first published bundle (the finish drops the secrets, as in Rust).
- `FieldsAgree c session`: both are defined and equal, and the registration ID is in the Server's consumed list.

The fields are read from each party's state and from the transcript. The Server-side Beacon identity, initial key exchange, registration ID and keys are public-reader decodings of the accept bytes in the transcript, and the Beacon-side initial key exchange, registration ID and keys combine its identity key with its first published bundle in the transcript; the equality of the keys is a conjunct of CE-A1's `PinnedMatchAt` itself. The state-level content beyond CE-A1's matching is the equality of the associated data of the Server's first logged seal context with the Beacon's stored one, of the Beacon's pinned key ID with the Server's key ID, and of the accepted identity key with the owner's identity-seed key, and the Server's consumption of the registration ID.

`pinned_agree` (identity index 0, generated seed): on every outcome, a session that pin-matches an accepted owner pinned to the protected binding (CE-A1's `PqxdhDeploymentServerAuth.PinnedMatchAt`) agrees with it on the ten fields. Ingredients: the run invariants of `PqxdhDeploymentSessionFieldsInvariant` (`inv_game`), positional session handles (`PqxdhDeploymentHeadlineGap.accept_positional`), `PqxdhDeploymentServerAuthInjectiveGame.keys_identity`, `PqxdhDeploymentEligibility.agree_game` and `PqxdhDeploymentReplay.replay_game`; premises: the approved Phase 1 and Phase 2 read-back contracts. `established_end`: an accepted owner is established at the end. `identityOf_accepted` and `publishedKeys_prefix` are the two public-reader facts used.

The root is not among the fields. The experiment retains no labelled Beacon root: the Server's session roots are in its touch log, the Extract entry from which the Beacon's root is expanded sits unlabelled in the shared HMAC cache, and the Beacon's evolving ratchet kernel is derived from that root, but no field of the outcome is the Beacon's root, so root equality is not a readout of the outcome. The payload and the assigned key ID are not among the eleven ServerAuth fields and are not stated.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentSessionFields
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentInterface (FreshBounds ModeSpec Mode Entry)
open PqxdhDeploymentServerAuthEvent (Reg regsOf accepted summarizeReg protectedBinding publishedKeys)
open PqxdhDeploymentServerAuth (PinnedMatchAt)
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

/-- The deterministic core at identity index 0: a session that pin-matches an accepted owner pinned to the protected binding agrees with it on the ten fields read from the experiment's final state, and the Server consumed its registration ID. The accept is looked up by the session handle (`PqxdhDeploymentHeadlineGap.accept_positional`), the Server's seal context by the handle in its ghost seal log (`ServerInv.sealed`), and the owner's identity key, pin, pinned key ID and stored associated data in its native state (`PqxdhDeploymentServerAuthInjectiveGame.keys_identity`, `PqxdhDeploymentEligibility.Agree`, `BeaconInv`); the consumed registration IDs are the transcript's (`PqxdhDeploymentReplay.replay_game`). Premises: the approved Phase 1 and Phase 2 read-back contracts. -/
theorem pinned_agree (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
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
    (pinned : PinnedMatchAt setup.source.crypto codec c session (protectedBinding setup created).1 before raw) :
    FieldsAgree setup codec final c session := by
  obtain ⟨identity, serverInv, beaconInv⟩ := PqxdhDeploymentSessionFieldsInvariant.inv_game setup codec checks route
    ensureInit 0 bounds mode adversary runtime outcome supported created output final reached
  have agree := PqxdhDeploymentEligibility.agree_game setup codec checks route ensureInit 0 bounds mode adversary
    runtime outcome supported created output final reached
  obtain ⟨acceptRaw, candidate, keys, payload, reply, _, acceptMember, candidateEq, keysEq, publishedEq, buildMember,
    _, _, _⟩ := pinned
  have prefixed := PqxdhDeploymentServerAuthEvent.accepted_prefix c _ before raw found
  have acceptEntry := PqxdhDeploymentHeadlineGap.accept_entry final.1.transcript acceptRaw (some session)
    (prefixed.subset acceptMember)
  have buildEntry := PqxdhDeploymentServerAuth.build_entry final.1.transcript session payload reply
    (prefixed.subset buildMember)
  obtain ⟨_, acceptOfEq⟩ := PqxdhDeploymentHeadlineGap.accept_positional setup codec checks route ensureInit phase1
    phase2 bounds mode adversary runtime outcome supported created output final reached acceptRaw session acceptEntry
  have beaconId := identityOf_accepted setup.source.crypto codec acceptRaw candidate keys candidateEq keysEq
  have registrationEq : PqxdhDeploymentReplay.registrationOf setup.source.crypto codec acceptRaw =
      some (keys.1.toList ++ keys.2.oneTime.toList) := by
    simp [PqxdhDeploymentReplay.registrationOf, candidateEq, keysEq]
  obtain ⟨sealRaw, beacon, context, sealAccept, sealIdentity, sealEq, ad⟩ :=
    serverInv.sealed session payload reply buildEntry
  obtain ⟨_, sealAcceptOf⟩ := PqxdhDeploymentHeadlineGap.accept_positional setup codec checks route ensureInit phase1
    phase2 bounds mode adversary runtime outcome supported created output final reached sealRaw session sealAccept
  rw [acceptOfEq, Option.some.injEq] at sealAcceptOf
  rw [← sealAcceptOf, beaconId, Option.some.injEq] at sealIdentity
  obtain ⟨owner, control, associatedData, kernel, ownerFound, ownerPhase⟩ := beaconInv.accepts c before raw found
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
  have adEq := beaconInv.installed c owner control associatedData kernel ownerFound ownerPhase
  rw [ownerPhase] at keyEq
  have consumed := (PqxdhDeploymentReplay.replay_game setup codec checks route ensureInit 0 bounds mode adversary
    runtime outcome supported created output final reached (keys.1.toList ++ keys.2.oneTime.toList)).2
  refine ⟨⟨(protectedBinding setup created).1, PqxdhRootTableInitialization.rootArray keys.1,
    PqxdhServerAuthPhase1Projection.unsigned keys.1 keys.2, keys.1.toList ++ keys.2.oneTime.toList, keys.2.prekey,
    keys.2.oneTime, keys.2.pqKey,
    Pqxdh.assocData (PqxdhRefinement.absBytes (protectedBinding setup created).1)
      (PqxdhRefinement.absBytes (PqxdhRootTableInitialization.rootArray keys.1)), setup.serverKeyId, c⟩, ?_, ?_, ?_⟩
  · simp only [serverFields, acceptOfEq, candidateEq, keysEq, beaconId, registrationEq, sealEq, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, Option.some.injEq]
    rw [identity, serverInv.kid, ad, sealIdentity]
  · simp only [beaconFields, ownerFound, publishedFull, ownerPhase, establishedAd, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, Option.some.injEq]
    rw [adEq, pinEq, keyEq, keysId]
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

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFields.pinned_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFields.pinned_agree
