-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineOrigin
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineUks
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineApp
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineKeyTransfer

/-!
# Symbolic corollaries of the CE-12 headlines (CE-12 P2, design-v2 sections 7.2, 7.3, 7.6; F-ct2 form)

The designation-free symbolic events of the CE-12 headlines and their corollaries: the headline events with the public designation replaced by symbolic eligibility (`PqxdhDeploymentHeadlineGap.SymServer`, `SymBeacon`, here `SymHandle`) and the CE counterpart replaced by identity-based symbolic counterpart sets, which are handle-level readings of the ProVerif conclusions. All events are read on the experiment's outcome (final transcript, final native identity keys, constructed Server).

- Counterpart sets (design-v2 section 7.2): `SymCpartB2s` (b2s, L2Published's `B`: the owners whose first published bundle carries the identity field of the accepted candidate of the session that built the peer) and `SymCpartS2b` (s2b, S2b-origin's "installed for `B`": the Server peers built by a session whose accepted candidate verifies to the owner's identity key).
- Events: `OriginFailureSym` (`ForgedAtSym`: an accepted raw receive on a symbolically eligible handle whose decoded frame no symbolic counterpart published before), `UksFailureSym` (`UksSenderSymAt`: an owner with `SymBeacon` returned a frame that a raw receive accepted on a handle outside its symbolic counterparts; the sender-eligible UKSr), `AppWinSym` and `AppWinPeerSym` (CE-APP's win on a symbolically eligible handle, on a Server peer), `KtSym` (an event whose claim is symbolically eligible).
- Containments on every outcome (design-v2 section 7.3): `origin_b2s_sym` (b2s: a CE b2s failure or a Server-side gap, no term, because a designated peer's CE counterpart is a symbolic counterpart, `peer_cpart_sym`); `origin_s2b_sym` and `uks_sym` (a CE event, a CE-A1 failure, a ciphertext gap or a ciphertext collision: the owner's pinned match is linked unless `CtGap`, and it is the designated session unless `CtColl`, so the CE counterpart is a symbolic counterpart, `owner_cpart_sym`, using positional sessions, `sessionAt_positional`); `app_sym`, `app_peer_sym`, `kt_sym` (a CE event or a gap).
- Corollaries in event form (`ce_or_b2s_sym_le`, `ce_or_s2b_sym_le`, `ce_uks_sym_le`, `ce_app_sym_le`, `ce_app_server_sym_le`, `ce_kt_sym_le`) and with the CE-12 bounds: `ce_or_b2s_sym` (CE-OR b2s's bound + `ε_A2pub`), `ce_or_s2b_sym` (CE-OR s2b's bound + `ε_A1` + `ctGapTerm` + `ctCollTerm`), `ce_uks_sym` (CE-UKS sender's bound + `ε_A1` + `ctGapTerm` + `ctCollTerm`), `ce_app_sym` (CE-APP's bound + `ε_A2pub + ε_A1` + `ctGapTerm`), `ce_app_server_sym` (CE-APP Server's bound + `ε_A2pub`), `ce_kt_sym` (CE-KT's one-sided bound + `ε_A2pub + ε_A1` + `ctGapTerm`).

Explicit terms: `ctGapTerm` is F-ct2's public ciphertext-gap term (the D-ct spike stopped, design-v2 section 8) and `ctCollTerm` is the public ciphertext-collision term, which design-v2 section 7.4 would bound by `ε_ctcoll` through a game-level step not proved here (`PqxdhDeploymentHeadlineCollision`). Not here: the injective CE-OR forms, `symbolic_lor`, the bills. The b2s publisher pin and the mode-O plaintext are not part of these events (design-v2 section 7.6). No new assumption or contract; the premises are those of the CE-12 headlines, of CE-A2pub and of CE-A1.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens observeGame)
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (Reg regsOf accepted publishedKeys keysOfBundle protectedBinding)
open PqxdhDeploymentServerAuth (PinnedMatchAt PinnedMatch A1NoPinnedMatch)
open PqxdhDeploymentPublishedTuple (ownerIdentities)
open PqxdhDeploymentHeadlineGap (SymServer SymBeacon CtGap ServerGap BeaconGap)
open PqxdhDeploymentHeadlineCollision (CarriesTo CtCollAt)
open PqxdhRecordLiftIdeal (receivingHandle PublishedBefore)
open PqxdhDeploymentHeadlineEvents (Direction)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-! ### Symbolic eligibility of a handle and the identity-based counterpart sets (design-v2 section 7.2) -/

section Definitions
variable (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)

/-- The symbolic eligibility of a record handle: a Server peer with `SymServer` (under the given owner identity keys), an owner with `SymBeacon` (under the given pin and key ID). -/
def SymHandle (transcript : List Entry) (identities : List PqxdhEd25519EufCma.Ed25519PublicKey)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (serverKid : Aeneas.Std.U64) : Handle → Prop
  | .peer keyId => SymServer crypto codec transcript identities keyId
  | .owner c => SymBeacon transcript pin serverKid c

/-- `symCpart_b2s` (design-v2 section 7.2, L2Published's `B`): the symbolic counterparts of Server peer `keyId` are the owners whose first published bundle carries the identity field of the accepted candidate of the session that built `keyId`. -/
def SymCpartB2s (transcript : List Entry) (keyId : Aeneas.Std.U64) (counterpart : Handle) : Prop :=
  ∃ k session response raw accepted published, counterpart = .owner k ∧ linkOf transcript keyId = some (session, response) ∧
    acceptOf transcript session = some raw ∧ candidateOf codec raw = some accepted ∧
    (bundleOf transcript k).bind (candidateOf codec) = some published ∧ published.identityKey = accepted.identityKey

/-- `symCpart_s2b` (design-v2 section 7.2, S2b-origin's "installed for `B`"): the symbolic counterparts of owner `c` are the Server peers built by a session whose accepted candidate verifies to owner `c`'s identity key (among the given owner identity keys). -/
def SymCpartS2b (transcript : List Entry) (identities : List PqxdhEd25519EufCma.Ed25519PublicKey) (c : Nat)
    (counterpart : Handle) : Prop :=
  ∃ keyId session payload response raw accepted identity keys, counterpart = .peer keyId ∧
    (⟨.inl (.inr (.build session payload)), some response⟩ : Entry) ∈ transcript ∧ response.keyId = keyId ∧
    acceptOf transcript session = some raw ∧ candidateOf codec raw = some accepted ∧
    acceptedKeys crypto accepted = some (identity, keys) ∧ identities[c]? = some identity

/-- The symbolic counterpart set of a receiving handle in a direction: `SymCpartB2s` for a Server peer (b2s), `SymCpartS2b` for an owner (s2b). -/
def SymCpart (transcript : List Entry) (identities : List PqxdhEd25519EufCma.Ed25519PublicKey) :
    Handle → Handle → Prop
  | .peer keyId => SymCpartB2s codec transcript keyId
  | .owner c => SymCpartS2b crypto codec transcript identities c

end Definitions

/-! ### Positional sessions and the designated owner's counterpart -/

section Counterpart
open PqxdhDeploymentKemTransfer (registrations)
open PqxdhDeploymentRegistrationTrace (acceptsOf)

/-- The replies of the raw accept attempts of a transcript are the replies of its logged raw accepts. -/
theorem acceptReplies_logged (transcript : List Entry) :
    PqxdhDeploymentIdealTrace.acceptReplies transcript = (acceptsOf (registrations transcript)).map Prod.snd := by
  unfold PqxdhDeploymentIdealTrace.acceptReplies registrations acceptsOf
  rw [List.filterMap_filterMap, List.map_filterMap]
  congr 1
  funext entry
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · rfl
  · cases command <;> rfl
  · rfl

set_option linter.deprecated false in
/-- Session handles are positional on every outcome of the experiment (identity index zero): a session handle that an accept returned is the session of the raw accept attempt of that ordinal (`PqxdhDeploymentIdealTrace.sessionAt`). -/
theorem sessionAt_positional (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X) (final : PqxdhDeploymentSecrecy.State KemSK)
    (found : outcome.1 = some (created, output, final)) (raw : Pqxdh.Bytes) (session : Nat)
    (accepted : (⟨.inl (.inr (.accept raw)), some session⟩ : Entry) ∈ final.1.transcript) :
    PqxdhDeploymentIdealTrace.sessionAt final.1.transcript session = some session := by
  have logged := PqxdhDeploymentHeadlineGap.accept_logged _ raw (some session) accepted
  have game := PqxdhDeploymentCompileSecrecy.compile_full_source setup codec checks route ensureInit phase1 phase2 bounds
    mode adversary ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)
  change _ = (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime at game
  have traced := PqxdhDeploymentRegistrationTrace.source_map setup codec checks ensureInit none Prod.fst
    (PqxdhDeploymentRegistrationTrace.traceFrom (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode
      adversary) []) ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)
  rw [PqxdhDeploymentRegistrationTrace.traceFrom_erase] at traced
  rw [← game, traced, Functor.map_map, support_map] at member
  obtain ⟨⟨_ | source, after⟩, sourceMember, rfl⟩ := member
  · simp [PqxdhDeploymentCompileSecrecy.mergeFull] at found
  · simp only [PqxdhDeploymentCompileSecrecy.mergeFull, Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨_, _, rfl⟩ := found
    have result := PqxdhDeploymentRegistrationTrace.source_support setup codec checks ensureInit none _ _ _ source
      sourceMember
    have logEq := PqxdhDeploymentKemTransfer.compiled_trace setup codec route bounds mode adversary source.2.1 result
    obtain ⟨tracedState, _⟩ := PqxdhDeploymentRegistrationTrace.traced_source setup codec checks ensureInit none _ _ rfl
      after source sourceMember
    simp only [PqxdhRegistrationJointInitializedSchedule.eraseOutcome] at logged ⊢
    rw [← logEq] at logged
    obtain ⟨position, positionFound⟩ := List.mem_iff_getElem?.mp logged
    have samePosition := tracedState.positional position raw session positionFound
    unfold PqxdhDeploymentIdealTrace.sessionAt
    rw [← samePosition] at positionFound
    rw [acceptReplies_logged, ← logEq, List.getElem?_map, positionFound]
    rfl

set_option linter.deprecated false in
/-- The CE counterpart of a designated, symbolically eligible owner is one of its symbolic counterparts, unless CE-A1 fails at the owner, the owner has a ciphertext gap, or two sessions carry one ciphertext to an owner's published PQ key (design-v2 section 7.3). The owner's pinned match `j` (else `A1NoPinnedMatch`) is linked (else `CtGap`), so the designated session, the smallest linked one, is `j` (else `CtColl`); `j`'s accepted keys are the owner's published keys, identity included, and session handles are positional, so the counterpart, the Server peer `j` built, is a symbolic counterpart. -/
theorem owner_cpart_sym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X) (final : PqxdhDeploymentSecrecy.State KemSK)
    (found : outcome.1 = some (created, output, final)) (c : Nat) (g : Fin budget.accept × Fin budget.capacity)
    (sym : SymBeacon final.1.transcript (protectedBinding setup created).1 setup.serverKeyId c)
    (designated : designateIn setup.source.crypto codec setup.serverKeyId budget final.1.transcript (.owner c) = some g)
    (noA1 : ¬A1NoPinnedMatch setup codec c outcome)
    (noGap : ∀ j, ¬CtGap setup.source.crypto codec final.1.transcript c j)
    (noColl : ∀ k i j, ¬CtCollAt setup.source.crypto codec final.1.transcript k i j) :
    ∃ counterpart, PqxdhDeploymentHeadlineEvents.cpart budget g final.1.transcript (.owner c) = some counterpart ∧
      SymCpartS2b setup.source.crypto codec final.1.transcript (ownerIdentities setup final.2.native) c counterpart := by
  obtain ⟨established, binding, clean⟩ := sym
  have unbudgeted := PqxdhDeploymentKemTransfer.designateIn_some _ codec _ budget _ _ g designated
  obtain ⟨same, _, pin, raw, ciphertext, published, pqKey, bindingFound, finished, ciphertextFound, publishedFound,
    pqKeyFound, _, linked⟩ :=
    PqxdhDeploymentTranscript.designate_owner _ codec _ _ c g.1.val g.2.val unbudgeted
  rw [binding, Option.some.injEq, Prod.mk.injEq] at bindingFound
  obtain ⟨pinEq, _⟩ := bindingFound
  subst pinEq
  have ready := PqxdhDeploymentHeadlineGap.ready_game setup codec checks route ensureInit 0 bounds mode adversary runtime
    outcome member created output final found
  obtain ⟨before, raw', acceptedFound⟩ := PqxdhDeploymentHeadlineGap.established_accepted c (regsOf final.1.transcript)
    (by rw [← PqxdhDeploymentServerAuthEvent.summarize_regs]; exact established)
  obtain ⟨finished', owners⟩ := PqxdhDeploymentHeadlineGap.ready_accepted final.1.transcript ready c before raw'
    acceptedFound
  rw [finished, Option.some.injEq] at finished'
  subst finished'
  have bindingBefore := owners _ binding
  have prefixed := PqxdhDeploymentServerAuthEvent.accepted_prefix c _ before raw acceptedFound
  have pinned : PinnedMatch setup.source.crypto codec c (protectedBinding setup created).1 before raw := by
    by_contra unpinned
    exact noA1 ⟨created, output, final, found, clean, before, raw, acceptedFound, bindingBefore, unpinned⟩
  obtain ⟨j, pinAt⟩ := pinned
  have sameCt : PqxdhDeploymentHeadlineGap.ciphertextOf codec (finishOf final.1.transcript c) =
      PqxdhDeploymentHeadlineGap.ciphertextOf codec ((buildOf final.1.transcript j).map (·.serialized)) := by
    by_contra different
    exact noGap j ⟨before, raw, _, acceptedFound, binding, pinAt, different⟩
  obtain ⟨acceptRaw, candidate, keys, payload, reply, _, acceptMember, candidateFound, keysFound, publishedKeysFound,
    buildMember, _, _, _⟩ := pinAt
  have agree := PqxdhDeploymentEligibility.agree_game setup codec checks route ensureInit 0 bounds mode adversary
    runtime outcome member created output final found
  have buildEntry := PqxdhDeploymentServerAuth.build_entry final.1.transcript j payload reply
    (prefixed.subset buildMember)
  have buildSome : (buildOf final.1.transcript j).isSome := by
    unfold buildOf
    rw [List.findSome?_isSome_iff]
    exact ⟨_, buildEntry, by simp⟩
  obtain ⟨response, responseFound⟩ := Option.isSome_iff_exists.mp buildSome
  obtain ⟨responsePayload, responseMember⟩ := PqxdhDeploymentKeyMatch.buildOf_mem _ j response responseFound
  obtain ⟨fields, written, _⟩ := id (agree.builds _ responseMember)
  obtain ⟨read, readFound, ciphertextRead, _, _, _, _⟩ := phase2 fields _ written
  have pinFound := PqxdhDeploymentServerAuth.build_pin setup codec checks route ensureInit 0 phase2 bounds mode
    adversary runtime outcome member created output final found j responsePayload response responseMember
  have ciphertextEq : fields.kemCiphertext = ciphertext := by
    have := sameCt
    simp only [PqxdhDeploymentHeadlineGap.ciphertextOf, finished, responseFound, Option.map_some, Option.bind_some,
      readFound, ciphertextRead] at this
    rw [ciphertextFound] at this
    exact (Option.some.inj this).symm
  subst ciphertextEq
  have acceptEntry := PqxdhDeploymentHeadlineGap.accept_entry _ acceptRaw (some j) (prefixed.subset acceptMember)
  obtain ⟨sessionBound, acceptFound⟩ := PqxdhDeploymentHeadlineGap.accept_positional setup codec checks route ensureInit
    phase1 phase2 bounds mode adversary runtime outcome member created output final found acceptRaw j acceptEntry
  have identityFound := PqxdhDeploymentServerAuthInjectiveGame.keys_identity setup codec phase1 _ _ _ agree before
    prefixed c keys publishedKeysFound
  unfold publishedKeys keysOfBundle at publishedKeysFound
  obtain ⟨bytes, bytesFound, publishedRest⟩ := Option.bind_eq_some_iff.mp publishedKeysFound
  obtain ⟨published', candidateRead, publishedRest⟩ := Option.bind_eq_some_iff.mp publishedRest
  obtain ⟨identityKey, _, publishedRest⟩ := Option.bind_eq_some_iff.mp publishedRest
  obtain ⟨tuple, tupleFound, publishedRest⟩ := Option.bind_eq_some_iff.mp publishedRest
  simp only [Option.pure_def, Option.some.injEq] at publishedRest
  have bundleFound : bundleOf final.1.transcript c = some bytes := by
    rw [← PqxdhDeploymentServerAuthInjectiveGame.bundleOfReg_regsOf]
    exact PqxdhDeploymentServerAuthInjectiveGame.bundleOfReg_prefix _ _ prefixed c bytes bytesFound
  rw [bundleFound, Option.bind_some, candidateRead, Option.some.injEq] at publishedFound
  subst publishedFound
  have pqEq : tuple.pqKey = pqKey := by
    rw [PqxdhDeploymentHeadlineGap.candidateTuple_pq _ tuple tupleFound, Option.some.injEq] at pqKeyFound
    exact pqKeyFound
  have carriesJ : CarriesTo setup.source.crypto codec final.1.transcript fields.kemCiphertext pqKey j :=
    ⟨response, candidate, keys, responseFound, by rw [readFound, Option.bind_some, ciphertextRead],
      by rw [acceptFound, Option.bind_some, candidateFound], keysFound, by rw [← publishedRest, pqEq]⟩
  have linkedJ : Linked setup.source.crypto codec final.1.transcript fields.kemCiphertext
      (protectedBinding setup created).1 pqKey j :=
    ⟨response, candidate, keys, responseFound, by rw [readFound, Option.bind_some, ciphertextRead], pinFound,
      by rw [acceptFound, Option.bind_some, candidateFound], keysFound, by rw [← publishedRest, pqEq]⟩
  obtain ⟨first, firstLe, firstDesignated⟩ := PqxdhDeploymentTranscript.designate_owner_complete setup.source.crypto
    codec setup.serverKeyId final.1.transcript c (protectedBinding setup created).1 raw fields.kemCiphertext published'
    pqKey j established binding finished ciphertextFound (by rw [bundleFound, Option.bind_some, candidateRead])
    pqKeyFound sessionBound linkedJ
  rw [unbudgeted, Option.some.injEq, Prod.mk.injEq] at firstDesignated
  have sessionEq : g.1.val = j := by
    by_contra different
    have below : g.1.val < j := lt_of_le_of_ne (firstDesignated.1 ▸ firstLe) different
    obtain ⟨linkedResponse, linkedAccepted, linkedKeys, linkedFound, linkedCt, _, linkedAccept, linkedKeysFound,
      linkedPq⟩ := linked
    exact noColl c g.1.val j ⟨below, fields.kemCiphertext, published', pqKey,
      by rw [bundleFound, Option.bind_some, candidateRead], pqKeyFound,
      ⟨linkedResponse, linkedAccepted, linkedKeys, linkedFound, linkedCt, linkedAccept, linkedKeysFound, linkedPq⟩,
      carriesJ⟩
  have sessionAtFound := sessionAt_positional setup codec checks route ensureInit phase1 phase2 bounds mode adversary
    runtime outcome member created output final found acceptRaw j acceptEntry
  refine ⟨.peer response.keyId, ?_, ?_⟩
  · simp only [PqxdhDeploymentHeadlineEvents.cpart, PqxdhDeploymentIdealTrace.peerOf,
      PqxdhDeploymentIdealParams.Target.ofCE, sessionEq, sessionAtFound, Option.bind_some, responseFound,
      Option.map_some]
  · obtain ⟨entry, entryFound, entryKey⟩ := identityFound
    refine ⟨response.keyId, j, responsePayload, response, acceptRaw, candidate, keys.1, keys.2, rfl, responseMember, rfl,
      acceptFound, candidateFound, keysFound, ?_⟩
    simp [ownerIdentities, entryFound, entryKey]

end Counterpart

/-! ### Designation-free symbolic origin events (design-v2 sections 7.2-7.3) -/

section OriginEvents
variable (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- `ForgedAtSym` (design-v2 section 7.2): the entry, with prefix `before` in the final transcript, is an accepted raw receive in the direction on a symbolically eligible handle, whose decoded frame none of the handle's symbolic counterparts published before. It is `PqxdhDeploymentHeadlineEvents.ForgedAtCE` with designation replaced by `SymHandle` and the CE counterpart by the identity-based counterpart set `SymCpart`. -/
def ForgedAtSym (direction : Direction) (transcript : List Entry) (identities : List PqxdhEd25519EufCma.Ed25519PublicKey)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (serverKid : Aeneas.Std.U64) (before : List Entry) (entry : Entry) :
    Prop :=
  ∃ receiver raw decrypted handle frame, entry.received = some (receiver, raw, .Some decrypted) ∧
    receivingHandle route receiver raw = some handle ∧ direction.Receives handle ∧
    SymHandle crypto codec transcript identities pin serverKid handle ∧ codec.frameRead raw = some frame ∧
    ∀ counterpart, SymCpart crypto codec transcript identities handle counterpart →
      ¬PublishedBefore codec before counterpart frame

end OriginEvents

/-- `OriginFailureSym` (design-v2 section 7.2): a Server was constructed and some entry of the final transcript is a symbolic origin failure in the direction, with the final native identity keys, the constructed Server's identity as pin and the protected key ID. -/
def OriginFailureSym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (direction : Direction)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧ ∃ before entry after,
    final.1.transcript = before ++ entry :: after ∧
    ForgedAtSym setup.source.crypto codec route direction final.1.transcript (ownerIdentities setup final.2.native)
      (protectedBinding setup created).1 setup.serverKeyId before entry

open Classical in
/-- `OriginFailureSym` as a Boolean of the outcome. -/
noncomputable def originSym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (direction : Direction)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Bool :=
  decide (OriginFailureSym setup codec route direction outcome)

/-- A designated Server peer's CE counterpart is one of its symbolic counterparts: owner `k` of the designation publishes the accepted identity field (`Publishes`). -/
theorem peer_cpart_sym (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64)
    (budget : Budget) (transcript : List Entry) (keyId : Aeneas.Std.U64) (g : Fin budget.accept × Fin budget.capacity)
    (designated : designateIn crypto codec serverKid budget transcript (.peer keyId) = some g) :
    SymCpartB2s codec transcript keyId (.owner g.2.val) := by
  have unbudgeted := PqxdhDeploymentKemTransfer.designateIn_some _ codec _ budget _ _ g designated
  obtain ⟨response, raw, accepted, keys, linked, rawFound, acceptedFound, _, _, published, publishedFound, identityEq,
    _⟩ := PqxdhDeploymentTranscript.designate_peer crypto codec serverKid keyId transcript g.1.val g.2.val unbudgeted
  exact ⟨g.2.val, g.1.val, response, raw, accepted, published, rfl, linked, rawFound, acceptedFound, publishedFound,
    identityEq⟩

/-- The b2s containment (design-v2 section 7.3): on every outcome, a symbolic b2s origin failure is a CE b2s origin failure or a Server-side gap. A designated peer's CE counterpart is a symbolic counterpart (`peer_cpart_sym`), so no frame publication is lost and no term is needed. -/
theorem origin_b2s_sym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (budget : Budget)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (holds : OriginFailureSym setup codec route .b2s outcome) :
    happens (PqxdhDeploymentHeadlineEvents.originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
        outcome = true ∨
      ServerGap setup codec budget outcome := by
  classical
  obtain ⟨created, output, final, found, before, entry, after, split, receiver, raw, decrypted, handle, frame, received,
    routed, receives, sym, framed, unpublished⟩ := holds
  cases handle with
  | owner c => exact absurd receives id
  | peer keyId =>
      cases designatedFound : designateIn setup.source.crypto codec setup.serverKeyId budget final.1.transcript
          (.peer keyId) with
      | none => exact Or.inr ⟨created, output, final, found, keyId, sym, designatedFound⟩
      | some g =>
          left
          simp only [happens, observeGame, found, Option.map_some, Option.any_some,
            PqxdhDeploymentHeadlineEvents.originEvent, decide_eq_true_eq]
          refine ⟨before, entry, after, split, g, receiver, raw, decrypted, .peer keyId, frame, received, routed, receives,
            designatedFound, framed, fun counterpart named => ?_⟩
          simp only [PqxdhDeploymentHeadlineEvents.cpart, Option.some.injEq] at named
          subst named
          exact unpublished _ (peer_cpart_sym _ codec _ budget _ keyId g designatedFound)

set_option linter.deprecated false in
/-- The s2b containment (design-v2 section 7.3): on every outcome of the experiment of a budget-respecting adversary, a symbolic s2b origin failure is a CE s2b origin failure, a CE-A1 failure, a ciphertext gap or a ciphertext collision. An undesignated owner is CE-A1's or a gap's (`beacon_gap`); a designated owner's CE counterpart is a symbolic counterpart unless one of those holds (`owner_cpart_sym`). Premises: the approved Phase 1 and Phase 2 read-back contracts and the budget. -/
theorem origin_s2b_sym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime))
    (holds : OriginFailureSym setup codec route .s2b outcome) :
    happens (PqxdhDeploymentHeadlineEvents.originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        outcome = true ∨
      (∃ c, A1NoPinnedMatch setup codec c outcome) ∨
      happens (PqxdhDeploymentHeadlineGap.ctGapEvent setup.source.crypto codec) outcome = true ∨
      happens (PqxdhDeploymentHeadlineCollision.ctCollEvent setup.source.crypto codec) outcome = true := by
  classical
  obtain ⟨created, output, final, found, before, entry, after, split, receiver, raw, decrypted, handle, frame, received,
    routed, receives, sym, framed, unpublished⟩ := holds
  have observed : observeGame outcome.1 = some (output, final.1, final.2.produced) := by
    rw [found]
    rfl
  cases handle with
  | peer keyId => exact absurd receives id
  | owner c =>
      by_cases a1 : A1NoPinnedMatch setup codec c outcome
      · exact Or.inr (Or.inl ⟨c, a1⟩)
      by_cases gap : ∃ j, CtGap setup.source.crypto codec final.1.transcript c j
      · obtain ⟨j, gapAt⟩ := gap
        refine Or.inr (Or.inr (Or.inl ?_))
        simp only [happens, observed, Option.any_some, PqxdhDeploymentHeadlineGap.ctGapEvent, decide_eq_true_eq]
        exact ⟨c, j, gapAt⟩
      by_cases coll : ∃ k i j, CtCollAt setup.source.crypto codec final.1.transcript k i j
      · refine Or.inr (Or.inr (Or.inr ?_))
        simp only [happens, observed, Option.any_some, PqxdhDeploymentHeadlineCollision.ctCollEvent,
          decide_eq_true_eq]
        exact coll
      left
      cases designatedFound : designateIn setup.source.crypto codec setup.serverKeyId budget final.1.transcript
          (.owner c) with
      | none =>
          rcases PqxdhDeploymentHeadlineGap.beacon_gap setup codec checks route ensureInit phase1 phase2 bounds mode
            adversary budget respects runtime outcome member created output final found c sym designatedFound with
            failure | ⟨j, gapAt⟩
          · exact absurd failure a1
          · exact absurd ⟨j, gapAt⟩ gap
      | some g =>
          obtain ⟨counterpart, named, symbolic⟩ := owner_cpart_sym setup codec checks route ensureInit phase1 phase2
            bounds mode adversary budget runtime outcome member created output final found c g sym designatedFound a1
            (fun j gapAt => gap ⟨j, gapAt⟩) (fun k i j collAt => coll ⟨k, i, j, collAt⟩)
          simp only [happens, observed, Option.any_some, PqxdhDeploymentHeadlineEvents.originEvent, decide_eq_true_eq]
          refine ⟨before, entry, after, split, g, receiver, raw, decrypted, .owner c, frame, received, routed, receives,
            designatedFound, framed, fun counterpart' named' => ?_⟩
          rw [named, Option.some.injEq] at named'
          subst named'
          exact unpublished _ symbolic

/-! ### Symbolic UKS (sender-eligible), APP and KT events (design-v2 sections 7.2-7.3) -/

section OtherEvents
variable (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- `UksSenderSymAt` (design-v2 section 7.2, UKSr sender-eligible): the entry returned, on an owner with `SymBeacon`, a record whose decoded frame some raw receive of the final transcript accepted on a handle that is not one of the owner's symbolic counterparts (in particular any handle that is not a Server peer). It is `PqxdhDeploymentHeadlineEvents.UksSenderAt` with designation replaced by `SymBeacon` and the CE partner by `SymCpartS2b`. -/
def UksSenderSymAt (transcript : List Entry) (identities : List PqxdhEd25519EufCma.Ed25519PublicKey)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (serverKid : Aeneas.Std.U64) (entry : Entry) : Prop :=
  ∃ c encrypted frame, entry.published = some (.owner c, encrypted) ∧ codec.frameRead encrypted.ciphertext = some frame ∧
    SymBeacon transcript pin serverKid c ∧
    ∃ other ∈ transcript, ∃ receiver raw decrypted receiving, other.received = some (receiver, raw, .Some decrypted) ∧
      receivingHandle route receiver raw = some receiving ∧ codec.frameRead raw = some frame ∧
      ¬SymCpartS2b crypto codec transcript identities c receiving

end OtherEvents

/-- `UksFailureSym` (design-v2 section 7.2): a Server was constructed and some entry of the final transcript is a sender-eligible symbolic UKS witness. -/
def UksFailureSym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧ ∃ entry ∈ final.1.transcript,
    UksSenderSymAt setup.source.crypto codec route final.1.transcript (ownerIdentities setup final.2.native)
      (protectedBinding setup created).1 setup.serverKeyId entry

open Classical in
/-- `UksFailureSym` as a Boolean of the outcome. -/
noncomputable def uksSym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Bool :=
  decide (UksFailureSym setup codec route outcome)

/-- `AppWinSym` (design-v2 section 7.2): a Server was constructed, the adversary's output claims index `i` and guess `m`, the `i`-th admitted fresh message was sent on a symbolically eligible handle, and it equals the guess. -/
def AppWinSym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (appClaim : X → Option (Nat × Pqxdh.Bytes))
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧ ∃ index guess entry,
    appClaim output = some (index, guess) ∧ final.1.fresh[index]? = some entry ∧
    SymHandle setup.source.crypto codec final.1.transcript (ownerIdentities setup final.2.native)
      (protectedBinding setup created).1 setup.serverKeyId entry.handle ∧ entry.message = guess

/-- `AppWinSym` on a Server peer (the symbolic form of `ce_app_server`'s event). -/
def AppWinPeerSym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (appClaim : X → Option (Nat × Pqxdh.Bytes))
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧ ∃ index guess entry keyId,
    appClaim output = some (index, guess) ∧ final.1.fresh[index]? = some entry ∧ entry.handle = .peer keyId ∧
    SymServer setup.source.crypto codec final.1.transcript (ownerIdentities setup final.2.native) keyId ∧
    entry.message = guess

open Classical in
/-- `AppWinSym` as a Boolean of the outcome. -/
noncomputable def appSym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (appClaim : X → Option (Nat × Pqxdh.Bytes))
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Bool :=
  decide (AppWinSym setup codec appClaim outcome)

open Classical in
/-- `AppWinPeerSym` as a Boolean of the outcome. -/
noncomputable def appPeerSym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (appClaim : X → Option (Nat × Pqxdh.Bytes))
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Bool :=
  decide (AppWinPeerSym setup codec appClaim outcome)

/-- `E ∧ Sym(claim)` (design-v2 section 7.2, the symbolic form of CE-KT's event): the event holds and the claim names a symbolically eligible handle. -/
def KtSym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (event : Observed X → Bool)
    (claim : Observed X → Option Handle)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Prop :=
  happens event outcome = true ∧ ∃ created output final, outcome.1 = some (created, output, final) ∧ ∃ handle,
    claim (output, final.1, final.2.produced) = some handle ∧
    SymHandle setup.source.crypto codec final.1.transcript (ownerIdentities setup final.2.native)
      (protectedBinding setup created).1 setup.serverKeyId handle

open Classical in
/-- `KtSym` as a Boolean of the outcome. -/
noncomputable def ktSym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (event : Observed X → Bool)
    (claim : Observed X → Option Handle)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Bool :=
  decide (KtSym setup codec event claim outcome)

/-- An undesignated symbolically eligible handle is a Server-side or Beacon-side gap. -/
theorem undesignated_gap (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (found : outcome.1 = some (created, output, final)) (handle : Handle)
    (sym : SymHandle setup.source.crypto codec final.1.transcript (ownerIdentities setup final.2.native)
      (protectedBinding setup created).1 setup.serverKeyId handle)
    (undesignated : designateIn setup.source.crypto codec setup.serverKeyId budget final.1.transcript handle = none) :
    ServerGap setup codec budget outcome ∨ BeaconGap setup codec budget outcome := by
  cases handle with
  | peer keyId => exact Or.inl ⟨created, output, final, found, keyId, sym, undesignated⟩
  | owner c => exact Or.inr ⟨created, output, final, found, c, sym, undesignated⟩

set_option linter.deprecated false in
/-- The UKS containment (design-v2 section 7.3): on every outcome of the experiment of a budget-respecting adversary, a sender-eligible symbolic UKS witness is a CE sender-side UKS witness, a CE-A1 failure, a ciphertext gap or a ciphertext collision (`beacon_gap`, `owner_cpart_sym`: the owner's CE partner is a symbolic counterpart, so a receiver outside the symbolic counterparts is not the CE partner). Premises: the approved Phase 1 and Phase 2 read-back contracts and the budget. -/
theorem uks_sym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime))
    (holds : UksFailureSym setup codec route outcome) :
    happens (PqxdhDeploymentHeadlineEvents.uksSenderEvent setup.source.crypto codec setup.serverKeyId budget route)
        outcome = true ∨
      (∃ c, A1NoPinnedMatch setup codec c outcome) ∨
      happens (PqxdhDeploymentHeadlineGap.ctGapEvent setup.source.crypto codec) outcome = true ∨
      happens (PqxdhDeploymentHeadlineCollision.ctCollEvent setup.source.crypto codec) outcome = true := by
  classical
  obtain ⟨created, output, final, found, entry, entryMember, c, encrypted, frame, published, framed, sym, other,
    otherMember, receiver, raw, decrypted, receiving, received, routed, otherFramed, notSymbolic⟩ := holds
  have observed : observeGame outcome.1 = some (output, final.1, final.2.produced) := by
    rw [found]
    rfl
  by_cases a1 : A1NoPinnedMatch setup codec c outcome
  · exact Or.inr (Or.inl ⟨c, a1⟩)
  by_cases gap : ∃ j, CtGap setup.source.crypto codec final.1.transcript c j
  · obtain ⟨j, gapAt⟩ := gap
    refine Or.inr (Or.inr (Or.inl ?_))
    simp only [happens, observed, Option.any_some, PqxdhDeploymentHeadlineGap.ctGapEvent, decide_eq_true_eq]
    exact ⟨c, j, gapAt⟩
  by_cases coll : ∃ k i j, CtCollAt setup.source.crypto codec final.1.transcript k i j
  · refine Or.inr (Or.inr (Or.inr ?_))
    simp only [happens, observed, Option.any_some, PqxdhDeploymentHeadlineCollision.ctCollEvent, decide_eq_true_eq]
    exact coll
  left
  cases designatedFound : designateIn setup.source.crypto codec setup.serverKeyId budget final.1.transcript
      (.owner c) with
  | none =>
      rcases PqxdhDeploymentHeadlineGap.beacon_gap setup codec checks route ensureInit phase1 phase2 bounds mode adversary
        budget respects runtime outcome member created output final found c sym designatedFound with
        failure | ⟨j, gapAt⟩
      · exact absurd failure a1
      · exact absurd ⟨j, gapAt⟩ gap
  | some g =>
      obtain ⟨counterpart, named, symbolic⟩ := owner_cpart_sym setup codec checks route ensureInit phase1 phase2 bounds
        mode adversary budget runtime outcome member created output final found c g sym designatedFound a1
        (fun j gapAt => gap ⟨j, gapAt⟩) (fun k i j collAt => coll ⟨k, i, j, collAt⟩)
      simp only [happens, observed, Option.any_some, PqxdhDeploymentHeadlineEvents.uksSenderEvent, decide_eq_true_eq]
      refine ⟨entry, entryMember, g, c, encrypted, frame, published, framed, designatedFound, other, otherMember, receiver,
        raw, decrypted, receiving, received, routed, otherFramed, ?_⟩
      rintro (⟨_, impossible⟩ | ⟨_, partner⟩)
      · cases next : PqxdhDeploymentIdealTrace.peerOf (PqxdhDeploymentIdealParams.Target.ofCE budget g)
          final.1.transcript <;> simp [next] at impossible
      · simp only [PqxdhDeploymentHeadlineEvents.cpart] at named
        rw [named, Option.some.injEq] at partner
        subst partner
        exact notSymbolic symbolic

/-- The APP containment (design-v2 section 7.3): on every outcome, a symbolic APP win is a CE APP win or a gap. -/
theorem app_sym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)
    (appClaim : X → Option (Nat × Pqxdh.Bytes))
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (holds : AppWinSym setup codec appClaim outcome) :
    happens (PqxdhDeploymentHeadlineEvents.appEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
        outcome = true ∨
      ServerGap setup codec budget outcome ∨ BeaconGap setup codec budget outcome := by
  classical
  obtain ⟨created, output, final, found, index, guess, entry, claimed, freshFound, sym, message⟩ := holds
  cases designatedFound : designateIn setup.source.crypto codec setup.serverKeyId budget final.1.transcript entry.handle with
  | none =>
      exact Or.inr (undesignated_gap setup codec budget outcome created output final found entry.handle sym
        designatedFound)
  | some g =>
      left
      simp only [happens, observeGame, found, Option.map_some, Option.any_some,
        PqxdhDeploymentHeadlineEvents.appEvent, decide_eq_true_eq]
      exact ⟨index, guess, entry, claimed, freshFound, by rw [designatedFound]; rfl, message⟩

/-- The Server-side APP containment: on every outcome, a symbolic APP win on a Server peer is a CE Server-side APP win or a Server-side gap. -/
theorem app_peer_sym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)
    (appClaim : X → Option (Nat × Pqxdh.Bytes))
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (holds : AppWinPeerSym setup codec appClaim outcome) :
    happens (PqxdhDeploymentHeadlineEvents.appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
        outcome = true ∨
      ServerGap setup codec budget outcome := by
  classical
  obtain ⟨created, output, final, found, index, guess, entry, keyId, claimed, freshFound, handled, sym, message⟩ := holds
  cases designatedFound : designateIn setup.source.crypto codec setup.serverKeyId budget final.1.transcript
      (.peer keyId) with
  | none => exact Or.inr ⟨created, output, final, found, keyId, sym, designatedFound⟩
  | some g =>
      left
      simp only [happens, observeGame, found, Option.map_some, Option.any_some,
        PqxdhDeploymentHeadlineEvents.appPeerEvent, decide_eq_true_eq]
      exact ⟨index, guess, entry, keyId, claimed, freshFound, handled, by rw [handled, designatedFound]; rfl, message⟩

/-- The KT containment (design-v2 section 7.3): on every outcome, an event whose claim is symbolically eligible is the event with a designated claim (`PqxdhDeploymentTargetRange.eligible`) or a gap. -/
theorem kt_sym (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)
    (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (holds : KtSym setup codec event claim outcome) :
    (happens event outcome = true ∧
        (PqxdhDeploymentTargetRange.eligible setup.source.crypto codec setup.serverKeyId claim outcome).isSome) ∨
      ServerGap setup codec budget outcome ∨ BeaconGap setup codec budget outcome := by
  obtain ⟨happened, created, output, final, found, handle, claimed, sym⟩ := holds
  cases designatedFound : designate setup.source.crypto codec setup.serverKeyId final.1.transcript handle with
  | none =>
      refine Or.inr (undesignated_gap setup codec budget outcome created output final found handle sym ?_)
      simp [PqxdhDeploymentTranscript.designateIn, designatedFound]
  | some pair =>
      left
      refine ⟨happened, ?_⟩
      simp [PqxdhDeploymentTargetRange.eligible, observeGame, found, claimed, designatedFound]

/-! ### The symbolic corollaries (design-v2 section 7.3) -/

section Corollaries
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss recLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim uksSenderEvent uksSenderClaim appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm bindingTerm)

/-- The union bound over four Boolean events on the support. -/
theorem chance_le_add4 {α : Type} (run : ProbComp α) (first second third fourth fifth : α → Bool)
    (implies : ∀ a ∈ support run, first a = true →
      second a = true ∨ third a = true ∨ fourth a = true ∨ fifth a = true) :
    𝒟[first <$> run] {true} ≤
      𝒟[second <$> run] {true} + 𝒟[third <$> run] {true} + 𝒟[fourth <$> run] {true} + 𝒟[fifth <$> run] {true} := by
  refine (chance_le_add_support run first second (fun a => third a || fourth a || fifth a) fun a member held => ?_).trans
    ?_
  · rcases implies a member held with one | two | three | four
    · exact Or.inl one
    · exact Or.inr (by simp [two])
    · exact Or.inr (by simp [three])
    · exact Or.inr (by simp [four])
  · rw [add_assoc, add_assoc]
    refine add_le_add le_rfl ((chance_le_add_support run _ (fun a => third a || fourth a) fifth fun a _ held => by
      simp only [Bool.or_eq_true] at held ⊢
      exact held).trans ?_)
    rw [← add_assoc]
    exact add_le_add (chance_le_add_support run _ third fourth fun a _ held => by simpa using held) le_rfl

/-- The A1 event as a Boolean of the outcome. -/
theorem a1_chance (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(fun outcome => @decide (∃ c, A1NoPinnedMatch setup codec c outcome) (Classical.propDecidable _)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ENNReal.ofReal (a1Term setup codec checks caps route bounds mode adversary budget a1Fallback signatureFallback) := by
  have a1 := PqxdhDeploymentServerAuthBills.ce_a1_billed setup codec checks caps bounded route ensureInit 0 phase1 phase2
    frameBack writable law spread correct adapter bounds mode adversary budget respects runtime a1Fallback
    signatureFallback
  rw [← ENNReal.ofReal_toReal (UniformTargetSelection.chance_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal a1.1

/-- `ce_or_b2s_sym` in event form: the symbolic b2s origin failure is at most the CE b2s origin failure plus the Server-side gap (`origin_b2s_sym`). -/
theorem ce_or_b2s_sym_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (runtime : A) :
    𝒟[originSym setup codec route .b2s <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[(fun outcome => happens (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s) outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} +
      𝒟[serverGap setup codec budget <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} := by
  refine chance_le_add_support _ _ _ _ fun outcome _ held => ?_
  simp only [originSym, decide_eq_true_eq] at held
  rcases origin_b2s_sym setup codec route budget outcome held with ce | gap
  · exact Or.inl ce
  · right
    simp only [serverGap, decide_eq_true_eq]
    exact gap

/-- `ce_or_s2b_sym` in event form: the symbolic s2b origin failure is at most the CE s2b origin failure plus CE-A1's event plus the explicit ciphertext-gap and ciphertext-collision terms (`origin_s2b_sym`). Premises: the approved Phase 1 and Phase 2 read-back contracts and the budget. -/
theorem ce_or_s2b_sym_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A) :
    𝒟[originSym setup codec route .s2b <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[(fun outcome => happens (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b) outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} +
      𝒟[(fun outcome => @decide (∃ c, A1NoPinnedMatch setup codec c outcome) (Classical.propDecidable _)) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} +
      ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime +
      ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime := by
  refine chance_le_add4 _ _ _ _ _ _ fun outcome member held => ?_
  simp only [originSym, decide_eq_true_eq] at held
  rcases origin_s2b_sym setup codec checks route ensureInit phase1 phase2 bounds mode adversary budget respects runtime
    outcome member held with ce | a1 | gap | coll
  · exact Or.inl ce
  · exact Or.inr (Or.inl (by simpa using a1))
  · exact Or.inr (Or.inr (Or.inl gap))
  · exact Or.inr (Or.inr (Or.inr coll))

/-- `ce_uks_sym` in event form: the sender-eligible symbolic UKS failure is at most the CE sender-side UKS failure plus CE-A1's event plus the explicit ciphertext-gap and ciphertext-collision terms (`uks_sym`). Premises: the approved Phase 1 and Phase 2 read-back contracts and the budget. -/
theorem ce_uks_sym_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A) :
    𝒟[uksSym setup codec route <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[(fun outcome => happens (uksSenderEvent setup.source.crypto codec setup.serverKeyId budget route) outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} +
      𝒟[(fun outcome => @decide (∃ c, A1NoPinnedMatch setup codec c outcome) (Classical.propDecidable _)) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} +
      ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime +
      ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime := by
  refine chance_le_add4 _ _ _ _ _ _ fun outcome member held => ?_
  simp only [uksSym, decide_eq_true_eq] at held
  rcases uks_sym setup codec checks route ensureInit phase1 phase2 bounds mode adversary budget respects runtime
    outcome member held with ce | a1 | gap | coll
  · exact Or.inl ce
  · exact Or.inr (Or.inl (by simpa using a1))
  · exact Or.inr (Or.inr (Or.inl gap))
  · exact Or.inr (Or.inr (Or.inr coll))

/-- `ce_app_sym` in event form: the symbolic APP win is at most the CE APP win plus both gaps (`app_sym`). -/
theorem ce_app_sym_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (runtime : A)
    (appClaim : X → Option (Nat × Pqxdh.Bytes)) :
    𝒟[appSym setup codec appClaim <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[(fun outcome => happens (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} +
      𝒟[(fun outcome => serverGap setup codec budget outcome || beaconGap setup codec budget outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} := by
  refine chance_le_add_support _ _ _ _ fun outcome _ held => ?_
  simp only [appSym, decide_eq_true_eq] at held
  rcases app_sym setup codec budget appClaim outcome held with ce | gap | gap
  · exact Or.inl ce
  · right
    simp [serverGap, gap]
  · right
    simp [beaconGap, gap]

/-- `ce_app_server_sym` in event form: the symbolic APP win on a Server peer is at most the CE Server-side APP win plus the Server-side gap (`app_peer_sym`). -/
theorem ce_app_server_sym_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (runtime : A)
    (appClaim : X → Option (Nat × Pqxdh.Bytes)) :
    𝒟[appPeerSym setup codec appClaim <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[(fun outcome => happens (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} +
      𝒟[serverGap setup codec budget <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} := by
  refine chance_le_add_support _ _ _ _ fun outcome _ held => ?_
  simp only [appPeerSym, decide_eq_true_eq] at held
  rcases app_peer_sym setup codec budget appClaim outcome held with ce | gap
  · exact Or.inl ce
  · right
    simp [serverGap, gap]

/-- `ce_kt_sym` in event form: the event with a symbolically eligible claim is at most the event with a designated claim plus both gaps (`kt_sym`). -/
theorem ce_kt_sym_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (runtime : A)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) :
    𝒟[ktSym setup codec event claim <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[(fun outcome => decide (happens event outcome = true ∧
          (PqxdhDeploymentTargetRange.eligible setup.source.crypto codec setup.serverKeyId claim outcome).isSome)) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} +
      𝒟[(fun outcome => serverGap setup codec budget outcome || beaconGap setup codec budget outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} := by
  refine chance_le_add_support _ _ _ _ fun outcome _ held => ?_
  simp only [ktSym, decide_eq_true_eq] at held
  rcases kt_sym setup codec budget event claim outcome held with ce | gap | gap
  · left
    simpa using ce
  · right
    simp [serverGap, gap]
  · right
    simp [beaconGap, gap]

end Corollaries

/-! ### The symbolic corollaries with the CE-12 bounds -/

section Headlines
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss recLoss slotted serverSlotted inputG)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim uksSenderEvent uksSenderClaim appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap a2pubTerm a1Term ctGapTerm)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm bindingTerm)

/-- `ce_or_b2s_sym` (design-v2 section 7.3; VC rows L2-origin, b2s-C2, b2s-C2-chosen-fs, b2s-C4, far-b2s-C4 on symbolic eligibility): the probability that some accepted Server raw receive on a symbolically eligible peer (`SymServer`) carries a decoded frame that no symbolic counterpart (an owner whose first published bundle carries the accepted identity field) published before is at most CE-OR b2s's bound (`PqxdhDeploymentHeadlineOrigin.ce_or_b2s`) plus `ε_A2pub`. Premises: those of `ce_or_b2s` and of `server_gap_bound` (`shortRejects`). -/
theorem ce_or_b2s_sym (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    𝒟[originSym setup codec route .b2s <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
            (orClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
            (orClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) (g.1, g.2.castSucc) runtime) +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
            fallback caps qInit (serverSlotted setup codec budget
              (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
              (orClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) (g.1, g.2.castSucc)) +
          publicationTerm budget)) +
      a2pubTerm setup codec checks route ensureInit bounds mode adversary budget runtime identityFallback
        ordinaryFallback :=
  (ce_or_b2s_sym_le setup codec checks route ensureInit bounds mode adversary budget runtime).trans
    (add_le_add (PqxdhDeploymentHeadlineOrigin.ce_or_b2s setup functional codec checks route ensureInit phase1 phase2
      correct caps bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback)
      (PqxdhDeploymentHeadlineGap.server_gap_bound setup codec checks shortRejects route ensureInit phase1 phase2 bounds
        mode adversary budget respects runtime identityFallback ordinaryFallback))

/-- `ce_or_s2b_sym` (design-v2 section 7.3; VC rows S2b-origin, s2b-C1, s2b-C4, far-s2b-C4 on symbolic eligibility, positions from 2): the probability that some accepted Beacon raw receive on a symbolically eligible owner (`SymBeacon`, pinned to the constructed Server and the protected key ID) carries a decoded frame that no symbolic counterpart (a Server peer built by a session whose accepted candidate verifies to the owner's identity key) published before is at most CE-OR s2b's bound (`PqxdhDeploymentHeadlineOrigin.ce_or_s2b`) plus `ε_A1` plus the explicit public terms `ctGapTerm` (F-ct2) and `ctCollTerm`. Premises: those of `ce_or_s2b` and of CE-A1 (`ReadWritable`, `X25519ClassLaw`, `X25519ScalarSpread`, `HasAttachedVerificationAdapter`). -/
theorem ce_or_s2b_sym (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[originSym setup codec route .s2b <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
            (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
            (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
            fallback caps qInit (slotted setup codec budget
              (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
              (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc)) +
          publicationTerm budget)) +
      ENNReal.ofReal (a1Term setup codec checks caps route bounds mode adversary budget a1Fallback signatureFallback) +
      ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime +
      ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime :=
  (ce_or_s2b_sym_le setup codec checks route ensureInit phase1 phase2 bounds mode adversary budget respects
    runtime).trans (add_le_add (add_le_add (add_le_add
      (PqxdhDeploymentHeadlineOrigin.ce_or_s2b setup functional codec checks route ensureInit phase1 phase2 correct caps
        bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback)
      (a1_chance setup codec checks caps bounded route ensureInit phase1 phase2 frameReadBack writable law spread correct
        adapter bounds mode adversary budget respects runtime a1Fallback signatureFallback)) le_rfl) le_rfl)

/-- `ce_uks_sym` (design-v2 section 7.3; VC row b2s-UKSr on sender symbolic eligibility): the probability that some owner with `SymBeacon` returned a record whose decoded frame a raw receive accepted on a handle that is not one of the owner's symbolic counterparts is at most CE-UKS sender's bound (`PqxdhDeploymentHeadlineUks.ce_uks_sender`) plus `ε_A1` plus the explicit public terms `ctGapTerm` (F-ct2) and `ctCollTerm`. Premises: those of `ce_uks_sender` and of CE-A1. -/
theorem ce_uks_sym (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[uksSym setup codec route <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
            (uksSenderEvent setup.source.crypto codec setup.serverKeyId budget route)
            (uksSenderClaim setup.source.crypto codec setup.serverKeyId budget route) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
            (uksSenderEvent setup.source.crypto codec setup.serverKeyId budget route)
            (uksSenderClaim setup.source.crypto codec setup.serverKeyId budget route) (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
            fallback caps qInit (slotted setup codec budget
              (uksSenderEvent setup.source.crypto codec setup.serverKeyId budget route)
              (uksSenderClaim setup.source.crypto codec setup.serverKeyId budget route) (g.1, g.2.castSucc)) +
          bindingTerm (inputG caps qInit budget bounds))) +
      ENNReal.ofReal (a1Term setup codec checks caps route bounds mode adversary budget a1Fallback signatureFallback) +
      ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime +
      ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime :=
  (ce_uks_sym_le setup codec checks route ensureInit phase1 phase2 bounds mode adversary budget respects
    runtime).trans (add_le_add (add_le_add (add_le_add
      (PqxdhDeploymentHeadlineUks.ce_uks_sender setup functional codec checks route ensureInit phase1 phase2 correct caps
        bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback)
      (a1_chance setup codec checks caps bounded route ensureInit phase1 phase2 frameReadBack writable law spread correct
        adapter bounds mode adversary budget respects runtime a1Fallback signatureFallback)) le_rfl) le_rfl)

/-- `ce_app_sym` (design-v2 section 7.3; VC rows App-b2s, b2s-S2 and App-s2b, s2b-S1 on symbolic eligibility, mode P): the probability that the adversary's claimed fresh message, sent on a symbolically eligible handle, equals its guess is at most CE-APP's bound (`PqxdhDeploymentHeadlineApp.ce_app`) plus `ε_A2pub + ε_A1` plus the explicit public term `ctGapTerm` (F-ct2), through `sym_gap`. Premises: those of `ce_app`, of `server_gap_bound` and of CE-A1. -/
theorem ce_app_sym (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes))
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[appSym setup codec appClaim <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
            (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
            (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime +
          recLoss setup codec checks route ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
            caps qInit (slotted setup codec budget (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
              (appHandle appClaim) (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (a2pubTerm setup codec checks route ensureInit bounds .P adversary budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P adversary budget a1Fallback signatureFallback) +
        ctGapTerm setup codec checks route ensureInit bounds .P adversary runtime) :=
  (ce_app_sym_le setup codec checks route ensureInit bounds .P adversary budget runtime appClaim).trans
    (add_le_add (PqxdhDeploymentHeadlineApp.ce_app setup functional codec checks route ensureInit phase1 phase2 correct
      caps bounded qInit initBound bounds adversary budget respects runtime fallback appClaim)
      (PqxdhDeploymentHeadlineGap.sym_gap setup codec checks caps bounded shortRejects route ensureInit phase1 phase2
        frameReadBack writable law spread correct adapter bounds .P adversary budget respects runtime identityFallback
        ordinaryFallback a1Fallback signatureFallback))

/-- `ce_app_server_sym` (design-v2 section 7.3; VC rows App-s2b, s2b-S1 on Server-side symbolic eligibility, mode P): the probability that the adversary's claimed fresh message, sent on a Server peer with `SymServer`, equals its guess is at most CE-APP Server's bound (`PqxdhDeploymentHeadlineApp.ce_app_server`) plus `ε_A2pub`. Premises: those of `ce_app_server` and of `server_gap_bound`. -/
theorem ce_app_server_sym (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (appClaim : X → Option (Nat × Pqxdh.Bytes))
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    𝒟[appPeerSym setup codec appClaim <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
            (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
            (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          recLoss setup codec checks route ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
            caps qInit (serverSlotted setup codec budget
              (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
              (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      a2pubTerm setup codec checks route ensureInit bounds .P adversary budget runtime identityFallback
        ordinaryFallback :=
  (ce_app_server_sym_le setup codec checks route ensureInit bounds .P adversary budget runtime appClaim).trans
    (add_le_add (PqxdhDeploymentHeadlineApp.ce_app_server setup functional codec checks route ensureInit phase1 phase2
      correct caps bounded qInit initBound bounds adversary budget respects runtime fallback appClaim)
      (PqxdhDeploymentHeadlineGap.server_gap_bound setup codec checks shortRejects route ensureInit phase1 phase2 bounds
        .P adversary budget respects runtime identityFallback ordinaryFallback))

/-- `ce_kt_sym` (design-v2 section 7.3; VC rows A1-root, S3-server, S3-beacon on symbolic eligibility): the probability of an event whose claim names a symbolically eligible handle is at most CE-KT's one-sided bound (`PqxdhDeploymentHeadlineKeyTransfer.ce_kt_sum_le`: the sum over the targets of the ideal game's probability plus `kemLoss` and `slotLoss`) plus `ε_A2pub + ε_A1` plus the explicit public term `ctGapTerm` (F-ct2). Premises: those of `ce_kt_sum_le`, of `server_gap_bound` and of CE-A1 (CE-KT's own premises do not include `KemBound`, which CE-A1 needs). -/
theorem ce_kt_sym (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (runtime : A)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[ktSym setup codec event claim <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[(fun outcome => decide (happens event (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
            PqxdhDeploymentKemTransfer.designated setup.source.crypto codec setup.serverKeyId budget claim
              (PqxdhDeploymentIdealBranch.classicalOf outcome) =
                some ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity))) <$>
          (PqxdhDeploymentIdealSteps.idealGame setup codec route checks budget (g.1, g.2.castSucc) ensureInit bounds
            mode adversary).run runtime] {true} +
        ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget event claim
          (g.1, g.2.castSucc) runtime) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget event claim
          (g.1, g.2.castSucc) runtime))) +
      (a2pubTerm setup codec checks route ensureInit bounds mode adversary budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds mode adversary budget a1Fallback signatureFallback) +
        ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime) :=
  (ce_kt_sym_le setup codec checks route ensureInit bounds mode adversary budget runtime event claim).trans
    (add_le_add (PqxdhDeploymentHeadlineKeyTransfer.ce_kt_sum_le setup functional codec checks route ensureInit phase1
      phase2 correct bounds mode adversary budget respects event claim runtime)
      (PqxdhDeploymentHeadlineGap.sym_gap setup codec checks caps bounded shortRejects route ensureInit phase1 phase2
        frameReadBack writable law spread correct adapter bounds mode adversary budget respects runtime identityFallback
        ordinaryFallback a1Fallback signatureFallback))

end Headlines

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.acceptReplies_logged' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.acceptReplies_logged

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.sessionAt_positional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.sessionAt_positional

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.owner_cpart_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.owner_cpart_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.peer_cpart_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.peer_cpart_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.origin_b2s_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.origin_b2s_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.origin_s2b_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.origin_s2b_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.undesignated_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.undesignated_gap

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.uks_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.uks_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.app_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.app_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.app_peer_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.app_peer_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.kt_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.kt_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.chance_le_add4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.chance_le_add4

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.a1_chance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.a1_chance

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_or_b2s_sym_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_or_b2s_sym_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_or_s2b_sym_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_or_s2b_sym_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_uks_sym_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_uks_sym_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_app_sym_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_app_sym_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_app_server_sym_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_app_server_sym_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_kt_sym_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_kt_sym_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_or_b2s_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_or_b2s_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_or_s2b_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_or_s2b_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_uks_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_uks_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_app_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_app_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_app_server_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_app_server_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_kt_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic.ce_kt_sym
