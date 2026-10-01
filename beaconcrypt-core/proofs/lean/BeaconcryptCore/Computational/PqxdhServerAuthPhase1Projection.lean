import BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity

/-! Actual unsigned verifier fields and native pending registration projection. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.ProtocolComposition
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection
open PqxdhServerAuthExperiment PqxdhEd25519EufCma PqxdhJointIdentity
open PqxdhServerAuthPhase1Receipt PqxdhServerAuthPhase1Origins PqxdhServerRootPreparation
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The same actual attached-verifier outputs are exactly the unsigned tagged fields accepted by the original parsers. The verification function remains arbitrary. -/
theorem source_fields (verify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (candidate : Phase1Candidate) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
    (accepted : PqxdhJointPhase1Reports.sourceAccept verify candidate = some (identity, keys)) :
    candidate.identityKey = encodedIdentity identity ∧
    verify identity candidate.preKey = some (prekeyMessage keys.prekey) ∧
    verify identity candidate.oneTimeKey = some (oneTimeMessage keys.oneTime) ∧
    verify identity candidate.pqKey = some (pqMessage keys.pqKey) := by
  simp only [PqxdhJointPhase1Reports.sourceAccept, Option.bind_eq_bind, Option.pure_def,
    Option.bind_eq_some_iff] at accepted
  obtain ⟨key, parsed, pq, pqVerified, pre, preVerified, one, oneVerified, repeated, _, prekey, preParsed,
    oneTime, oneParsed, pqKey, pqParsed, same⟩ := accepted
  cases same
  exact ⟨(parseIdentity_eq_some_iff _ _).mp parsed,
    (parsePrekeyMessage_eq_some_iff _ _).mp preParsed ▸ preVerified,
    (parseOneTimeMessage_eq_some_iff _ _).mp oneParsed ▸ oneVerified,
    (parsePqMessage_eq_some_iff _ _).mp pqParsed ▸ pqVerified⟩

/-- The fixed-width native unsigned InitKex, using the actual source tags and unmodified typed key bytes. -/
def unsigned (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) : pqxdh.InitKex where
  identity_key := ⟨(encodedIdentity identity).map concreteByte, by simp⟩
  prekey := ⟨(prekeyMessage keys.prekey).map concreteByte, by simp⟩
  one_time_key := ⟨(oneTimeMessage keys.oneTime).map concreteByte, by simp⟩
  pq_key := ⟨(pqMessage keys.pqKey).map concreteByte, by simp⟩

/-- Projecting the actual native fields recovers all four original unsigned verifier byte strings. -/
theorem unsigned_bytes (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) :
    absBytes (unsigned identity keys).identity_key = encodedIdentity identity ∧
    absBytes (unsigned identity keys).prekey = prekeyMessage keys.prekey ∧
    absBytes (unsigned identity keys).one_time_key = oneTimeMessage keys.oneTime ∧
    absBytes (unsigned identity keys).pq_key = pqMessage keys.pqKey := by
  simp [unsigned, absBytes, List.map_map, Function.comp_def]

/-- The original unsigned native structure contains exactly the decoder's identity and the three actual successful verifier replies, independently of any signature representation. -/
theorem source_unsigned (verify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (candidate : Phase1Candidate) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
    (accepted : PqxdhJointPhase1Reports.sourceAccept verify candidate = some (identity, keys)) :
    candidate.identityKey = absBytes (unsigned identity keys).identity_key ∧
    verify identity candidate.preKey = some (absBytes (unsigned identity keys).prekey) ∧
    verify identity candidate.oneTimeKey = some (absBytes (unsigned identity keys).one_time_key) ∧
    verify identity candidate.pqKey = some (absBytes (unsigned identity keys).pq_key) := by
  simp only [(unsigned_bytes identity keys).1, (unsigned_bytes identity keys).2.1,
    (unsigned_bytes identity keys).2.2.1, (unsigned_bytes identity keys).2.2.2]
  exact source_fields verify candidate identity keys accepted

/-- Two receipts from the same raw request have the same reader, candidate and verified tuple because they use the same concrete functions. This does not assert injectivity of the decoder or verifier. -/
theorem decoded_unique (codec : Codec Reader Response)
    (verify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (raw : Pqxdh.Bytes) (first second : Verified Reader)
    (firstDecoded : Decoded codec raw first) (secondDecoded : Decoded codec raw second)
    (firstAccepted : PqxdhJointPhase1Reports.sourceAccept verify first.candidate = some (first.identity, first.keys))
    (secondAccepted : PqxdhJointPhase1Reports.sourceAccept verify second.candidate = some (second.identity, second.keys)) :
    first = second := by
  have readers : first.reader = second.reader := Option.some.inj (firstDecoded.1.symm.trans secondDecoded.1)
  have identities := Option.some.inj (firstDecoded.2.1.symm.trans
    ((congrArg codec.identity readers).trans secondDecoded.2.1))
  have prekeys := Option.some.inj (firstDecoded.2.2.1.symm.trans
    ((congrArg codec.preField readers).trans secondDecoded.2.2.1))
  have oneTimes := Option.some.inj (firstDecoded.2.2.2.1.symm.trans
    ((congrArg codec.oneField readers).trans secondDecoded.2.2.2.1))
  have pqKeys := Option.some.inj (firstDecoded.2.2.2.2.symm.trans
    ((congrArg codec.pqField readers).trans secondDecoded.2.2.2.2))
  have candidates : first.candidate = second.candidate := by
    cases firstCandidate : first.candidate
    cases secondCandidate : second.candidate
    simpa only [firstCandidate, secondCandidate, Phase1Candidate.mk.injEq] using
      And.intro identities (And.intro prekeys (And.intro oneTimes pqKeys))
  have fields := Option.some.inj (firstAccepted.symm.trans
    ((congrArg (PqxdhJointPhase1Reports.sourceAccept verify) candidates).trans secondAccepted))
  cases first
  cases second
  simp_all only [Prod.mk.injEq]

/-- The same decoded verified occurrence fixes the native pending binding, raw identity and registration ID, including the exact original core registration-ID operation. The cleared root field is not used to reconstruct a root. -/
theorem token_fields (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PqxdhJointGapDh.PublicChallenge) (raw : Pqxdh.Bytes)
    (token : PqxdhServerRelatedRootConsumer.Returned)
    (receipt : TokenReceipt setup codec checks publicValue raw token)
    (verified : Verified Reader) (decoded : Decoded codec raw verified)
    (accepted : PqxdhJointPhase1Reports.sourceAccept (fun identity => setup.source.crypto.verify identity.toList)
      verified.candidate = some (verified.identity, verified.keys)) :
    token.pending.server_binding = binding setup publicValue ∧
    token.pending.beacon_identity_public_key = PqxdhRootTableInitialization.rootArray verified.identity ∧
    token.pending.registration_id = PqxdhServerClearedRoot.registrationIdValue verified ∧
    absBytes token.pending.registration_id.bytes = verified.identity.toList ++ verified.keys.oneTime.toList ∧
    pqxdh.registration_id (PqxdhProtocolAcceptance.verified verified.identity verified.keys) =
      ok token.pending.registration_id := by
  obtain ⟨consumed, after, input, supported, pendingEq, sourceDecoded, sourceAccepted⟩ := receipt
  have same := decoded_unique codec (fun identity => setup.source.crypto.verify identity.toList) raw
    input.verified verified sourceDecoded decoded sourceAccepted accepted
  rw [pendingEq, ← same]
  refine ⟨rfl, rfl, rfl, ?_, PqxdhServerClearedRoot.registrationId_source input.verified⟩
  simp [PqxdhServerClearedRoot.pending, PqxdhServerClearedRoot.registrationIdValue,
    absBytes, List.map_map, Function.comp_def]

/-- When the actual verified tuple is the target context's unsigned material, its native registration ID is precisely the target raw identity followed by the original one-time public key. -/
theorem context_registration (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : PqxdhServerAuthEntryFactor.Context KemSK) (raw : Pqxdh.Bytes)
    (token : PqxdhServerRelatedRootConsumer.Returned)
    (receipt : TokenReceipt setup codec checks (context.publicValue setup) raw token)
    (verified : Verified Reader) (decoded : Decoded codec raw verified)
    (accepted : PqxdhJointPhase1Reports.sourceAccept (fun identity => setup.source.crypto.verify identity.toList)
      verified.candidate = some (verified.identity, verified.keys))
    (identity : verified.identity = (setup.joint.publicKeys context.beaconSeed).ed25519)
    (fields : verified.keys = (PqxdhServerAuthPhase1Identity.contextMaterial setup context).keyTuple) :
    token.pending.server_binding = binding setup (context.publicValue setup) ∧
    token.pending.beacon_identity_public_key =
      PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys context.beaconSeed).ed25519 ∧
    absBytes token.pending.registration_id.bytes =
      (setup.joint.publicKeys context.beaconSeed).ed25519.toList ++ (setup.dh.publicKey context.oneTime).toList := by
  have actual := token_fields setup codec checks (context.publicValue setup) raw token receipt verified decoded accepted
  refine ⟨actual.1, ?_, ?_⟩
  · exact actual.2.1.trans (congrArg PqxdhRootTableInitialization.rootArray identity)
  · simpa only [identity, fields, PqxdhServerAuthPhase1Identity.contextMaterial,
      PqxdhServerAuthPhase1Identity.material, Phase1Material.keyTuple] using actual.2.2.2.1

/-- The exact unsigned field projection is accepted by the original extracted validator with the unchanged typed verification result. -/
theorem unsigned_validates (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) :
    pqxdh.validate_init_kex (unsigned identity keys) =
      ok (.Ok (PqxdhProtocolAcceptance.verified identity keys)) := by
  have identityTag := BeaconcryptCore.Refinement.PqxdhSurface.untag_sign_key_of_parse (unsigned identity keys).identity_key
    (PqxdhProtocolAcceptance.verified identity keys).beacon_identity_public_key
    (by simp [(unsigned_bytes identity keys).1, encodedIdentity, PqxdhProtocolAcceptance.verified,
      PqxdhRootTableInitialization.rootArray_bytes])
  have prekeyTag := BeaconcryptCore.Refinement.PqxdhSurface.untag_x25519_key_of_parse (unsigned identity keys).prekey pqxdh.KEY_ROLE_PREKEY
    (PqxdhProtocolAcceptance.verified identity keys).beacon_prekey_public_key
    (by simp [(unsigned_bytes identity keys).2.1, prekeyMessage, PqxdhProtocolAcceptance.verified,
      PqxdhRootTableInitialization.rootArray_bytes])
  have oneTimeTag := BeaconcryptCore.Refinement.PqxdhSurface.untag_x25519_key_of_parse (unsigned identity keys).one_time_key pqxdh.KEY_ROLE_ONE_TIME
    (PqxdhProtocolAcceptance.verified identity keys).beacon_one_time_public_key
    (by simp [(unsigned_bytes identity keys).2.2.1, oneTimeMessage, PqxdhProtocolAcceptance.verified,
      PqxdhRootTableInitialization.rootArray_bytes])
  have pqTag := BeaconcryptCore.Refinement.PqxdhSurface.untag_mlkem768_key_of_parse (unsigned identity keys).pq_key
    (PqxdhProtocolAcceptance.verified identity keys).beacon_pq_public_key
    (by rw [(unsigned_bytes identity keys).2.2.2];
        simp [pqMessage, PqxdhProtocolAcceptance.verified, absBytes, List.map_map, Function.comp_def])
  simp [pqxdh.validate_init_kex, identityTag, prekeyTag, oneTimeTag, pqTag]

/-- Exact unsigned and native pending fields of one source-verified occurrence. These are functional output equations, not a premise about signature security or root identity. -/
def Projected (setup : Setup baseSpec KemSK) (publicValue : PqxdhJointGapDh.PublicChallenge)
    (token : PqxdhServerRelatedRootConsumer.Returned) (verified : Verified Reader) : Prop :=
  token.pending.server_binding = binding setup publicValue ∧
  token.pending.beacon_identity_public_key = PqxdhRootTableInitialization.rootArray verified.identity ∧
  absBytes token.pending.registration_id.bytes = verified.identity.toList ++ verified.keys.oneTime.toList ∧
  pqxdh.registration_id (PqxdhProtocolAcceptance.verified verified.identity verified.keys) =
    ok token.pending.registration_id ∧
  pqxdh.validate_init_kex (unsigned verified.identity verified.keys) =
    ok (.Ok (PqxdhProtocolAcceptance.verified verified.identity verified.keys)) ∧
  verified.candidate.identityKey = absBytes (unsigned verified.identity verified.keys).identity_key ∧
  setup.source.crypto.verify verified.identity.toList verified.candidate.preKey =
    some (absBytes (unsigned verified.identity verified.keys).prekey) ∧
  setup.source.crypto.verify verified.identity.toList verified.candidate.oneTimeKey =
    some (absBytes (unsigned verified.identity verified.keys).one_time_key) ∧
  setup.source.crypto.verify verified.identity.toList verified.candidate.pqKey =
    some (absBytes (unsigned verified.identity verified.keys).pq_key)

/-- The concrete pending-token receipt discharges every unsigned/native projection equation for its same actual decoded verification result. -/
theorem token_projection (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PqxdhJointGapDh.PublicChallenge) (raw : Pqxdh.Bytes)
    (token : PqxdhServerRelatedRootConsumer.Returned)
    (receipt : TokenReceipt setup codec checks publicValue raw token)
    (verified : Verified Reader) (decoded : Decoded codec raw verified)
    (accepted : PqxdhJointPhase1Reports.sourceAccept (fun identity => setup.source.crypto.verify identity.toList)
      verified.candidate = some (verified.identity, verified.keys)) :
    Projected setup publicValue token verified := by
  have actual := token_fields setup codec checks publicValue raw token receipt verified decoded accepted
  exact ⟨actual.1, actual.2.1, actual.2.2.2.1, actual.2.2.2.2,
    unsigned_validates verified.identity verified.keys,
    source_unsigned (fun identity => setup.source.crypto.verify identity.toList)
      verified.candidate verified.identity verified.keys accepted⟩

open PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState PqxdhSecretInputKdf
abbrev Observed := PqxdhServerAuthPublicationRecordReserve.Observed

/-- The actual accepted-owner journal supplies one same-token native projection and either the context's exact unsigned Phase1 tuple or the existing joint-use field-substitution event. The ordinary observer-win alternative and every successful builder record are retained. -/
theorem journal_projection (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (context : Context KemSK)
    (sampled : context ∈ support (contextSample setup codec))
    (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput) (Q : Nat) (j : Fin (Q + 1))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : (Option (Unit × QueryLog ServerAuthSpec) × (Local KemSK × Option Nat)) × Observed)
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      (PqxdhServerAuthPublicationOccurrence.execution setup codec checks adversary Q j context rest)).run
      (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)))
    (journal : QueryLog ServerAuthSpec) (normal : result.1.1 = some ((), journal))
    (snap : Snapshot) (accepted : result.1.2.1.1.1.ghost.acceptance = some snap)
    (owned : entryOwner setup context.seed context.scalar Q result.1.2.1.1.1.ghost = some j)
    (notBad : result.1.2.1.1.2.2.bad = false)
    (unique : ¬ CollB setup context.seed context.scalar result.1.2.1.1.1.ghost)
    (payload : Option Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (published : (⟨.inr (.build j.val payload), some response⟩ :
      (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈ journal) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1 = true ∨
      ∃ (token : PqxdhServerRelatedRootConsumer.Returned) (server : ServerState) (raw : Pqxdh.Bytes)
        (verified : PqxdhServerRootPreparation.Verified Reader),
        TokenReceipt setup codec checks (context.publicValue setup) raw token ∧
        PqxdhServerAuthPhase1BuildOrigins.BeforeBuild journal j.val payload response raw ∧
        Decoded codec raw verified ∧ verified.identity = (setup.joint.publicKeys context.beaconSeed).ed25519 ∧
        PqxdhJointPhase1Reports.sourceAccept (fun identity => setup.source.crypto.verify identity.toList)
          verified.candidate = some (verified.identity, verified.keys) ∧
        Projected setup (context.publicValue setup) token verified ∧
        (verified.keys = (PqxdhServerAuthPhase1Identity.contextMaterial setup context).keyTuple ∨ phase1FieldSubstitutionBit setup.joint.verify
          (setup.joint.publicKeys context.beaconSeed).ed25519 (PqxdhServerAuthPhase1Identity.contextMaterial setup context) verified.candidate = true) ∧
        ∀ entry ∈ result.2.1.seals,
          PqxdhServerAuthPublicationBuiltRecord.At codec token.pending payload server response entry := by
  rcases PqxdhServerAuthPhase1Identity.journal_fields setup codec checks adversary context sampled rest key Q j
    writable result supported journal normal snap accepted owned notBad unique payload response adapter
    (PqxdhServerAuthPhase1Identity.contextMaterial setup context) published with won | origin
  · exact Or.inl won
  · obtain ⟨token, server, raw, verified, receipt, beforeBuild, decoded, identityEq, acceptedFields,
      fields, records⟩ := origin
    exact Or.inr ⟨token, server, raw, verified, receipt, beforeBuild, decoded, identityEq, acceptedFields,
      token_projection setup codec checks (context.publicValue setup) raw token receipt verified decoded acceptedFields,
      fields, records⟩

end BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection.source_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection.source_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection.unsigned_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection.unsigned_bytes

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection.source_unsigned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection.source_unsigned

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection.decoded_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection.decoded_unique

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection.token_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection.token_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection.context_registration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection.context_registration

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection.unsigned_validates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection.unsigned_validates

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection.token_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection.token_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection.journal_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection.journal_projection
