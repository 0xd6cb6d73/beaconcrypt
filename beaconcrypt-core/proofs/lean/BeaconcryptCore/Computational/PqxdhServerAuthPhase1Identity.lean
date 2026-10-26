import BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity

/-! Concrete identity parsing of the same actual Phase1 pending-token receipt. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity
open PqxdhServerAuthExperiment PqxdhJointIdentity PqxdhEd25519EufCma
open PqxdhServerAuthPhase1Origins PqxdhServerAuthPhase1Receipt
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The three public unsigned Phase1 fields, with no identity seed argument. -/
def material (prekey oneTime : X25519PublicKey) (pqKey : PqxdhKemIndCca.MlKem768PublicKey) :
    Phase1Material Unit := ⟨prekey, oneTime, pqKey, ()⟩

/-- The literal context's prekey, generated one-time public key and ML-KEM public key. This projection does not read the target Beacon identity seed. -/
def contextMaterial (setup : Setup baseSpec KemSK) (context : PqxdhServerAuthEntryFactor.Context KemSK) :
    Phase1Material Unit :=
  material (context.publicValue setup).prekey (setup.dh.publicKey context.oneTime) context.keys.1

/-- Original attached verification returns the same identity parsed from the original candidate field. No signature adapter is needed for this source equation. -/
theorem accepted_identity (verify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (candidate : Phase1Candidate) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
    (accepted : PqxdhJointPhase1Reports.sourceAccept verify candidate = some (identity, keys)) :
    parseIdentity candidate.identityKey = some identity := by
  simp only [PqxdhJointPhase1Reports.sourceAccept, Option.bind_eq_bind, Option.pure_def,
    Option.bind_eq_some_iff] at accepted
  obtain ⟨key, parsed, pq, _, pre, _, one, _, repeated, _, prekey, _, oneTime, _, pqKey, _, same⟩ := accepted
  have identityEq : key = identity := congrArg Prod.fst (Option.some.inj same)
  exact identityEq ▸ parsed

/-- The same actual pending receipt exposes the original reader/getters and parsed identity stored in the native token. -/
theorem token_identity (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PqxdhJointGapDh.PublicChallenge) (raw : Pqxdh.Bytes)
    (token : PqxdhServerRelatedRootConsumer.Returned)
    (receipt : TokenReceipt setup codec checks publicValue raw token) :
    ∃ verified : PqxdhServerRootPreparation.Verified Reader,
      Decoded codec raw verified ∧
      parseIdentity verified.candidate.identityKey = some verified.identity ∧
      token.pending.beacon_identity_public_key = PqxdhRootTableInitialization.rootArray verified.identity ∧
      PqxdhJointPhase1Reports.sourceAccept (fun identity => setup.source.crypto.verify identity.toList)
        verified.candidate = some (verified.identity, verified.keys) := by
  obtain ⟨consumed, after, input, supported, pendingEq, decoded, accepted⟩ := receipt
  exact ⟨input.verified, decoded, accepted_identity _ _ _ _ accepted,
    congrArg beaconcrypt_core.pqxdh.PendingServerRegistration.beacon_identity_public_key pendingEq, accepted⟩

/-- Matching the actual builder's AD to the original Beacon control identifies the accepted signature key and leaves only the existing unsigned-field substitution event. -/
theorem matched_fields (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PqxdhJointGapDh.PublicChallenge) (raw : Pqxdh.Bytes)
    (token : PqxdhServerRelatedRootConsumer.Returned)
    (receipt : TokenReceipt setup codec checks publicValue raw token)
    (payload : Option Pqxdh.Bytes) (server : PqxdhServerAuthEntryFactor.ServerState)
    (response : PqxdhServerRegistrationPublication.Response) (entry : CtxRomAuth.CtxSuccessfulSeal)
    (built : PqxdhServerAuthPublicationBuiltRecord.At codec token.pending payload server response entry)
    (control : pqxdh.BeaconInitSent) (target : Ed25519PublicKey)
    (identity : control.beacon_identity_public_key = PqxdhRootTableInitialization.rootArray target)
    (same : entry.input.context.ad.bytes = absBytes (PqxdhBeaconPhase2Shared.associatedData control))
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    {Context : Type} (material : Phase1Material Context) :
    ∃ verified : PqxdhServerRootPreparation.Verified Reader,
      Decoded codec raw verified ∧ verified.identity = target ∧
      (verified.keys = material.keyTuple ∨
        phase1FieldSubstitutionBit setup.joint.verify target material verified.candidate = true) := by
  obtain ⟨verified, decoded, parsed, stored, accepted⟩ := token_identity setup codec checks publicValue raw token receipt
  have bound := (PqxdhServerAuthPublicationIdentity.receipt_identities codec token.pending payload server response entry built control same).2
  have identityEq : verified.identity = target := by
    apply List.Vector.toList_injective
    simpa only [PqxdhRootTableInitialization.rootArray_bytes] using
      congrArg absBytes (stored.symm.trans (bound.trans identity))
  refine ⟨verified, decoded, identityEq, ?_⟩
  by_cases fields : verified.keys = material.keyTuple
  · exact Or.inl fields
  · apply Or.inr
    apply (phase1FieldSubstitutionBit_eq_true_iff _ _ _ _).mpr
    refine ⟨verified.keys, ?_, fields⟩
    rw [← identityEq, ← PqxdhJointPhase1Reports.sourceAccept_eq _ setup.joint adapter]
    exact accepted

/-- The actual successful builder and concrete ordered AD bytes identify the same parsed target verification key, with no cryptographic-output injectivity premise. -/
theorem matched_record (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PqxdhJointGapDh.PublicChallenge) (raw : Pqxdh.Bytes)
    (token : PqxdhServerRelatedRootConsumer.Returned)
    (receipt : TokenReceipt setup codec checks publicValue raw token)
    (payload : Option Pqxdh.Bytes) (server : PqxdhServerAuthEntryFactor.ServerState)
    (response : PqxdhServerRegistrationPublication.Response) (entry : CtxRomAuth.CtxSuccessfulSeal)
    (built : PqxdhServerAuthPublicationBuiltRecord.At codec token.pending payload server response entry)
    (targetServer : PqxdhBeaconPhase2Preparation.Word32) (target : Ed25519PublicKey)
    (same : entry.input.context.ad.bytes = Pqxdh.assocData (absBytes targetServer) target.toList) :
    ∃ verified : PqxdhServerRootPreparation.Verified Reader,
      Decoded codec raw verified ∧ verified.identity = target ∧
      PqxdhJointPhase1Reports.sourceAccept (fun identity => setup.source.crypto.verify identity.toList)
        verified.candidate = some (verified.identity, verified.keys) := by
  obtain ⟨verified, decoded, parsed, stored, accepted⟩ := token_identity setup codec checks publicValue raw token receipt
  obtain ⟨key, candidate, binding, sealed, encrypted, nonce, width, _, prepared, _, contextSame,
    _, _, _, input, _⟩ := built
  have candidateBytes : absBytes candidate.associated_data =
      Pqxdh.assocData (absBytes targetServer) target.toList :=
    (congrArg (fun context : RawCtxSourceSend.SealContext => context.associatedData) contextSame).symm.trans
      ((congrArg (fun input : CtxRomAuth.CtxSealInput => input.context.ad.bytes) input).symm.trans same)
  have fields := Pqxdh.assocData_inj
    (by simp : (absBytes server.server.identity).length = 32)
    (by simp : (absBytes token.pending.beacon_identity_public_key).length = 32)
    (by simp : (absBytes targetServer).length = 32) target.2
    ((PqxdhServerAuthPublicationIdentity.prepared_bytes server.control token.pending
      ⟨server.server.identity, server.identityKeyId⟩ _ candidate prepared).symm.trans candidateBytes)
  have identityEq : verified.identity = target := by
    apply List.Vector.toList_injective
    simpa only [PqxdhRootTableInitialization.rootArray_bytes, List.Vector.toList] using
      (congrArg absBytes stored).symm.trans fields.2
  exact ⟨verified, decoded, identityEq, accepted⟩

open PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState PqxdhSecretInputKdf
abbrev Observed := PqxdhServerAuthPublicationRecordReserve.Observed

/-- The complete actual accepted-owner run identifies the same consumed pending token's verified target identity and earlier raw acceptance. Source initialization, admission and the AD match are all discharged by that run. -/
theorem journal_identity (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
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
        ∀ entry ∈ result.2.1.seals,
          PqxdhServerAuthPublicationBuiltRecord.At codec token.pending payload server response entry := by
  rcases PqxdhServerAuthPhase1BuildOrigins.accepted_records setup codec checks adversary context rest key Q j writable
    result supported journal normal snap accepted owned notBad unique payload response published with won | ⟨receipt, records⟩
  · exact Or.inl won
  · obtain ⟨token, server, raw, origin, beforeBuild, records⟩ := records
    obtain ⟨message, reply, bytes, sealContext, entry, attempt, target, touched, rooted, beacon,
      logged, fields, recorded, attempted, decoded, plaintext, sealed, matched⟩ := receipt
    have retained := PqxdhServerAuthPublicationBuildJournal.retained_program true
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key
      (PqxdhServerAuthPublicationOccurrence.execution setup codec checks adversary Q j context rest)
      (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)
      (by intro attempt found; cases found) result supported
    have identities := PqxdhServerAuthBeaconIdentity.observed_initial setup codec checks context sampled rest key Q j
      (PqxdhServerAuthApiJournal.record (adversary (contextInput setup false context))) result supported
    have same : entry.input.context.ad.bytes = Pqxdh.assocData
        (absBytes (binding setup (context.publicValue setup)).identity_public_key)
        (setup.joint.publicKeys context.beaconSeed).ed25519.toList := by
      simpa only [PqxdhRootTableInitialization.rootArray_bytes] using
        recorded.2.1.trans ((congrArg Accepted.associatedData fields).trans (identities.2 snap accepted))
    obtain ⟨verified, sourceDecoded, identityEq, verifiedFields⟩ := matched_record setup codec checks
      (context.publicValue setup) raw token origin payload server response entry
      (records entry (retained attempt attempted entry sealed)) _ _ same
    exact Or.inr ⟨token, server, raw, verified, origin, beforeBuild, sourceDecoded, identityEq, verifiedFields, records⟩

/-- The actual accepted record's earlier verified Phase1 fields are the supplied material tuple or the existing joint-use field-substitution event. Only this verification-interface consumer requires the approved full attached-buffer adapter; no cryptographic bound is asserted. -/
theorem journal_fields (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
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
    {MaterialContext : Type} (material : Phase1Material MaterialContext)
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
        (verified.keys = material.keyTuple ∨ phase1FieldSubstitutionBit setup.joint.verify
          (setup.joint.publicKeys context.beaconSeed).ed25519 material verified.candidate = true) ∧
        ∀ entry ∈ result.2.1.seals,
          PqxdhServerAuthPublicationBuiltRecord.At codec token.pending payload server response entry := by
  rcases journal_identity setup codec checks adversary context sampled rest key Q j writable result supported
    journal normal snap accepted owned notBad unique payload response published with won | origin
  · exact Or.inl won
  · obtain ⟨token, server, raw, verified, receipt, beforeBuild, decoded, identityEq, acceptedFields, records⟩ := origin
    refine Or.inr ⟨token, server, raw, verified, receipt, beforeBuild, decoded, identityEq, acceptedFields, ?_, records⟩
    by_cases fields : verified.keys = material.keyTuple
    · exact Or.inl fields
    · apply Or.inr
      apply (phase1FieldSubstitutionBit_eq_true_iff _ _ _ _).mpr
      refine ⟨verified.keys, ?_, fields⟩
      rw [← identityEq, ← PqxdhJointPhase1Reports.sourceAccept_eq _ setup.joint adapter]
      exact acceptedFields

end BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity.accepted_identity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity.accepted_identity
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity.token_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity.token_identity
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity.matched_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity.matched_fields
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity.matched_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity.matched_record
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity.journal_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity.journal_identity
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity.journal_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Identity.journal_fields
