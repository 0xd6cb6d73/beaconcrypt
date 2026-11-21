import BeaconcryptCore.Computational.PqxdhServerAuthRootExecution
import BeaconcryptCore.Computational.PqxdhRegistrationResponse
import BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl

/-! Actual native session fields at the source-root initialization occurrences. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthRootOccurrences
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Native successful publication supplies the exact pending/current binding check; the proof uses the actual complete builder support and allows all earlier callback effects. The builder runs at the supplied per-call associated data, which is also the new peer's metadata (lower layer). -/
theorem native_binding (associatedData : PqxdhTranscriptAd.AssociatedData)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (pending : pqxdh.PendingServerRegistration) (root : RootOutput) (payload : Option Pqxdh.Bytes)
    (before after : ServerState) (cache next : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (response : PqxdhServerRegistrationPublication.Response)
    (supported : (ok (some response, after), next) ∈ support
      ((simulateQ (tailImpl setup codec checks)
        (PqxdhServerRegistrationPublication.build (associatedData := associatedData) setup.source pending root payload
          associatedData before)).run cache)) :
    pending.server_binding = ⟨before.server.identity, before.identityKeyId⟩ := by
  rcases PqxdhRegistrationResponse.build_publication associatedData (tailImpl setup codec checks) setup.source pending
      root payload associatedData before cache (ok (some response, after), next) supported with failed |
      ⟨_, candidate, _, _, _, prepared, _⟩
  · cases RustM.ok.inj failed
  · exact PqxdhServerAuthPhase1Binding.prepare_binding before.control pending _ _ candidate prepared

/-- A candidate that passed the Server's pure pre-hash guard carries the pending Beacon identity and the Server's current identity binding. -/
theorem prehash_fields {Metadata PeerMetadata Consumed : Type}
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (candidate : pqxdh.ServerRegistrationCandidate)
    (passed : PqxdhServerRegistrationPublication.prehash state pending data = some candidate) :
    candidate.beacon_identity_public_key = pending.beacon_identity_public_key ∧
      candidate.server_identity_public_key = state.server.identity ∧
      candidate.server_identity_key_id = state.identityKeyId := by
  obtain ⟨next, hnext⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok state.control
  simp only [PqxdhServerRegistrationPublication.prehash, hnext] at passed
  cases next with
  | Err => exact absurd passed (by simp)
  | Ok next =>
      obtain ⟨prepared, hprepared⟩ := BeaconcryptCore.PanicFreedom.server_prepare_commit_ok
        state.control pending ⟨state.server.identity, state.identityKeyId⟩
        (if (state.server.peers next).isSome then pqxdh.KeyIdAvailability.Occupied else .Available)
      simp only [hprepared] at passed
      cases prepared with
      | Err => split_ifs at passed
      | Ok prepared =>
          split_ifs at passed
          cases passed
          obtain ⟨beacon, server, identifier, _, _⟩ :=
            PqxdhServerAuthNegativeControl.prepare_commit_fields _ _ _ _ _ hprepared
          exact ⟨beacon, server, identifier⟩

/-- The exact native successful build of a candidate that passed the pure pre-hash guard has one source seal context, for that same candidate under the supplied per-call associated data, and an initializer run using the supplied source root. No writer totality or decode/read-back premise is needed. This replaces `native_context`, whose associated-data conjunct (the identity layout) no longer holds: the experiment supplies the associated data it computed from the transcript hash. -/
theorem native_context_transcript (associatedData : PqxdhTranscriptAd.AssociatedData)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (pending : pqxdh.PendingServerRegistration) (root : RootOutput) (payload : Option Pqxdh.Bytes)
    (before after : ServerState) (cache : CtxRomAuth.CtxRO.QueryCache)
    (logged : List RawCtxSourceSend.SealContext) (next : CtxRomAuth.CtxRO.QueryCache)
    (response : PqxdhServerRegistrationPublication.Response) (candidate : pqxdh.ServerRegistrationCandidate)
    (passed : PqxdhServerRegistrationPublication.prehash before pending payload = some candidate)
    (supported : (ok (some response, after), (logged, next)) ∈ support
      ((simulateQ (tailImpl setup codec checks)
        (PqxdhServerRegistrationPublication.build (associatedData := associatedData) setup.source pending root payload
          associatedData before)).run ([], cache))) :
    ∃ kernel,
      candidate.beacon_identity_public_key = pending.beacon_identity_public_key ∧
      candidate.server_identity_public_key = before.server.identity ∧
      candidate.server_identity_key_id = before.identityKeyId ∧
      PqxdhRootTableInitialization.initialKernelRun setup.source false root = ok kernel ∧
      logged = [PqxdhServerRegistrationPublication.firstContext candidate associatedData
        (Pqxdh.LE64 candidate.key_id.val ++ payload.getD PqxdhServerRegistrationPublication.registrationWitness)] := by
  rw [PqxdhServerRegistrationPublication.build_prehash_some associatedData setup.source pending root payload associatedData before
    candidate passed] at supported
  obtain ⟨kernel, _, _, initialized, _, _, _, _, log⟩ :=
    PqxdhServerAuthNegativeControl.tail_published associatedData associatedData setup codec checks candidate root
      payload before cache (ok (some response, after), (logged, next)) supported response rfl
  obtain ⟨beacon, server, identifier⟩ := prehash_fields before pending payload candidate passed
  exact ⟨kernel, beacon, server, identifier, initialized, log⟩

/-- An active Beacon on the original source path retains the exact successful output of the actual target Phase1 generation. Writer failure is excluded by the reached phase, not by writer totality. -/
theorem path_generation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (sampled : context ∈ support (contextSample setup codec))
    (initial : PqxdhJointDhExtractFamily.State)
    (current : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks (context.publicValue setup) context.beaconSeed context.seed context.scalar
      (contextState setup context, initial) calls current)
    (active : InitSent current.1) :
    ∃ bytes,
      codec.write1 (PqxdhServerAuthNegativeControl.beaconCandidate setup (context.publicValue setup)
        context.beaconSeed context.oneTime context.keys.1) = some bytes ∧
      context.published = (some bytes, PqxdhServerAuthNegativeControl.publishedBeacon setup
        (context.publicValue setup) context.beaconSeed context.oneTime context.keys.2) ∧
      current.1.beacon = context.published.2 := by
  have retained := PqxdhServerAuthRootProvenance.path_active setup codec checks (context.publicValue setup)
    context.beaconSeed context.seed context.scalar (contextState setup context, initial) current calls path active
  have generated := (PqxdhServerAuthPhase1Generation.context_generated setup codec context sampled).2.2.2.2.2
  rw [PqxdhServerAuthNegativeControl.phase1Run_eq] at generated
  simp only [support_pure, Set.mem_singleton_iff] at generated
  cases written : codec.write1 (PqxdhServerAuthNegativeControl.beaconCandidate setup
    (context.publicValue setup) context.beaconSeed context.oneTime context.keys.1)
  · simp [InitSent, retained, contextState, initialGameState, generated, written, freshBeacon] at active
  · exact ⟨_, rfl, by simpa only [written] using generated, retained⟩

/-- The original successful builder's exact native context remains in the same session's complete final ghost log. Its token and root are the actual consumed values. The candidate is the one that passed the pure pre-hash guard; the Server hashed the transcript of the token's retained Init buffers and that candidate's response fields, the digest stays at that query in the final cache, and the logged context carries the associated data of that digest. This replaces `path_build_context`, whose identity-layout associated-data conjunct no longer holds. -/
theorem path_build_context_transcript (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PqxdhJointGapDh.PublicChallenge) (beaconSeed seed : IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (first final : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks publicValue beaconSeed seed scalar first calls final)
    (index : Nat) (data : Option Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response)
    (before after : GameState KemSK) (roots : QueryLog PqxdhJointDhExtractRoot.RootSpec)
    (built : (⟨.inr (.build index data), some response, before, after, roots⟩ : Call KemSK) ∈ calls) :
    ∃ token candidate digest hashed kernel,
      before.pending index = some token ∧
      token.pending.server_binding = ⟨before.server.server.identity, before.server.identityKeyId⟩ ∧
      candidate.beacon_identity_public_key = token.pending.beacon_identity_public_key ∧
      candidate.server_identity_public_key = before.server.server.identity ∧
      candidate.server_identity_key_id = before.server.identityKeyId ∧
      PqxdhRootTableInitialization.initialKernelRun setup.source false token.root = ok kernel ∧
      PqxdhServerRegistrationPublication.prehash before.server token.pending data = some candidate ∧
      (digest, hashed) ∈ support ((CtxRomAuth.ctxRandomOracle (PqxdhTranscriptAd.query
        (PqxdhTranscriptAd.initOf token.init) (PqxdhTranscriptAd.serverResponse candidate))).run before.ctx) ∧
      final.1.ctx (PqxdhTranscriptAd.query (PqxdhTranscriptAd.initOf token.init)
        (PqxdhTranscriptAd.serverResponse candidate)) = some digest ∧
      (index, PqxdhServerRegistrationPublication.firstContext candidate (PqxdhTranscriptAd.adOf digest)
        (Pqxdh.LE64 candidate.key_id.val ++ data.getD PqxdhServerRegistrationPublication.registrationWitness))
          ∈ final.1.ghost.seals := by
  obtain ⟨earlier, later, prior, next, split, preceding, reached, suffix⟩ :=
    path_occurrence setup codec checks publicValue beaconSeed seed scalar first final calls path _ built
  have source := callback_source setup codec checks publicValue beaconSeed seed scalar _ prior next reached
  obtain ⟨token, candidate, digest, hashed, _, _, logged, cache, found, passed, hashRun, _, _,
      _, _, native, cacheEq, sealed⟩ :=
    PqxdhServerAuthRootInitialization.build_receipt_transcript setup codec checks seed scalar index data
      (before, prior) response (after, next) source
  obtain ⟨kernel, beacon, server, identifier, initialized, log⟩ :=
    native_context_transcript (PqxdhTranscriptAd.adOf digest) setup codec checks token.pending token.root data
      before.server _ hashed logged cache response candidate passed native
  have cached : hashed (PqxdhTranscriptAd.query (PqxdhTranscriptAd.initOf token.init)
      (PqxdhTranscriptAd.serverResponse candidate)) = some digest :=
    QueryImpl.withCaching_run_caches uniformSampleImpl _ before.ctx (digest, hashed) hashRun
  have tailGrown : hashed ≤ cache := tail_run_grows setup codec checks _ ([], hashed) _ native
  have growth := PqxdhServerAuthRootProvenance.path_grows setup codec checks publicValue beaconSeed seed scalar
    (after, next) final later suffix
  refine ⟨token, candidate, digest, hashed, kernel, found,
    native_binding (PqxdhTranscriptAd.adOf digest) setup codec checks token.pending token.root data before.server _
      _ _ response native,
    beacon, server, identifier, initialized, passed, hashRun, ?_, ?_⟩
  · apply growth.ctx
    change after.ctx _ = _
    rw [cacheEq]
    exact tailGrown cached
  · apply growth.seals.subset
    change (index, _) ∈ after.ghost.seals
    rw [sealed, log]
    exact List.mem_append_right _ (by simp)

end BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields.native_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields.native_binding

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields.prehash_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields.prehash_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields.native_context_transcript' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields.native_context_transcript

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields.path_generation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields.path_generation

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields.path_build_context_transcript' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields.path_build_context_transcript
