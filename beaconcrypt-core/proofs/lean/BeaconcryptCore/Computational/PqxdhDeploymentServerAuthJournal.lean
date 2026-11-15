-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthOutcome

/-! The journal of a ServerAuth client in the root-audited singleton execution (CE-8). On every outcome of the occurrence execution, the client's return value is a possible return value of the client program (`execution_client`), and when the client journals its own queries, that journal is the public projection of the private callback receipts of the same run (`execution_log`). The root-audited singleton run is one occurrence execution on its own sampled context (`audited_member`), so on its outcomes the client's return value is a possible return value of the client on the target's published Phase 1 (`audited_client`) and its own journal is the public journal of the outcome (`audited_log`); for every Server seed the generator can draw, its outcome is an outcome of the Server-authentication game of the same client with its return value discarded (`audited_game`). `audited_failure` combines these with `PqxdhDeploymentServerAuthOutcome.game_failure`: a successful finish in the client's own journal, and no session with both an earlier publication of the accepted decoded record and an accept carrying the target's published keys, give the common authentication failure. No security claim is made here. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhJointIdentity
open PqxdhServerAuthRootExecution (Outcome publicCall)
open PqxdhRegistrationR1RootAudit (rootAudited)
open PqxdhDeploymentTranscript (candidateOf acceptedKeys)
open PqxdhDeploymentServerAuthEvent (keysOfBundle)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- On every outcome of the occurrence execution, the client's return value is a possible return value of the client program. -/
theorem execution_client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (client : OracleComp ServerAuthSpec Result)
    (outcome : (Result × PqxdhServerAuthRootOccurrences.Audit KemSK) × PqxdhJointDhExtractFamily.State)
    (member : outcome ∈ support (PqxdhServerAuthRootExecution.execution setup codec checks context client)) :
    outcome.1.1 ∈ support client := by
  have inner : outcome.1 ∈ support ((simulateQ (PqxdhServerAuthRootOccurrences.handler setup codec checks
      (context.publicValue setup) context.beaconSeed) client).run (contextState setup context, [])) := by
    apply support_simulateQ_run'_subset (PqxdhServerAuthRootOccurrences.family setup context.seed context.scalar) _
      PqxdhJointDhExtractFamily.empty
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ member
  apply support_simulateQ_run'_subset (PqxdhServerAuthRootOccurrences.handler setup codec checks
    (context.publicValue setup) context.beaconSeed) client (contextState setup context, [])
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem _ inner

/-- On every outcome of the occurrence execution of a client that journals its own queries, the client's journal is the public projection of the callback receipts. -/
theorem execution_log (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (client : OracleComp ServerAuthSpec Result)
    (outcome : ((Result × QueryLog ServerAuthSpec) × PqxdhServerAuthRootOccurrences.Audit KemSK) ×
      PqxdhJointDhExtractFamily.State)
    (member : outcome ∈ support (PqxdhServerAuthRootExecution.execution setup codec checks context
      (PqxdhServerAuthApiJournal.record client))) :
    outcome.1.1.2 = outcome.1.2.2.map publicCall := by
  have inner : outcome.1 ∈ support ((simulateQ (PqxdhServerAuthRootOccurrences.handler setup codec checks
      (context.publicValue setup) context.beaconSeed) (PqxdhServerAuthApiJournal.record client)).run
        (contextState setup context, [])) := by
    apply support_simulateQ_run'_subset (PqxdhServerAuthRootOccurrences.family setup context.seed context.scalar) _
      PqxdhJointDhExtractFamily.empty
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ member
  have projected := PqxdhServerAuthRootExecution.program_public setup codec checks (context.publicValue setup)
    context.beaconSeed (PqxdhServerAuthApiJournal.record client) (contextState setup context, [])
  have mapped := Set.mem_image_of_mem (fun result : ((Result × QueryLog ServerAuthSpec) ×
      PqxdhServerAuthRootOccurrences.Audit KemSK) => ((result.1, result.2.2.map publicCall), result.2.1)) inner
  rw [← support_map, projected, support_map] at mapped
  obtain ⟨other, otherMember, otherEq⟩ := mapped
  have logged : other.1 ∈ support (PqxdhServerAuthApiJournal.record (PqxdhServerAuthApiJournal.record client)) := by
    apply support_simulateQ_run'_subset (authHandler setup codec checks (context.publicValue setup)
      context.beaconSeed) _ (contextState setup context)
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ otherMember
  have self := OracleComp.withQueryLog_self_log_eq client (v := other.1.1.1) (l₁ := other.1.1.2) (l₂ := other.1.2)
    logged
  have first := congrArg (fun value => value.1.1) otherEq
  have second := congrArg (fun value => value.1.2) otherEq
  simp only [List.map_nil, List.nil_append] at first second
  rw [← first, ← second, self]

/-- A root-audited singleton outcome is one occurrence execution of the client on the target's published Phase 1, on the outcome's own context. -/
theorem audited_member (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (work : Option Pqxdh.Bytes → OracleComp ServerAuthSpec Result)
    (audit : PqxdhRegistrationR1RootAudit.RootAudit KemSK Result)
    (member : audit ∈ support (rootAudited setup codec checks serverSeed work)) :
    audit.2.context.seed = serverSeed ∧
    ∃ result ∈ support (PqxdhServerAuthRootExecution.execution setup codec checks audit.2.context
        (work audit.2.context.published.1)),
      audit.1 = result.1.1 ∧ audit.2.state = result.1.2 ∧ audit.2.primitive = result.2 := by
  simp only [rootAudited, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
  obtain ⟨value, _, oneTime, _, published, _, result, reached, rfl⟩ := member
  exact ⟨rfl, result, reached, rfl, rfl, rfl⟩

/-- On every root-audited singleton outcome, the client's return value is a possible return value of the client on the target's published Phase 1. -/
theorem audited_client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (work : Option Pqxdh.Bytes → OracleComp ServerAuthSpec Result)
    (audit : PqxdhRegistrationR1RootAudit.RootAudit KemSK Result)
    (member : audit ∈ support (rootAudited setup codec checks serverSeed work)) :
    audit.1 ∈ support (work audit.2.context.published.1) := by
  obtain ⟨_, result, reached, same, _, _⟩ := audited_member setup codec checks serverSeed work audit member
  rw [same]
  exact execution_client setup codec checks _ _ result reached

/-- On every root-audited singleton outcome of a client that journals its own queries, that journal is the public journal of the outcome. -/
theorem audited_log (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (client : Option Pqxdh.Bytes → OracleComp ServerAuthSpec Result)
    (audit : PqxdhRegistrationR1RootAudit.RootAudit KemSK (Result × QueryLog ServerAuthSpec))
    (member : audit ∈ support (rootAudited setup codec checks serverSeed
      (fun published => PqxdhServerAuthApiJournal.record (client published)))) :
    audit.1.2 = audit.2.state.2.map publicCall := by
  obtain ⟨_, result, reached, same, state, _⟩ := audited_member setup codec checks serverSeed _ audit member
  rw [same, state]
  exact execution_log setup codec checks _ _ result reached

/-- For every Server seed the generator can draw, a root-audited singleton outcome is an outcome of the Server-authentication game of the same client with its return value discarded. -/
theorem audited_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (seeded : serverSeed ∈ support sampleSeed)
    (work : AuthInput → OracleComp ServerAuthSpec Result) (audit : PqxdhRegistrationR1RootAudit.RootAudit KemSK Result)
    (member : audit ∈ support (rootAudited setup codec checks serverSeed
      (fun published => work ⟨setup.joint.publicKeys serverSeed, setup.serverKeyId, published, none⟩))) :
    audit.2 ∈ support (PqxdhServerAuthRootExecution.game setup codec checks false
      (fun input => (fun _ => ()) <$> work input)) := by
  have ordered : audit.2 ∈ support (PqxdhServerAuthRootObserved.orderedGame setup codec checks false
      (fun input => (fun _ => ()) <$> work input)) := by
    rw [← PqxdhRegistrationR1RootAudit.generated_order setup codec checks work, mem_support_bind_iff]
    exact ⟨serverSeed, seeded, by rw [support_map]; exact Set.mem_image_of_mem _ member⟩
  have same := congrArg (fun measure => measure {true})
    (PqxdhServerAuthRootObserved.observation_order (Result := Bool) setup codec checks false
      (fun input => (fun _ => ()) <$> work input) (fun outcome => @decide (outcome = audit.2) (Classical.propDecidable _)))
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map] at same
  simp only [decide_eq_true_eq] at same
  have positive : Pr{let outcome ← (PqxdhServerAuthRootObserved.orderedGame setup codec checks false
      (fun input => (fun _ => ()) <$> work input))}[outcome = audit.2] ≠ 0 := fun zero =>
    (OracleComp.prEvent_eq_zero_iff _ _).mp zero _ ordered rfl
  rw [← same] at positive
  by_contra absent
  exact positive ((OracleComp.prEvent_eq_zero_iff _ _).mpr fun outcome reached equal => absent (equal ▸ reached))

/-- On a root-audited singleton outcome of a client that journals its own queries, a successful finish in that journal and no session with both an earlier publication of the accepted decoded record and an accept carrying the target's published keys give the common authentication failure. -/
theorem audited_failure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (serverSeed : IdentitySeed)
    (seeded : serverSeed ∈ support sampleSeed) (client : AuthInput → OracleComp ServerAuthSpec Result)
    (audit : PqxdhRegistrationR1RootAudit.RootAudit KemSK (Result × QueryLog ServerAuthSpec))
    (member : audit ∈ support (rootAudited setup codec checks serverSeed
      (fun published => PqxdhServerAuthApiJournal.record
        (client ⟨setup.joint.publicKeys serverSeed, setup.serverKeyId, published, none⟩))))
    (raw payload : Pqxdh.Bytes)
    (finished : (⟨.inr (.finish raw), some payload⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈
      audit.1.2)
    (unmatched : ∀ index, PqxdhServerAuthRecordPublicationEvent.RecordPublished codec index audit.1.2 →
      ∀ acceptRaw candidate keys,
        (⟨.inr (.accept acceptRaw), some index⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈
          audit.1.2 →
        candidateOf codec acceptRaw = some candidate → acceptedKeys setup.source.crypto candidate = some keys →
        keysOfBundle codec audit.2.context.published.1 ≠ some keys) :
    PqxdhServerAuthCommonProbability.decision setup codec checks audit.2 = true := by
  have logEq := audited_log setup codec checks serverSeed _ audit member
  have game := audited_game setup codec checks serverSeed seeded
    (fun input => PqxdhServerAuthApiJournal.record (client input)) audit member
  rw [logEq] at finished unmatched
  have failure := PqxdhDeploymentServerAuthOutcome.game_failure setup codec checks phase1 _ audit.2 game raw payload
    finished unmatched
  exact @decide_eq_true _ (Classical.propDecidable _) failure

/-! ## The transcript failure -/

/-- Under the complete source agreement at a session index and outside a collision of the final BLAKE2b cache, the public journal has an accept of that session whose raw candidate the source attached verification accepts with the target's keys, a successful build of the same session and a successful finish, and the public registration transcript of the accept bytes and the build response (`PqxdhDeploymentCompile.publicTranscript`) is the transcript of the target's written Phase 1 candidate and the decoded finish input: both roles hashed one transcript (`PqxdhServerAuthRootCommon.Agreement`), the accept bytes read back to the Server's retained Init buffers, and the build response reads back to the Server's candidate response fields. Premise: the approved Phase 2 read-back contract. -/
theorem agreement_public (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (result : Outcome KemSK) (index : Nat)
    (agreement : PqxdhServerAuthRootCommon.Agreement setup codec checks result index)
    (collisionFree : ¬ CacheHasCollision result.state.1.ctx) :
    ∃ acceptRaw candidate data reply raw payload response,
      (⟨.inr (.accept acceptRaw), some index⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈
        result.state.2.map publicCall ∧
      candidateOf codec acceptRaw = some candidate ∧
      acceptedKeys setup.source.crypto candidate = some (PqxdhDeploymentServerAuthOutcome.targetKeys setup result.context) ∧
      (⟨.inr (.build index data), some reply⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈
        result.state.2.map publicCall ∧
      (⟨.inr (.finish raw), some payload⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈
        result.state.2.map publicCall ∧
      responseOf codec raw = some response ∧
      PqxdhDeploymentCompile.publicTranscript codec acceptRaw reply.serialized =
        some (PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf (PqxdhServerAuthNegativeControl.beaconCandidate setup
          (result.context.publicValue setup) result.context.beaconSeed result.context.oneTime result.context.keys.1))
          response) := by
  obtain ⟨data, reply, serverBefore, serverAfter, serverRoots, raw, payload, beaconBefore, beaconAfter, beaconRoots,
    _, _, built, finished, _, _, _, _, token, candidate, digest, hashed, published, kernel, logged, cache, acceptCall,
    acceptRaw, input, consumed, init, response, _, _, _, _, _, acceptMember, acceptEq, prefixed, _, tokenInit, decoded,
    _, sessionEq, _, _, passed, _, _, buildRun, _, _, _, _, _, _, _, _, _, initEq, responseEq, _, _, _, serverFinal,
    beaconFinal⟩ := agreement
  have native : (some (PqxdhServerStaticDhSource.concreteInputs setup.joint result.context.seed input), consumed) ∈
      support ((PqxdhServerAuthNative.nativePrefix setup codec checks result.context.seed acceptRaw).run
        acceptCall.before.server.consumed) := by
    rw [PqxdhServerAuthNative.native_prefix, StateT.run_map, support_map]
    exact ⟨(some input, consumed), prefixed, rfl⟩
  obtain ⟨candidateEq, acceptedEq⟩ := PqxdhRegistrationJointRawSignatures.prefix_candidate setup codec checks
    result.context.seed acceptRaw _ consumed _ native
  have keysEq : acceptedKeys setup.source.crypto input.verified.candidate =
      some (PqxdhDeploymentServerAuthOutcome.targetKeys setup result.context) := by
    have prekey : input.verified.keys.prekey = (result.context.publicValue setup).prekey :=
      congrArg PqxdhServerAuthRootSession.Session.prekey sessionEq
    have oneTime : input.verified.keys.oneTime = setup.dh.publicKey result.context.oneTime :=
      congrArg PqxdhServerAuthRootSession.Session.oneTime sessionEq
    have pqKey : input.verified.keys.pqKey = result.context.keys.1 :=
      congrArg PqxdhServerAuthRootSession.Session.pqKey sessionEq
    have initKex : PqxdhServerAuthPhase1Projection.unsigned input.verified.identity input.verified.keys =
        PqxdhServerAuthPhase1Projection.unsigned (setup.joint.publicKeys result.context.beaconSeed).ed25519
          (PqxdhServerAuthPhase1Identity.contextMaterial setup result.context).keyTuple :=
      congrArg PqxdhServerAuthRootSession.Session.initKex sessionEq
    have identityBytes := congrArg (fun kex : beaconcrypt_core.pqxdh.InitKex => PqxdhRefinement.absBytes kex.identity_key) initKex
    simp only [(PqxdhServerAuthPhase1Projection.unsigned_bytes _ _).1] at identityBytes
    have identity : input.verified.identity = (setup.joint.publicKeys result.context.beaconSeed).ed25519 := by
      have parsed := congrArg PqxdhEd25519EufCma.parseIdentity identityBytes
      simpa using parsed
    have keys : input.verified.keys = ⟨(result.context.publicValue setup).prekey,
        setup.dh.publicKey result.context.oneTime, result.context.keys.1⟩ := by
      rw [← prekey, ← oneTime, ← pqKey]
    simp only [PqxdhServerStaticDhSource.concreteInputs] at acceptedEq
    change PqxdhJointPhase1Reports.sourceAccept (fun publicKey => setup.source.crypto.verify publicKey.toList)
      input.verified.candidate = _
    rw [acceptedEq, identity, keys]
    rfl
  have serverInit : PqxdhDeploymentCompile.publicInit codec acceptRaw =
      some (PqxdhTranscriptAd.initOf token.init) := by
    obtain ⟨read, identityRead, preRead, oneRead, pqRead⟩ := decoded
    rw [tokenInit]
    simp only [PqxdhDeploymentCompile.publicInit, read, identityRead, preRead, oneRead, pqRead, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]
  have run := buildRun
  rw [PqxdhServerRegistrationPublication.build_prehash_some (associatedData := PqxdhTranscriptAd.adOf digest)
    setup.source _ _ data _ serverBefore.server candidate passed] at run
  obtain ⟨_, _, frameBytes, _, _, _, _, written, _⟩ := PqxdhServerAuthNegativeControl.tail_published
    (PqxdhTranscriptAd.adOf digest) (PqxdhTranscriptAd.adOf digest) setup codec checks candidate token.root data
    serverBefore.server hashed _ run reply rfl
  obtain ⟨decodedReply, readReply, ciphertextRead, ephemeralRead, serverRead, assignedRead, _⟩ :=
    phase2 _ _ written
  have serverReply : responseOf codec reply.serialized = some (PqxdhTranscriptAd.serverResponse candidate) := by
    simp only [responseOf, readReply, ciphertextRead, ephemeralRead, serverRead, assignedRead, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]
    rfl
  have same := PqxdhTranscriptAd.transcript_eq_of_ad_eq result.state.1.ctx serverFinal beaconFinal rfl collisionFree
  refine ⟨acceptRaw, input.verified.candidate, data, reply, raw, payload, response,
    List.mem_map.mpr ⟨acceptCall, acceptMember, acceptEq⟩, candidateEq, keysEq, List.mem_map.mpr ⟨_, built, rfl⟩,
    List.mem_map.mpr ⟨_, finished, rfl⟩, responseEq, ?_⟩
  rw [← initEq, ← same]
  simp only [PqxdhDeploymentCompile.publicTranscript, serverInit, serverReply, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def]

/-- Public transcript failure of the common event: on every outcome of the Server-authentication game, a successful finish in the public journal and, for every session with an earlier publication of the accepted decoded record (`RecordPublished`) and an accept carrying the published keys of the target, a public registration transcript of the accept bytes and every successful build response of that session that differs from the public registration transcript of the target's published Phase 1 bytes and every successful finish input, give a failure of the common event or a collision of the final BLAKE2b cache. Premises: the approved Phase 1 and Phase 2 read-back contracts. -/
theorem game_transcript_failure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (adversary : Adversary) (result : Outcome KemSK)
    (supported : result ∈ support (PqxdhServerAuthRootExecution.game setup codec checks false adversary))
    (raw payload : Pqxdh.Bytes)
    (finished : (⟨.inr (.finish raw), some payload⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈
      result.state.2.map publicCall)
    (untranscripted : ∀ index, PqxdhServerAuthRecordPublicationEvent.RecordPublished codec index
        (result.state.2.map publicCall) →
      ∀ acceptRaw candidate keys,
        (⟨.inr (.accept acceptRaw), some index⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈
          result.state.2.map publicCall →
        candidateOf codec acceptRaw = some candidate → acceptedKeys setup.source.crypto candidate = some keys →
        keysOfBundle codec result.context.published.1 = some keys →
        ∀ data reply finishRaw finishPayload bundle transcript,
          (⟨.inr (.build index data), some reply⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈
            result.state.2.map publicCall →
          (⟨.inr (.finish finishRaw), some finishPayload⟩ :
            (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈ result.state.2.map publicCall →
          result.context.published.1 = some bundle →
          PqxdhDeploymentCompile.publicTranscript codec acceptRaw reply.serialized = some transcript →
          PqxdhDeploymentCompile.publicTranscript codec bundle finishRaw ≠ some transcript) :
    PqxdhServerAuthCommonEvent.FailureOrCollision setup codec checks result := by
  by_cases collided : CacheHasCollision result.state.1.ctx
  · exact Or.inr collided
  refine Or.inl ⟨PqxdhDeploymentServerAuthOutcome.game_accepted setup codec checks adversary result supported raw
    payload finished, ?_⟩
  rintro ⟨index, ⟨generation, _, agreement⟩, published⟩
  obtain ⟨acceptRaw, candidate, data, reply, finishRaw, finishPayload, response, acceptMember, candidateEq, keysEq,
    buildMember, finishMember, responseEq, serverTranscript⟩ :=
    agreement_public setup codec checks phase2 result index agreement collided
  have generated := generation
  obtain ⟨_, _, bytes, written, publishedEq⟩ := generated
  obtain ⟨reader, read, identityRead, pqRead, preRead, oneRead⟩ := phase1 _ bytes written
  have beaconTranscript : PqxdhDeploymentCompile.publicTranscript codec bytes finishRaw =
      some (PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf (PqxdhServerAuthNegativeControl.beaconCandidate setup
        (result.context.publicValue setup) result.context.beaconSeed result.context.oneTime result.context.keys.1))
        response) := by
    simp only [PqxdhDeploymentCompile.publicTranscript, PqxdhDeploymentCompile.publicInit, read, identityRead,
      pqRead, preRead, oneRead, responseEq, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  exact untranscripted index published acceptRaw candidate _ acceptMember candidateEq keysEq
    (PqxdhDeploymentServerAuthOutcome.generation_keys setup codec phase1 result generation) data reply finishRaw
    finishPayload bytes _ buildMember finishMember (by rw [publishedEq]) serverTranscript beaconTranscript

/-- On a root-audited singleton outcome of a client that journals its own queries, a successful finish in that journal and, for every session with an earlier publication of the accepted decoded record and an accept carrying the target's published keys, a public registration transcript of the accept bytes and every successful build response of that session that differs from the public registration transcript of the target's published Phase 1 and every successful finish input, give the failure-or-collision decision. Premises: the approved Phase 1 and Phase 2 read-back contracts. -/
theorem audited_transcript_failure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (serverSeed : IdentitySeed)
    (seeded : serverSeed ∈ support sampleSeed) (client : AuthInput → OracleComp ServerAuthSpec Result)
    (audit : PqxdhRegistrationR1RootAudit.RootAudit KemSK (Result × QueryLog ServerAuthSpec))
    (member : audit ∈ support (rootAudited setup codec checks serverSeed
      (fun published => PqxdhServerAuthApiJournal.record
        (client ⟨setup.joint.publicKeys serverSeed, setup.serverKeyId, published, none⟩))))
    (raw payload : Pqxdh.Bytes)
    (finished : (⟨.inr (.finish raw), some payload⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈
      audit.1.2)
    (untranscripted : ∀ index, PqxdhServerAuthRecordPublicationEvent.RecordPublished codec index audit.1.2 →
      ∀ acceptRaw candidate keys,
        (⟨.inr (.accept acceptRaw), some index⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈
          audit.1.2 →
        candidateOf codec acceptRaw = some candidate → acceptedKeys setup.source.crypto candidate = some keys →
        keysOfBundle codec audit.2.context.published.1 = some keys →
        ∀ data reply finishRaw finishPayload bundle transcript,
          (⟨.inr (.build index data), some reply⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈
            audit.1.2 →
          (⟨.inr (.finish finishRaw), some finishPayload⟩ :
            (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈ audit.1.2 →
          audit.2.context.published.1 = some bundle →
          PqxdhDeploymentCompile.publicTranscript codec acceptRaw reply.serialized = some transcript →
          PqxdhDeploymentCompile.publicTranscript codec bundle finishRaw ≠ some transcript) :
    PqxdhServerAuthCommonProbability.collisionDecision setup codec checks audit.2 = true := by
  have logEq := audited_log setup codec checks serverSeed _ audit member
  have game := audited_game setup codec checks serverSeed seeded
    (fun input => PqxdhServerAuthApiJournal.record (client input)) audit member
  rw [logEq] at finished untranscripted
  have failure := game_transcript_failure setup codec checks phase1 phase2 _ audit.2 game raw payload finished
    untranscripted
  exact @decide_eq_true _ (Classical.propDecidable _) failure

end BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.execution_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.execution_client

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.execution_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.execution_log

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_member

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_client

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_log

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_game

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_failure

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.agreement_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.agreement_public

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.game_transcript_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.game_transcript_failure

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_transcript_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthJournal.audited_transcript_failure
