-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuth

/-! The public transcript-match route of CE-A1 (CE-8), the probability side of the ten-field session agreement (`PqxdhDeploymentSessionAgreement`). Both honest roles compute the record associated data `AD151 = context87 ‖ BLAKE2b-512(T)` from the 2638-byte registration transcript `T`, so a pin-matching session may carry a transcript, and hence an associated data, different from the accepted Beacon's. `TranscriptMatchAt` strengthens `PqxdhDeploymentServerAuth.PinnedMatchAt` by a transcript conjunct read from public bytes only: a successful build of the same session returned a response whose public registration transcript with the matching accept bytes (`PqxdhDeploymentCompile.publicTranscript`) is the public registration transcript of the owner's first published bundle and the accepted raw input. `A1NoTranscriptMatch` is `A1NoPinnedMatch` with this matching; it contains `A1NoPinnedMatch` on every outcome (`noPinnedMatch_noTranscriptMatch`). On the support of the experiment it is the A1 transcript failure on the registration view (`A1TranscriptAt`, from `PqxdhDeploymentServerAuthTrack.Untranscripted`; `noTranscriptMatch_transcriptAt`, with `PqxdhDeploymentServerAuth.build_pin`). Per creation index `c`, the A1 transcript failure is at most the failure-or-collision probability of `R_c` in the ordered Server-authentication game (`transcript_le_ordered`, from `PqxdhDeploymentServerAuthChain.seed_bound_transcript`): outside a collision of the final BLAKE2b cache, the common session's two roles hashed one transcript, and the read-back contracts equal it to the public transcripts of the journal (`PqxdhDeploymentServerAuthJournal.audited_transcript_failure`). `PqxdhServerAuthCommonAuthentication.collision_authentication_with_resources` bounds that event by exactly `serverAuthBound` (whose last summand is the transcript-hash collision term), so `a1_transcript_sum` has the right-hand side of `PqxdhDeploymentServerAuth.a1_sum` verbatim. No new assumption or contract: the premises are those of `a1_sum`. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTranscript
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthSourceCosts
open PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh PqxdhServerAuthAssumptions
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhEd25519EufCma CtxNonceAeadIntCtxt
open PqxdhJointIdentity
open PqxdhDeploymentInterface (FreshBounds ModeSpec Mode Budget)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentCompile (Local)
open PqxdhDeploymentCompileSecrecy (compileFull mergeFull)
open PqxdhDeploymentServerAuthEvent (SourceEntry Reg regsOf regsOfSource summarizeReg accepted bundleOfReg publishedKeys
  protectedBinding)
open PqxdhDeploymentServerAuthChain (seedBinding seedInput)
open PqxdhDeploymentServerAuthTrack (TranscriptMatchedAt Untranscripted)
open PqxdhDeploymentServerAuth (reduction serverAuthAdversary serverAuthBound ReductionCaps PinnedMatchAt
  A1NoPinnedMatch probEvent_bind_le owners_foldl compiled_owners)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X A : Type}

/-! ## The public transcript match -/

/-- Session `session` transcript-matches owner `owner` before its acceptance with the pin `pin`: the pinned match (`PqxdhDeploymentServerAuth.PinnedMatchAt`), and a successful build of the same session before the acceptance returned a response whose public registration transcript with the matching accept bytes is the public registration transcript of the owner's first published bundle and the accepted raw input (`PqxdhDeploymentCompile.publicTranscript`). Only public bytes, the public attached verification of `Pqxdh.Crypto`, the codec readers and the parsers are used. -/
def TranscriptMatchAt (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (owner session : Nat)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (before : List Reg) (raw : Pqxdh.Bytes) : Prop :=
  ∃ acceptRaw candidate keys payload reply record transcriptPayload transcriptReply bundle transcript,
    Reg.accept acceptRaw (some session) ∈ before ∧ PqxdhDeploymentTranscript.candidateOf codec acceptRaw = some candidate ∧
    PqxdhDeploymentTranscript.acceptedKeys crypto candidate = some keys ∧
    publishedKeys codec before owner = some keys ∧
    Reg.build session payload (some reply) ∈ before ∧
    (codec.read2 reply.serialized).bind codec.serverIdentity = some pin ∧
    PqxdhServerAuthRecordPublicationEvent.frame codec raw = some record ∧
    PqxdhServerAuthRecordPublicationEvent.frame codec reply.serialized = some record ∧
    Reg.build session transcriptPayload (some transcriptReply) ∈ before ∧ bundleOfReg before owner = some bundle ∧
    PqxdhDeploymentCompile.publicTranscript codec acceptRaw transcriptReply.serialized = some transcript ∧
    PqxdhDeploymentCompile.publicTranscript codec bundle raw = some transcript

/-- Some session transcript-matches the owner before its acceptance with the pin. -/
def TranscriptMatch (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (owner : Nat)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (before : List Reg) (raw : Pqxdh.Bytes) : Prop :=
  ∃ session, TranscriptMatchAt crypto codec owner session pin before raw

/-- A transcript match is a pinned match. -/
theorem transcriptMatch_pinned (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (owner session : Nat)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (before : List Reg) (raw : Pqxdh.Bytes)
    (matched : TranscriptMatchAt crypto codec owner session pin before raw) :
    PinnedMatchAt crypto codec owner session pin before raw := by
  obtain ⟨acceptRaw, candidate, keys, payload, reply, record, _, _, _, _, acceptMember, candidateEq, keysEq,
    publishedEq, buildMember, pinned, frameRaw, frameReply, _⟩ := matched
  exact ⟨acceptRaw, candidate, keys, payload, reply, record, acceptMember, candidateEq, keysEq, publishedEq,
    buildMember, pinned, frameRaw, frameReply⟩

/-- CE-A1 on runs with `NoBundleFailure_c` with the transcript matching: a Server was constructed; owner `c` has no rejected bundle call in Fresh in the whole run, accepted, was created with the protected binding before its acceptance, and no session transcript-matches it with the protected binding's pin. -/
def A1NoTranscriptMatch (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧
    PqxdhDeploymentTranscript.NoBundleFailureAt final.1.transcript c ∧
    ∃ before raw, accepted c (regsOf final.1.transcript) = some (before, raw) ∧
      (summarizeReg before).owners[c]? = some (protectedBinding setup created) ∧
      ¬ TranscriptMatch setup.source.crypto codec c (protectedBinding setup created).1 before raw

/-- On every outcome, CE-A1 with the pinned matching is contained in CE-A1 with the transcript matching: a transcript match is a pinned match. -/
theorem noPinnedMatch_noTranscriptMatch (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (event : A1NoPinnedMatch setup codec c outcome) : A1NoTranscriptMatch setup codec c outcome := by
  obtain ⟨created, output, final, found, noFailure, before, raw, acceptedEq, bound, unpinned⟩ := event
  exact ⟨created, output, final, found, noFailure, before, raw, acceptedEq, bound, fun ⟨session, matched⟩ =>
    unpinned ⟨session, transcriptMatch_pinned _ codec c session _ before raw matched⟩⟩

/-- CE-A1's transcript event at creation index `c`: a Server was constructed and owner `c`, created with the protected binding, accepted with no transcript-matching session and no rejected bundle call in Fresh before its acceptance. -/
def A1TranscriptAt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧
    Untranscripted setup.source.crypto codec (protectedBinding setup created) c (regsOf final.1.transcript)

/-- On every outcome of the experiment, CE-A1 with the transcript matching is the A1 transcript failure: a transcript-matching session of the registration view matches with the pin of the protected binding (`PqxdhDeploymentServerAuth.build_pin`), and no rejected bundle in the whole run gives none before the acceptance. Premise: the approved Phase 2 read-back contract. -/
theorem noTranscriptMatch_transcriptAt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) (c : Nat)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds
      mode adversary).run runtime))
    (event : A1NoTranscriptMatch setup codec c outcome) : A1TranscriptAt setup codec c outcome := by
  obtain ⟨created, output, final, found, noFailure, before, raw, acceptedEq, bound, unmatched⟩ := event
  have prefixed := PqxdhDeploymentServerAuthEvent.accepted_prefix c _ before raw acceptedEq
  obtain ⟨rest, restEq⟩ := id prefixed
  refine ⟨created, output, final, found, before, raw, acceptedEq, bound, ?_, fun ⟨session, matched⟩ => unmatched ?_⟩
  · cases failed : (summarizeReg before).failures c with
    | false => rfl
    | true =>
        have later := PqxdhDeploymentServerAuthEvent.failures_append before rest c failed
        rw [restEq, ← PqxdhDeploymentServerAuthEvent.summarize_regs] at later
        unfold PqxdhDeploymentTranscript.NoBundleFailureAt at noFailure
        rw [noFailure] at later
        cases later
  · obtain ⟨acceptRaw, candidate, keys, payload, reply, record, transcriptPayload, transcriptReply, bundle, transcript,
      acceptMember, candidateEq, keysEq, publishedEq, buildMember, frameRaw, frameReply, transcriptMember, bundleEq,
      serverTranscript, beaconTranscript⟩ := matched
    have built := PqxdhDeploymentServerAuth.build_entry final.1.transcript session payload reply
      (prefixed.subset buildMember)
    exact ⟨session, acceptRaw, candidate, keys, payload, reply, record, transcriptPayload, transcriptReply, bundle,
      transcript, acceptMember, candidateEq, keysEq, publishedEq, buildMember,
      PqxdhDeploymentServerAuth.build_pin setup codec checks route ensureInit identityIndex phase2 bounds mode adversary
        runtime outcome supported created output final found session payload reply built,
      frameRaw, frameReply, transcriptMember, bundleEq, serverTranscript, beaconTranscript⟩

/-- The CE-A1 transcript event at a constructed Server is the A1 transcript failure on the transcript of the compiled program's run. -/
theorem transcriptAt_merge (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit)
    (result : ((X × Ledger) × Local) × PqxdhRegistrationSchedule.State KemSK) (runtime : A) :
    A1TranscriptAt setup codec c (mergeFull (some (created, result), runtime)) ↔
      Untranscripted setup.source.crypto codec (protectedBinding setup created) c (regsOf result.1.1.2.transcript) := by
  constructor
  · rintro ⟨created', output, final, found, failure⟩
    simp only [mergeFull, Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, _, rfl⟩ := found
    exact failure
  · intro failure
    exact ⟨_, _, _, rfl, failure⟩

/-- The CE-A1 transcript event at creation index `c`, as a decision. -/
noncomputable def transcriptDecision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Bool :=
  @decide (A1TranscriptAt setup codec c outcome) (Classical.propDecidable _)

/-! ## One creation index -/

/-- Per creation index `c`: the probability of the CE-A1 transcript event at `c` in the common deployment experiment, for every identity index of the constructed Server and every initialization runtime, is at most the failure-or-collision probability of `R_c` in the ordered Server-authentication game. Premises: the approved Phase 1 and Phase 2 read-back contracts. -/
theorem transcript_le_ordered (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) (c : Nat) :
    Pr{let outcome ← (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime}[A1TranscriptAt setup codec c outcome] ≤
    Pr{let result ← (PqxdhServerAuthRootObserved.orderedGame setup codec checks false
        (serverAuthAdversary (KemSK := KemSK) setup codec route bounds mode adversary c))}[PqxdhServerAuthCommonProbability.collisionDecision setup codec checks result = true] := by
  rw [← PqxdhDeploymentCompileSecrecy.compile_full_game setup codec checks route ensureInit identityIndex phase1 phase2
    bounds mode adversary runtime, prEvent_map]
  rw [show serverAuthAdversary (KemSK := KemSK) setup codec route bounds mode adversary c =
      fun input => (fun _ => ()) <$> reduction (KemSK := KemSK) setup codec route bounds mode adversary c input from rfl,
    ← PqxdhRegistrationR1RootAudit.generated_order setup codec checks
      (reduction (KemSK := KemSK) setup codec route bounds mode adversary c)]
  simp only [PqxdhRegistrationJointInitializedSchedule.native, PqxdhLiveServerConstruction.construct, StateT.run]
  rw [bind_assoc (ensureInit runtime)]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun ready _ => ?_
  cases ready.1 with
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [pure_bind]
      refine le_of_eq_of_le ((OracleComp.prEvent_eq_zero_iff _ _).mpr ?_) zero_le
      intro outcome member
      simp only [support_pure, Set.mem_singleton_iff] at member
      subst member
      simp [mergeFull, A1TranscriptAt]
  | true =>
      simp only [ite_true, bind_map_left]
      refine probEvent_bind_le _ _ _ _ _ fun seed seeded => ?_
      rw [prEvent_map, prEvent_map]
      have bound := PqxdhDeploymentServerAuthChain.seed_bound_transcript setup codec checks phase1 phase2 route bounds mode
        adversary c seed seeded identityIndex .generated
      refine le_of_eq_of_le ?_ bound
      refine prEvent_congr_of_support _ _ _ fun result _ => ?_
      exact transcriptAt_merge setup codec c _ result _

/-- The CE-A1 transcript event at one creation index `c` is at most the Server-authentication bound of `R_c` (`serverAuthBound`, whose last summand is the transcript-hash collision term), with the bills of every reduction in that bound: `transcript_le_ordered` and `PqxdhServerAuthCommonAuthentication.collision_authentication_with_resources`. Premises: those of `PqxdhDeploymentServerAuth.a1_bound`. -/
theorem transcript_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) (caps : KemCaps)
    (bounded : KemBound setup caps) (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : Nat) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) (c : Nat)
    (qCoin Q qH qHash qTotal qFinish : Nat)
    (reductionCaps : ReductionCaps (reduction (KemSK := KemSK) setup codec route bounds mode adversary c)
      qCoin Q qH qHash qTotal qFinish)
    (fallback : ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[transcriptDecision setup codec c <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime]
        {true}).toReal ≤
      serverAuthBound setup codec checks caps (serverAuthAdversary setup codec route bounds mode adversary c)
        qCoin Q qH qHash fallback signatureFallback ∧
    PqxdhServerAuthCommonAuthentication.ReductionBills setup codec checks caps
      (serverAuthAdversary setup codec route bounds mode adversary c) qCoin Q qH qHash qTotal qFinish fallback
      signatureFallback := by
  set work := reduction (KemSK := KemSK) setup codec route bounds mode adversary c
  have sa := PqxdhServerAuthCommonAuthentication.collision_authentication_with_resources setup codec checks caps bounded
    (serverAuthAdversary setup codec route bounds mode adversary c) qCoin Q qH qHash
    ((PqxdhRegistrationR1Authentication.budget_iff work Q qH qHash).mpr reductionCaps.source)
    (fun input => (PqxdhRegistrationR1Authentication.unit_queries work input _ _).mpr (reductionCaps.coins input))
    law spread correct adapter writable phase2 frameBack qTotal qFinish
    (fun input => by
      simpa only [serverAuthAdversary, PqxdhRegistrationR1Authentication.unitWork, IsTotalQueryBound,
        isQueryBound_map_iff] using reductionCaps.total input)
    (fun input => (PqxdhRegistrationR1Authentication.unit_queries work input _ _).mpr (reductionCaps.finish input))
    fallback signatureFallback
  refine ⟨?_, sa.2⟩
  have ordered := transcript_le_ordered setup codec checks route ensureInit identityIndex phase1 phase2 bounds mode adversary
    runtime c
  have left : 𝒟[transcriptDecision setup codec c <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime]
        {true} = Pr{let outcome ← ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run
        runtime)}[A1TranscriptAt setup codec c outcome] := by
    classical
    exact UniformTargetSelection.chance_eq _ _
  have right : 𝒟[PqxdhServerAuthCommonProbability.collisionDecision setup codec checks <$>
      PqxdhServerAuthRootObserved.orderedGame setup codec checks false
        (serverAuthAdversary setup codec route bounds mode adversary c)] {true} =
      Pr{let result ← (PqxdhServerAuthRootObserved.orderedGame setup codec checks false
          (serverAuthAdversary setup codec route bounds mode adversary c))}[PqxdhServerAuthCommonProbability.collisionDecision setup codec checks result = true] := by
    rw [← prEvent_eq_evalDist_singleton _ true, prEvent_map]
  have finite : 𝒟[PqxdhServerAuthCommonProbability.collisionDecision setup codec checks <$>
      PqxdhServerAuthRootObserved.orderedGame setup codec checks false
        (serverAuthAdversary setup codec route bounds mode adversary c)] {true} ≠ ⊤ := by
    rw [← prEvent_eq_evalDist_singleton _ true]
    exact prEvent_ne_top _
  rw [left]
  rw [← right] at ordered
  exact (ENNReal.toReal_mono finite ordered).trans sa.1

/-! ## All creation indices -/

/-- Owner `c` of an A1 transcript failure has a binding in the summary of the view. -/
theorem untranscripted_created (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (binding : PqxdhBeaconPhase2Preparation.Word32 × Std.U64) (c : Nat) (regs : List Reg)
    (failure : Untranscripted crypto codec binding c regs) : c < (summarizeReg regs).owners.length := by
  obtain ⟨before, raw, found, bound, _, _⟩ := failure
  have below : c < (summarizeReg before).owners.length := (List.getElem?_eq_some_iff.mp bound).1
  obtain ⟨rest, rfl⟩ := PqxdhDeploymentServerAuthEvent.accepted_prefix c regs before raw found
  rw [PqxdhDeploymentServerAuthEvent.summarizeReg_append]
  exact lt_of_lt_of_le below (owners_foldl _ rest)

/-- On every outcome of the deployment experiment of a budget-respecting adversary, the CE-A1 transcript event can occur only at a creation index below `qCreate`. -/
theorem transcript_range (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (member : outcome ∈ support
      ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime))
    (c : Nat) (event : A1TranscriptAt setup codec c outcome) : c < budget.create := by
  rw [← PqxdhDeploymentCompileSecrecy.compile_full_game setup codec checks route ensureInit identityIndex phase1 phase2
    bounds mode adversary runtime, support_map] at member
  obtain ⟨native, nativeMember, rfl⟩ := member
  simp only [PqxdhRegistrationJointInitializedSchedule.native, StateT.run, mem_support_bind_iff] at nativeMember
  obtain ⟨⟨born, after⟩, _, nativeMember⟩ := nativeMember
  cases born with
  | none =>
      simp only [support_pure, Set.mem_singleton_iff] at nativeMember
      subst nativeMember
      obtain ⟨_, _, _, found, _⟩ := event
      simp [mergeFull] at found
  | some created =>
      simp only [support_map, Set.mem_image] at nativeMember
      obtain ⟨result, resultMember, rfl⟩ := nativeMember
      have failure := (transcriptAt_merge setup codec c _ result after).mp event
      have created' := untranscripted_created _ codec _ c _ failure
      rw [← PqxdhDeploymentServerAuthEvent.summarize_regs] at created'
      have program : result.1 ∈ support (compileFull setup codec route bounds mode adversary) := by
        apply support_simulateQ_run'_subset (PqxdhRegistrationJointRevealSchedule.native setup codec checks created.seed)
          _ (PqxdhRegistrationSchedule.initial created)
        rw [StateT.run'_eq, support_map]
        exact Set.mem_image_of_mem _ resultMember
      exact lt_of_lt_of_le created' (compiled_owners setup codec route bounds mode adversary budget respects _ program)

/-- The CE-A1 transcript event over all Beacons: in the common deployment experiment of a budget-respecting adversary, the probability that some owner accepted with no transcript-matching session is at most the sum over the `qCreate` creation indices `c` of the Server-authentication bound of `R_c`, with every reduction's bills. The premises and the right-hand side are those of `PqxdhDeploymentServerAuth.a1_sum`. -/
theorem a1_transcript_sum (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) (caps : KemCaps)
    (bounded : KemBound setup caps) (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : Nat) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (qCoin Q qH qHash qTotal qFinish : Nat)
    (reductionCaps : ∀ c, ReductionCaps (reduction (KemSK := KemSK) setup codec route bounds mode adversary c)
      qCoin Q qH qHash qTotal qFinish)
    (fallback : ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[(fun outcome => @decide (∃ c, A1TranscriptAt setup codec c outcome) (Classical.propDecidable _)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime]
        {true}).toReal ≤
      ∑ c : Fin budget.create, serverAuthBound setup codec checks caps
        (serverAuthAdversary setup codec route bounds mode adversary c) qCoin Q qH qHash fallback signatureFallback ∧
    ∀ c, PqxdhServerAuthCommonAuthentication.ReductionBills setup codec checks caps
      (serverAuthAdversary setup codec route bounds mode adversary c) qCoin Q qH qHash qTotal qFinish fallback
      signatureFallback := by
  have each := fun c => transcript_bound setup codec checks caps bounded route ensureInit identityIndex phase1 phase2 frameBack
    writable law spread correct adapter bounds mode adversary runtime c qCoin Q qH qHash qTotal qFinish
    (reductionCaps c) fallback signatureFallback
  refine ⟨?_, fun c => (each c).2⟩
  set run := (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run
    runtime with runEq
  have chance : ∀ c, 𝒟[transcriptDecision setup codec c <$> run] {true} = Pr{let outcome ← run}[A1TranscriptAt setup codec c outcome] := by
    intro c
    classical
    exact UniformTargetSelection.chance_eq _ _
  have total : 𝒟[(fun outcome => @decide (∃ c, A1TranscriptAt setup codec c outcome) (Classical.propDecidable _)) <$> run]
      {true} = Pr{let outcome ← run}[∃ c, A1TranscriptAt setup codec c outcome] := by
    classical
    exact UniformTargetSelection.chance_eq _ _
  have ranged : Pr{let outcome ← run}[∃ c, A1TranscriptAt setup codec c outcome] =
      Pr{let outcome ← run}[∃ c ∈ (Finset.univ : Finset (Fin budget.create)), A1TranscriptAt setup codec c.val outcome] := by
    refine prEvent_congr_of_support _ _ _ fun outcome member =>
      ⟨fun ⟨c, event⟩ => ?_, fun ⟨c, _, event⟩ => ⟨c.val, event⟩⟩
    exact ⟨⟨c, transcript_range setup codec checks route ensureInit identityIndex phase1 phase2 bounds mode adversary budget
      respects runtime outcome member c event⟩, Finset.mem_univ _, event⟩
  have union := prEvent_exists_finset_le (Finset.univ : Finset (Fin budget.create)) run
    (fun c outcome => A1TranscriptAt setup codec c.val outcome)
  have finite : ∑ c : Fin budget.create, Pr{let outcome ← run}[A1TranscriptAt setup codec c.val outcome] ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun c _ => (prEvent_ne_top _)
  rw [total, ranged]
  refine (ENNReal.toReal_mono finite union).trans ?_
  rw [ENNReal.toReal_sum fun c _ => (prEvent_ne_top _)]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [← chance c.val]
  exact (each c.val).1

end BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTranscript

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTranscript.transcriptMatch_pinned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTranscript.transcriptMatch_pinned

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTranscript.noPinnedMatch_noTranscriptMatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTranscript.noPinnedMatch_noTranscriptMatch

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTranscript.noTranscriptMatch_transcriptAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTranscript.noTranscriptMatch_transcriptAt

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTranscript.transcriptAt_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTranscript.transcriptAt_merge

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTranscript.transcript_le_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTranscript.transcript_le_ordered

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTranscript.transcript_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTranscript.transcript_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTranscript.untranscripted_created' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTranscript.untranscripted_created

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTranscript.transcript_range' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTranscript.transcript_range

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTranscript.a1_transcript_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTranscript.a1_transcript_sum
