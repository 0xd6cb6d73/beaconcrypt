-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective

/-! Injectivity of the CE-A1 matching and the combined CE-A1 headline (CE-8). `SharedMatch c c'` is the event that two distinct Beacons accepted and the same session matches each before its acceptance. On every outcome of the deployment experiment at identity index zero (the index of CE-9), session handles are positional (`session_unique`, from the CE-9 trace invariant `Traced.positional` and `compiled_trace`), so the two matches use one accept and one accepted candidate; the first published bundle of each Beacon carries the identity key of its final native identity seed (`keys_identity`, from the run invariant `Agree` of CE-5 and the approved Phase 1 read-back contract); hence the two owners have equal identity keys (`shared_collision`). Through CE-COMPILE, the constructor and `owners_collision`, the probability of `SharedMatch` is at most `ε_inj`, the sum over the `qCreate + 1` identity indices of the joint-use weak-EUF advantage of the collision finder's family reduction (`injective_bound`). `ce_a1_injective` adds this to `PqxdhDeploymentServerAuthBills.ce_a1_billed` by the union bound: the probability that some Beacon pinned to the constructed Server accepted with no session that matches it with that pin (`A1NoPinnedMatch`) on a run with `NoBundleFailure_c`, or that two distinct Beacons are matched to one session (by the public matching `MatchedAt`, which every pinned match is), is at most the sum over the creation indices of the Server-authentication bound of `R_c` at the transported caps plus `ε_inj`. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentInterface (Entry FreshBounds ModeSpec Mode Budget)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentCompile (Local)
open PqxdhDeploymentCompileSecrecy (compileFull mergeFull)
open PqxdhDeploymentServerAuthEvent (Reg regOfEntry regsOf summarizeReg accepted bundleOfReg keysOfBundle publishedKeys
  MatchedAt)
open PqxdhDeploymentServerAuthInjective (identities Collision)
open PqxdhDeploymentRegistrationTrace (Logged acceptsOf traceFrom)
open PqxdhDeploymentKemTransfer (registrations regOf)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-! ## The registration view and the transcript -/

/-- Searching a filtered list searches the list with the filter composed. -/
theorem findSome_filterMap {α β γ : Type} (keep : α → Option β) (search : β → Option γ) (list : List α) :
    (list.filterMap keep).findSome? search = list.findSome? fun value => (keep value).bind search := by
  induction list with
  | nil => rfl
  | cons value rest ih =>
      cases kept : keep value with
      | none => simp [kept, ih]
      | some reg => simp [kept, ih, List.findSome?_cons]

/-- The first successful bundle of an owner in the registration view of a transcript is its first successful bundle in the transcript. -/
theorem bundleOfReg_regsOf (transcript : List Entry) (owner : Nat) :
    bundleOfReg (regsOf transcript) owner = PqxdhDeploymentTranscript.bundleOf transcript owner := by
  unfold bundleOfReg regsOf PqxdhDeploymentTranscript.bundleOf
  rw [findSome_filterMap]
  congr 1
  funext entry
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · rfl
  · cases command with
    | create pin keyId =>
        cases reply with
        | none => rfl
        | some index => cases parsed : PqxdhDeploymentInterface.parsePin pin <;> simp [regOfEntry, parsed]
    | bundle index =>
        cases reply with
        | none => rfl
        | some bytes => rfl
    | _ => rfl
  · rfl

/-- An accept of the registration view of a transcript is a logged raw accept of its registrations. -/
theorem accept_registrations (transcript : List Entry) (raw : Pqxdh.Bytes) (reply : Option Nat)
    (member : Reg.accept raw reply ∈ regsOf transcript) : (raw, reply) ∈ acceptsOf (registrations transcript) := by
  simp only [regsOf, List.mem_filterMap] at member
  obtain ⟨entry, entryMember, found⟩ := member
  simp only [acceptsOf, registrations, List.mem_filterMap]
  refine ⟨.accept raw reply, ⟨entry, entryMember, ?_⟩, rfl⟩
  rcases entry with ⟨(coin | command) | secrecy, entryReply⟩
  · cases found
  · cases command with
    | create pin keyId =>
        cases entryReply with
        | none => cases found
        | some index =>
            cases parsed : PqxdhDeploymentInterface.parsePin pin <;> simp [regOfEntry, parsed] at found
    | accept other =>
        simp only [regOfEntry, Option.some.injEq, Reg.accept.injEq] at found
        obtain ⟨rfl, rfl⟩ := found
        rfl
    | bundle index => cases found
    | build session payload => cases found
    | finish index other => cases found
    | _ => cases found
  · cases found

/-- Session handles are positional on every outcome of the deployment experiment (identity index zero, as in CE-9): two logged raw accepts of the final transcript that returned the same session handle carry the same bytes. -/
theorem session_unique (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X) (final : PqxdhDeploymentSecrecy.State KemSK)
    (found : outcome.1 = some (created, output, final)) (raw other : Pqxdh.Bytes) (session : Nat)
    (first : (raw, some session) ∈ acceptsOf (registrations final.1.transcript))
    (second : (other, some session) ∈ acceptsOf (registrations final.1.transcript)) : raw = other := by
  have game := PqxdhDeploymentCompileSecrecy.compile_full_source setup codec checks route ensureInit phase1 phase2 bounds
    mode adversary ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)
  change _ = (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime at game
  have traced := PqxdhDeploymentRegistrationTrace.source_map setup codec checks ensureInit none Prod.fst
    (traceFrom (compileFull setup codec route bounds mode adversary) [])
    ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)
  rw [PqxdhDeploymentRegistrationTrace.traceFrom_erase] at traced
  rw [← game, traced, Functor.map_map, support_map] at member
  obtain ⟨⟨_ | source, after⟩, sourceMember, rfl⟩ := member
  · simp [mergeFull] at found
  · simp only [mergeFull, Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨_, _, rfl⟩ := found
    have result := PqxdhDeploymentRegistrationTrace.source_support setup codec checks ensureInit none _ _ _ source
      sourceMember
    have logEq := PqxdhDeploymentKemTransfer.compiled_trace setup codec route bounds mode adversary source.2.1 result
    obtain ⟨tracedState, _⟩ := PqxdhDeploymentRegistrationTrace.traced_source setup codec checks ensureInit none _ _ rfl
      after source sourceMember
    simp only [PqxdhRegistrationJointInitializedSchedule.eraseOutcome] at first second
    rw [← logEq] at first second
    obtain ⟨position, positionFound⟩ := List.mem_iff_getElem?.mp first
    obtain ⟨position', positionFound'⟩ := List.mem_iff_getElem?.mp second
    have samePosition := tracedState.positional position raw session positionFound
    have samePosition' := tracedState.positional position' other session positionFound'
    rw [← samePosition, samePosition', positionFound'] at positionFound
    simp only [Option.some.injEq, Prod.mk.injEq] at positionFound
    exact positionFound.1.symm


/-- A first successful bundle found in a prefix of the registration view is the first successful bundle of the view. -/
theorem bundleOfReg_prefix (before regs : List Reg) (prefixed : before <+: regs) (owner : Nat) (bytes : Pqxdh.Bytes)
    (found : bundleOfReg before owner = some bytes) : bundleOfReg regs owner = some bytes := by
  obtain ⟨rest, rfl⟩ := prefixed
  unfold bundleOfReg at found ⊢
  rw [List.findSome?_append, found]
  rfl

/-- On every outcome of the deployment experiment, the identity key that the first published bundle of an owner carries, read without a signature check, is the identity key of that owner's final native identity seed. Premise: the approved Phase 1 read-back contract. -/
theorem keys_identity (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (server : RawCtxServerRouting.Identity)
    (transcript : List Entry) (native : PqxdhRegistrationSchedule.State KemSK)
    (agree : PqxdhDeploymentEligibility.Agree setup codec server transcript native) (before : List Reg)
    (prefixed : before <+: regsOf transcript) (owner : Nat)
    (keys : PqxdhEd25519EufCma.Ed25519PublicKey × PqxdhEd25519EufCma.Phase1KeyTuple)
    (published : publishedKeys codec before owner = some keys) :
    ∃ entry : PqxdhRegistrationSchedule.Owner KemSK, native.owners[owner]? = some entry ∧
      keys.1 = (setup.joint.publicKeys entry.beacon.identity).ed25519 := by
  unfold publishedKeys keysOfBundle at published
  obtain ⟨bytes, bytesFound, rest⟩ := Option.bind_eq_some_iff.mp published
  have full := bundleOfReg_prefix _ _ prefixed owner bytes bytesFound
  rw [bundleOfReg_regsOf] at full
  obtain ⟨entry, tuple, preSignature, oneSignature, pqSignature, entryFound, written, _⟩ :=
    agree.bundles _ (PqxdhDeploymentKeyMatch.bundleOf_mem transcript owner bytes full)
  have read := PqxdhDeploymentKeyMatch.candidateOf_written codec phase1 _ bytes written
  rw [read] at rest
  simp [PqxdhJointPhase1SourceWriter.candidate, PqxdhDeploymentPublishedTuple.candidateTuple] at rest
  refine ⟨entry, entryFound, ?_⟩
  rw [← rest]


/-- Two distinct Beacons `c` and `c'` of an outcome of the deployment experiment are matched to one session: each accepted, and the same session matches each before its acceptance. -/
def SharedMatch {X A : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c c' : Nat)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧ c ≠ c' ∧ ∃ session,
    (∃ before raw, accepted c (regsOf final.1.transcript) = some (before, raw) ∧
      MatchedAt setup.source.crypto codec c session before raw) ∧
    (∃ before raw, accepted c' (regsOf final.1.transcript) = some (before, raw) ∧
      MatchedAt setup.source.crypto codec c' session before raw)

/-- The identity seeds of the reassembled deployment state are those of the source14 state. -/
theorem identities_merge (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) :
    identities (PqxdhDeploymentCompile.merge copies native).native = identities native := by
  simp only [identities, PqxdhDeploymentCompile.merge]
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_map, List.getElem?_mapIdx]
  cases native.owners[index]? with
  | none => rfl
  | some owner =>
      simp only [Option.map_some]
      unfold PqxdhDeploymentCompile.mergeOwner
      split <;> rfl

/-- On every outcome of the deployment experiment (identity index zero), two distinct Beacons matched to one session have equal identity keys: their first published bundles carry the keys of one accepted candidate. -/
theorem shared_collision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime)) (c c' : Nat) (shared : SharedMatch setup codec c c' outcome) :
    ∃ created output final, outcome.1 = some (created, output, final) ∧
      Collision setup.joint (identities final.2.native) := by
  obtain ⟨created, output, final, found, different, session, ⟨before, raw, acceptedEq, matched⟩,
    ⟨before', raw', acceptedEq', matched'⟩⟩ := shared
  refine ⟨created, output, final, found, ?_⟩
  have agree := PqxdhDeploymentEligibility.agree_game setup codec checks route ensureInit 0 bounds mode adversary
    runtime outcome member created output final found
  have prefixed := PqxdhDeploymentServerAuthEvent.accepted_prefix c _ before raw acceptedEq
  have prefixed' := PqxdhDeploymentServerAuthEvent.accepted_prefix c' _ before' raw' acceptedEq'
  obtain ⟨acceptRaw, candidate, keys, _, _, _, acceptMember, candidateEq, keysEq, publishedEq, _⟩ := matched
  obtain ⟨acceptRaw', candidate', keys', _, _, _, acceptMember', candidateEq', keysEq', publishedEq', _⟩ := matched'
  have sameRaw : acceptRaw = acceptRaw' := session_unique setup codec checks route ensureInit phase1 phase2 bounds mode
    adversary runtime outcome member created output final found acceptRaw acceptRaw' session
    (accept_registrations _ _ _ (prefixed.subset acceptMember))
    (accept_registrations _ _ _ (prefixed'.subset acceptMember'))
  subst sameRaw
  rw [candidateEq, Option.some.injEq] at candidateEq'
  subst candidateEq'
  rw [keysEq, Option.some.injEq] at keysEq'
  subst keysEq'
  obtain ⟨entry, entryFound, entryKey⟩ := keys_identity setup codec phase1 _ _ _ agree before prefixed c keys publishedEq
  obtain ⟨entry', entryFound', entryKey'⟩ := keys_identity setup codec phase1 _ _ _ agree before' prefixed' c' keys
    publishedEq'
  refine ⟨c, c', different, entry.beacon.identity, entry'.beacon.identity, ?_, ?_, ?_⟩
  · simp [identities, entryFound]
  · simp [identities, entryFound']
  · rw [← entryKey, ← entryKey']


/-- A query cap transfers between two equivalent query classes. -/
theorem bound_congr {κ α : Type} {spec : OracleSpec κ} (program : OracleComp spec α) (first second : κ → Prop)
    [DecidablePred first] [DecidablePred second] (same : ∀ query, first query ↔ second query) (cap : Nat)
    (bounded : program.IsQueryBoundP first cap) : program.IsQueryBoundP second cap := by
  induction program using OracleComp.inductionOn generalizing cap with
  | pure value => exact isQueryBoundP_pure _ _ _
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded ⊢
      obtain ⟨allowed, rest⟩ := bounded
      refine ⟨by rw [← same]; exact allowed, fun reply => ?_⟩
      by_cases holds : first query
      · have holds' := (same query).mp holds
        simp only [holds, holds', ite_true] at rest ⊢
        exact ih reply _ (rest reply)
      · have holds' : ¬ second query := fun other => holds ((same query).mpr other)
        simp only [holds, holds', ite_false] at rest ⊢
        exact ih reply _ (rest reply)

/-- The compiled program of a budget-respecting adversary makes at most `qCreate + 1` creates. -/
theorem compiled_creates (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) :
    (compileFull setup codec route bounds mode adversary).IsQueryBoundP
      (PqxdhDeploymentServerAuthInjective.IsCreate (KemSK := KemSK)) (budget.create + 1) := by
  have certified := PqxdhDeploymentCompileCaps.compile_full_certified setup codec route bounds mode adversary budget
    respects (.inl 1)
  refine (bound_congr _ _ _ (fun query => ?_) _ certified).mono (by
    simp [PqxdhDeploymentCompileCaps.transported])
  rcases query with (coin | request) | read
  · simp [PqxdhRegistrationJointRevealCosts.sourceKind, PqxdhRegistrationSchedule.sourceKind,
      PqxdhDeploymentServerAuthInjective.IsCreate]
  · cases request <;> simp [PqxdhRegistrationJointRevealCosts.sourceKind, PqxdhRegistrationSchedule.sourceKind,
      PqxdhDeploymentServerAuthInjective.IsCreate]
  · simp [PqxdhRegistrationJointRevealCosts.sourceKind, PqxdhDeploymentServerAuthInjective.IsCreate]

set_option linter.deprecated false in
/-- The injectivity loss `ε_inj` of CE-A1: in the common deployment experiment of a budget-respecting adversary (identity index zero), the probability that two distinct Beacons are matched to one session is at most the sum, over the `qCreate + 1` identity indices `t`, of the joint-use weak-EUF advantage of the family reduction of the collision finder at `t`. Premises: the approved Phase 1 and Phase 2 read-back contracts. No distributional property of key generation is assumed; a collision of identity keys gives a forgery by signing correctness. -/
theorem injective_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A) :
    𝒟[(fun outcome => @decide (∃ c c', SharedMatch setup codec c c' outcome) (Classical.propDecidable _)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ target : Fin (budget.create + 1), advantage setup.joint
        (PqxdhJointIdentityFamily.reduction setup.joint target
          (PqxdhDeploymentServerAuthInjective.collider budget.create)) := by
  classical
  rw [UniformTargetSelection.chance_eq]
  refine le_trans (probEvent_mono (q := fun outcome => ∃ created output final, outcome.1 = some (created, output, final) ∧
    Collision setup.joint (identities final.2.native)) fun outcome member ⟨c, c', shared⟩ =>
      shared_collision setup codec checks route ensureInit phase1 phase2 bounds mode adversary runtime outcome member c c'
        shared) ?_
  refine le_trans ?_ (PqxdhDeploymentServerAuthInjective.collision_bound setup budget.create)
  rw [← PqxdhDeploymentCompileSecrecy.compile_full_game setup codec checks route ensureInit 0 phase1 phase2 bounds mode
    adversary runtime, probEvent_map]
  simp only [PqxdhRegistrationJointInitializedSchedule.native, PqxdhLiveServerConstruction.construct, StateT.run,
    bind_assoc]
  refine probEvent_bind_le_of_forall_le fun ready _ => ?_
  cases ready.1 with
  | false =>
      simp only [Bool.false_eq_true, ite_false, pure_bind]
      refine le_of_eq_of_le (probEvent_eq_zero_iff.mpr ?_) zero_le
      intro outcome member
      simp only [support_pure, Set.mem_singleton_iff] at member
      subst member
      simp [mergeFull]
  | true =>
      simp only [ite_true, bind_map_left]
      refine probEvent_bind_le_of_forall_le fun seed _ => ?_
      rw [probEvent_map]
      refine le_of_eq_of_le (probEvent_ext fun result _ => ?_)
        (PqxdhDeploymentServerAuthInjective.owners_collision setup codec checks seed
          (compileFull setup codec route bounds mode adversary) (budget.create + 1)
          (compiled_creates setup codec route bounds mode adversary budget respects) _ rfl)
      simp only [Function.comp_apply, mergeFull, Option.map_some, Option.some.injEq]
      constructor
      · rintro ⟨_, _, _, equal, collision⟩
        cases equal
        simpa [identities_merge] using collision
      · intro collision
        exact ⟨_, _, _, rfl, by simpa [identities_merge] using collision⟩


set_option linter.deprecated false in
/-- Theorem CE-A1 with injectivity (plan section 10): in the common deployment experiment with a generated Server seed (identity index zero, as in CE-9), for a budget-respecting adversary, the probability that some Beacon pinned to the constructed Server accepted with no session that matches it with that pin (`A1NoPinnedMatch`) on a run with `NoBundleFailure_c`, or that two distinct Beacons are matched to one session, is at most the sum over the `qCreate` creation indices `c` of the Server-authentication bound of `R_c` at the transported caps, plus `ε_inj`, the sum over the `qCreate + 1` identity indices of the joint-use weak-EUF advantage of the collision finder's family reduction; every reduction of the first sum has its bills. Premises: the approved Phase 1, Phase 2 and frame read-back contracts, `ReadWritable`, `X25519ClassLaw`, `X25519ScalarSpread`, `SourceFullCorrect`, `HasAttachedVerificationAdapter` and the KEM base caps. -/
theorem ce_a1_injective (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
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
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[(fun outcome => @decide ((∃ c, PqxdhDeploymentServerAuth.A1NoPinnedMatch setup codec c outcome) ∨
        ∃ c c', SharedMatch setup codec c c' outcome) (Classical.propDecidable _)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime]
        {true}).toReal ≤
      (∑ c : Fin budget.create, PqxdhDeploymentServerAuth.serverAuthBound setup codec checks caps
        (PqxdhDeploymentServerAuth.serverAuthAdversary setup codec route bounds mode adversary c)
        (PqxdhDeploymentServerAuthBills.coinCap caps bounds budget) budget.accept
        (PqxdhDeploymentServerAuthBills.romCap budget) (PqxdhDeploymentServerAuthBills.hashCap budget) fallback
        signatureFallback) +
      ∑ target : Fin (budget.create + 1), (advantage setup.joint
        (PqxdhJointIdentityFamily.reduction setup.joint target
          (PqxdhDeploymentServerAuthInjective.collider budget.create))).toReal ∧
    ∀ c, PqxdhServerAuthCommonAuthentication.ReductionBills setup codec checks caps
      (PqxdhDeploymentServerAuth.serverAuthAdversary setup codec route bounds mode adversary c)
      (PqxdhDeploymentServerAuthBills.coinCap caps bounds budget) budget.accept
      (PqxdhDeploymentServerAuthBills.romCap budget) (PqxdhDeploymentServerAuthBills.hashCap budget)
      (PqxdhDeploymentServerAuthBills.totalCap caps bounds budget) budget.finish fallback signatureFallback := by
  have unmatched := PqxdhDeploymentServerAuthBills.ce_a1_billed setup codec checks caps bounded route ensureInit 0
    phase1 phase2 frameBack writable law spread correct adapter bounds mode adversary budget respects runtime fallback
    signatureFallback
  have injective := injective_bound setup codec checks route ensureInit phase1 phase2 bounds mode adversary budget
    respects runtime
  refine ⟨?_, unmatched.2⟩
  set run := (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime
  classical
  rw [UniformTargetSelection.chance_eq] at unmatched injective
  have total : 𝒟[(fun outcome => @decide ((∃ c, PqxdhDeploymentServerAuth.A1NoPinnedMatch setup codec c outcome) ∨
      ∃ c c', SharedMatch setup codec c c' outcome) (Classical.propDecidable _)) <$> run] {true} =
      Pr[fun outcome => (∃ c, PqxdhDeploymentServerAuth.A1NoPinnedMatch setup codec c outcome) ∨
        ∃ c c', SharedMatch setup codec c c' outcome | run] :=
    @UniformTargetSelection.chance_eq _ run _ (fun _ => Classical.propDecidable _)
  rw [total]
  have split := probEvent_or_le run (fun outcome => ∃ c, PqxdhDeploymentServerAuth.A1NoPinnedMatch setup codec c outcome)
    (fun outcome => ∃ c c', SharedMatch setup codec c c' outcome)
  have finiteSum : ∑ target : Fin (budget.create + 1), advantage setup.joint
      (PqxdhJointIdentityFamily.reduction setup.joint target
        (PqxdhDeploymentServerAuthInjective.collider budget.create)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun _ _ => ne_top_of_le_ne_top ENNReal.one_ne_top probOutput_le_one
  refine (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩) split).trans ?_
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top]
  refine add_le_add unmatched.1 ?_
  rw [← ENNReal.toReal_sum fun target _ => ne_top_of_le_ne_top finiteSum
    (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ target))]
  exact ENNReal.toReal_mono finiteSum injective


end BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.findSome_filterMap' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.findSome_filterMap

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.bundleOfReg_regsOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.bundleOfReg_regsOf

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.accept_registrations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.accept_registrations

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.session_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.session_unique

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.bundleOfReg_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.bundleOfReg_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.keys_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.keys_identity

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.identities_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.identities_merge

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.shared_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.shared_collision

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.bound_congr' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.bound_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.compiled_creates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.compiled_creates

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.injective_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.injective_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.ce_a1_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame.ce_a1_injective
