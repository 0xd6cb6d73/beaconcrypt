-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain

/-! Theorem CE-A1, the initial-response origin of every Beacon in the common deployment experiment (CE-8, plan section 10). `reduction c` is `R_c`: the frozen compiled program under the embedding at creation index `c`, journaling its own ServerAuth queries; `serverAuthAdversary c` discards its return value. `a1_le_ordered` bounds the probability of CE-A1 at `c` (`A1At`) by the probability of the common authentication failure of `R_c` in the ordered Server-authentication game: CE-COMPILE (`compile_full_game`), the constructor's initialization gate and generated seed against the game's seed draw (`generated_order`), and `PqxdhDeploymentServerAuthChain.seed_bound` for every seed. `a1_bound` adds the existing complete Server-authentication bound with its reduction bills (`common_authentication_with_resources`) for `R_c`, with `R_c`'s query caps (`ReductionCaps`) as a premise. For a budget-respecting adversary, CE-A1 can occur only below `qCreate` (`a1_range`), so the exact union over the `qCreate` creation indices gives `a1_sum`. `A1NoFailure` is CE-A1 on runs with `NoBundleFailure_c` (option (b) of plan section 19), which implies `A1At` (`noFailure_a1At`). The matching relation is public: a session matches owner `c` when an accept returned it on bytes whose raw candidate the source attached verification accepts with the identity key and key tuple of `c`'s first published bundle, and a build of it returned the decoded record that `c` accepted, both before the acceptance. It is weaker than the plan's eleven-field common session: the Server-authentication common event implies it on the same run (`PqxdhDeploymentServerAuthChain.root_failure`), not conversely; in particular it states no root agreement and nothing about the KEM ciphertext or the ephemeral key of the accepted response. `PinnedMatchAt` adds the Server-identity conjunct of CE-5's `PqxdhDeploymentTranscript.Linked`: the matching build response reads back, with the Phase 2 reader, `c`'s pin as the Server identity. `A1NoPinnedMatch` is `A1NoFailure` with this matching; it contains `A1NoFailure` on every outcome (`noFailure_noPinnedMatch`) and coincides with it on every outcome of the experiment (`noPinnedMatch_noFailure`, from `build_pin`: every successful build response of the experiment carries the constructed Server's identity key). `ce_a1` is stated for `A1NoPinnedMatch`, so the matching of the headline is pinned to the Server identity. The KEM-ciphertext conjunct of `Linked` is not part of the matching, and it is not provable at the CE-A1 bound: the Server-authentication bound charges no KEM property, and with a KEM whose decapsulation ignores the ciphertext, an adversary that relays a session's build response to a Beacon with only the ciphertext replaced makes the Beacon derive the same key and accept, so the session still matches it with the pin while no build response carries the Beacon's ciphertext. By plan section 30 the ciphertext link moves to the Beacon-side symbolic-eligibility corollary of CE-12, which charges its own term `ε_ct`: a per-pair IND-CCA reduction (an existing assumption) plus a statistical term for the ideal world. CE-5's `designate` keeps its ciphertext-equality conjunct, so CE-9 is unaffected. The injectivity of the matching across Beacons is a separate statement (`PqxdhDeploymentServerAuthInjectiveGame`). -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentServerAuth
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthSourceCosts
open PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh PqxdhServerAuthAssumptions
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhEd25519EufCma CtxNonceAeadIntCtxt
open PqxdhJointIdentity
open PqxdhDeploymentInterface (FreshBounds ModeSpec Mode Budget)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentCompile (Local)
open PqxdhDeploymentCompileSecrecy (compileFull mergeFull)
open PqxdhDeploymentServerAuthEvent (SourceEntry Reg regsOf regsOfSource summarizeReg accepted Matched Unmatched A1At
  protectedBinding)
open PqxdhDeploymentServerAuthChain (seedBinding seedInput)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X A : Type}

/-- The reduction `R_c` of the deployment adversary: the embedding at creation index `c` of the compiled program, journaling its own ServerAuth queries. -/
noncomputable def reduction (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (c : Nat) (input : AuthInput) :
    OracleComp ServerAuthSpec (((((X × Ledger) × Local) × List (SourceEntry KemSK)) ×
      PqxdhDeploymentServerAuthEmbed.Emb KemSK) × QueryLog ServerAuthSpec) :=
  PqxdhDeploymentServerAuthEmbed.adversary setup codec c (compileFull setup codec route bounds mode adversary) input

/-- `R_c` as a Server-authentication adversary: its return value discarded. -/
noncomputable def serverAuthAdversary (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (c : Nat) : Adversary :=
  PqxdhRegistrationR1Authentication.unitWork (reduction (KemSK := KemSK) setup codec route bounds mode adversary c)

/-- The CE-A1 event at creation index `c`, as a decision. -/
noncomputable def a1Decision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Bool :=
  @decide (A1At setup codec c outcome) (Classical.propDecidable _)

/-- The CE-A1 event at a constructed Server is the A1 failure on the transcript of the compiled program's run. -/
theorem a1At_merge (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit)
    (result : ((X × Ledger) × Local) × PqxdhRegistrationSchedule.State KemSK) (runtime : A) :
    A1At setup codec c (mergeFull (some (created, result), runtime)) ↔
      Unmatched setup.source.crypto codec (protectedBinding setup created) c (regsOf result.1.1.2.transcript) := by
  constructor
  · rintro ⟨created', output, final, found, failure⟩
    simp only [mergeFull, Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, _, rfl⟩ := found
    exact failure
  · intro failure
    exact ⟨_, _, _, rfl, failure⟩


set_option linter.deprecated false in
/-- Two continuations of one computation, with possibly different events, compare pointwise on its support. -/
theorem probEvent_bind_le {α β γ : Type} (first : ProbComp α) (left : α → ProbComp β) (right : α → ProbComp γ)
    (leftEvent : β → Prop) (rightEvent : γ → Prop)
    (bound : ∀ value ∈ support first, Pr[leftEvent | left value] ≤ Pr[rightEvent | right value]) :
    Pr[leftEvent | first >>= left] ≤ Pr[rightEvent | first >>= right] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun value => ?_
  by_cases member : value ∈ support first
  · gcongr
    exact bound value member
  · simp [probOutput_eq_zero_of_not_mem_support member]

set_option linter.deprecated false in
/-- Per creation index `c`: the probability of CE-A1 at `c` in the common deployment experiment, for every identity index of the constructed Server and every initialization runtime, is at most the probability of the common authentication failure of `R_c` in the ordered Server-authentication game. The constructor's initialization gate and seed draw are matched with the game's seed draw; a refused construction has no event. Premises: the approved Phase 1 and Phase 2 read-back contracts (through CE-COMPILE). -/
theorem a1_le_ordered (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) (c : Nat) :
    Pr[fun outcome => A1At setup codec c outcome |
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime] ≤
    Pr[fun result => PqxdhServerAuthCommonProbability.decision setup codec checks result = true |
      PqxdhServerAuthRootObserved.orderedGame setup codec checks false
        (serverAuthAdversary (KemSK := KemSK) setup codec route bounds mode adversary c)] := by
  rw [← PqxdhDeploymentCompileSecrecy.compile_full_game setup codec checks route ensureInit identityIndex phase1 phase2
    bounds mode adversary runtime, probEvent_map]
  rw [show serverAuthAdversary (KemSK := KemSK) setup codec route bounds mode adversary c =
      fun input => (fun _ => ()) <$> reduction (KemSK := KemSK) setup codec route bounds mode adversary c input from rfl,
    ← PqxdhRegistrationR1RootAudit.generated_order setup codec checks
      (reduction (KemSK := KemSK) setup codec route bounds mode adversary c)]
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
      simp [mergeFull, A1At]
  | true =>
      simp only [ite_true, bind_map_left]
      refine probEvent_bind_le _ _ _ _ _ fun seed seeded => ?_
      rw [probEvent_map, probEvent_map]
      have bound := PqxdhDeploymentServerAuthChain.seed_bound setup codec checks phase1 route bounds mode adversary c seed
        seeded identityIndex .generated
      refine le_of_eq_of_le ?_ bound
      refine probEvent_ext fun result _ => ?_
      exact a1At_merge setup codec c _ result _

/-- The ServerAuth bound of `R_c`: the Gap-DH advantage of the scanning extractor, the accept-collision term, the record and schedule losses of every record coordinate and the joint-use signature advantage, each of the reductions constructed from `R_c`. -/
noncomputable def serverAuthBound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (adversary : Adversary) (qCoin Q qH qHash : Nat) (fallback : ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery) : ℝ :=
  (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
    (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal +
  (Q.choose 2 : ℝ) * 64 / (2 ^ 256 : ℝ) +
  ∑ j : Fin (Q + 1), (PqxdhServerAuthPublicationLoss.recordLoss setup codec checks adversary Q j fallback
    (entryReductionBudget caps qCoin Q qHash qH + 76) +
    PqxdhServerAuthObservedSchedule.scheduleLoss setup codec checks adversary false Q j
      (PqxdhServerAuthSessionRecord.observers codec Q j)) +
  (PqxdhJointIdentity.advantage setup.joint
    (PqxdhServerAuthJointIdentityEuf.reduction setup codec checks adversary signatureFallback)).toReal

/-- The query caps of `R_c` that the Server-authentication theorem charges: accepts, random-oracle HMACs, BLAKE2b queries, coins, all queries and finishes. -/
structure ReductionCaps (work : AuthInput → OracleComp ServerAuthSpec X) (qCoin Q qH qHash qTotal qFinish : Nat) : Prop where
  source : PqxdhRegistrationR1Authentication.SourceBudget work Q qH qHash
  coins : ∀ input, (work input).IsQueryBoundP IsAuthCoin qCoin
  total : ∀ input, (work input).IsTotalQueryBound qTotal
  finish : ∀ input, (work input).IsQueryBoundP PqxdhServerAuthJointIdentityDhBudget.IsFinish qFinish

set_option linter.deprecated false in
/-- Theorem CE-A1 at one creation index `c`: in the common deployment experiment with a generated Server seed, for every identity index of the constructed Server, the probability that owner `c`, created with the protected binding, accepted with no session matching it and no rejected bundle call in Fresh before its acceptance, is at most the Server-authentication bound of `R_c`, with the bills of every reduction in that bound. Premises: the approved Phase 1 and Phase 2 read-back contracts, `FrameReadBack`, `ReadWritable`, `X25519ClassLaw`, `X25519ScalarSpread`, `SourceFullCorrect`, `HasAttachedVerificationAdapter`, the KEM base caps and the query caps of `R_c`. -/
theorem a1_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) (caps : KemCaps)
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
    (𝒟[a1Decision setup codec c <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime]
        {true}).toReal ≤
      serverAuthBound setup codec checks caps (serverAuthAdversary setup codec route bounds mode adversary c)
        qCoin Q qH qHash fallback signatureFallback ∧
    PqxdhServerAuthCommonAuthentication.ReductionBills setup codec checks caps
      (serverAuthAdversary setup codec route bounds mode adversary c) qCoin Q qH qHash qTotal qFinish fallback
      signatureFallback := by
  set work := reduction (KemSK := KemSK) setup codec route bounds mode adversary c
  have sa := PqxdhServerAuthCommonAuthentication.common_authentication_with_resources setup codec checks caps bounded
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
  have ordered := a1_le_ordered setup codec checks route ensureInit identityIndex phase1 phase2 bounds mode adversary
    runtime c
  have left : 𝒟[a1Decision setup codec c <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime]
        {true} = Pr[fun outcome => A1At setup codec c outcome |
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run
        runtime] := by
    classical
    exact UniformTargetSelection.chance_eq _ _
  have right : 𝒟[PqxdhServerAuthCommonProbability.decision setup codec checks <$>
      PqxdhServerAuthRootObserved.orderedGame setup codec checks false
        (serverAuthAdversary setup codec route bounds mode adversary c)] {true} =
      Pr[fun result => PqxdhServerAuthCommonProbability.decision setup codec checks result = true |
        PqxdhServerAuthRootObserved.orderedGame setup codec checks false
          (serverAuthAdversary setup codec route bounds mode adversary c)] := by
    rw [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map]
    rfl
  have finite : 𝒟[PqxdhServerAuthCommonProbability.decision setup codec checks <$>
      PqxdhServerAuthRootObserved.orderedGame setup codec checks false
        (serverAuthAdversary setup codec route bounds mode adversary c)] {true} ≠ ⊤ := by
    rw [evalDist_apply_singleton]
    exact probOutput_ne_top
  rw [left]
  rw [← right] at ordered
  exact (ENNReal.toReal_mono finite ordered).trans sa.1


/-! ## All creation indices -/

/-- A summary step never removes an owner binding. -/
theorem owners_step (summary : PqxdhDeploymentTranscript.Summary) (reg : Reg) :
    summary.owners.length ≤ (PqxdhDeploymentServerAuthEvent.stepReg summary reg).owners.length := by
  cases reg with
  | create pin keyId owner => simp [PqxdhDeploymentServerAuthEvent.stepReg]
  | bundle owner reply =>
      cases reply <;> simp only [PqxdhDeploymentServerAuthEvent.stepReg] <;> split_ifs <;> exact le_refl _
  | accept raw reply => exact le_refl _
  | build session payload reply => exact le_refl _
  | finish owner raw reply =>
      cases reply <;> simp only [PqxdhDeploymentServerAuthEvent.stepReg] <;> split_ifs <;> exact le_refl _

/-- Folding summary steps never removes an owner binding. -/
theorem owners_foldl (summary : PqxdhDeploymentTranscript.Summary) (regs : List Reg) :
    summary.owners.length ≤ (regs.foldl PqxdhDeploymentServerAuthEvent.stepReg summary).owners.length := by
  induction regs generalizing summary with
  | nil => exact le_refl _
  | cons reg rest ih => exact (owners_step summary reg).trans (ih _)

/-- Owner `c` of an A1 failure has a binding in the summary of the view. -/
theorem unmatched_created (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (binding : PqxdhBeaconPhase2Preparation.Word32 × Std.U64) (c : Nat) (regs : List Reg)
    (failure : Unmatched crypto codec binding c regs) : c < (summarizeReg regs).owners.length := by
  obtain ⟨before, raw, found, bound, _, _⟩ := failure
  have below : c < (summarizeReg before).owners.length := (List.getElem?_eq_some_iff.mp bound).1
  obtain ⟨rest, rfl⟩ := PqxdhDeploymentServerAuthEvent.accepted_prefix c regs before raw found
  rw [PqxdhDeploymentServerAuthEvent.summarizeReg_append]
  exact lt_of_lt_of_le below (owners_foldl _ rest)

/-- Every return value of the compiled program of a budget-respecting adversary has at most `qCreate` owner bindings in its transcript summary. -/
theorem compiled_owners (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (value : (X × Ledger) × Local) (member : value ∈ support (compileFull setup codec route bounds mode adversary)) :
    (PqxdhDeploymentTranscript.summarize value.1.2.transcript).owners.length ≤ budget.create := by
  have wrapped : value.1 ∈ support (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds
      (PqxdhDeploymentInterface.asModeO mode adversary)) := by
    apply support_simulateQ_run'_subset (PqxdhDeploymentCompile.compileImpl setup codec route) _ Local.empty
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ member
  have creates := PqxdhDeploymentTargetRange.ledger_count setup.source.crypto codec setup.serverKeyId bounds 1
    (PqxdhDeploymentInterface.asModeO mode adversary) (budget.cap 1)
    (PqxdhDeploymentCompileSecrecy.asModeO_bound mode adversary budget respects 1) Ledger.empty _ wrapped
  simp only [Ledger.empty, PqxdhDeploymentTargetRange.classCount, List.countP_nil, Nat.zero_add] at creates
  have owners := PqxdhDeploymentTargetRange.owners_count value.1.2.transcript
  simp only [PqxdhDeploymentTargetRange.classCount] at owners
  exact le_trans owners creates

/-- On every outcome of the deployment experiment of a budget-respecting adversary, CE-A1 can occur only at a creation index below `qCreate`. -/
theorem a1_range (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (member : outcome ∈ support
      ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime))
    (c : Nat) (event : A1At setup codec c outcome) : c < budget.create := by
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
      have failure := (a1At_merge setup codec c _ result after).mp event
      have created' := unmatched_created _ codec _ c _ failure
      rw [← PqxdhDeploymentServerAuthEvent.summarize_regs] at created'
      have program : result.1 ∈ support (compileFull setup codec route bounds mode adversary) := by
        apply support_simulateQ_run'_subset (PqxdhRegistrationJointRevealSchedule.native setup codec checks created.seed)
          _ (PqxdhRegistrationSchedule.initial created)
        rw [StateT.run'_eq, support_map]
        exact Set.mem_image_of_mem _ resultMember
      exact lt_of_lt_of_le created' (compiled_owners setup codec route bounds mode adversary budget respects _ program)

set_option linter.deprecated false in
/-- Theorem CE-A1 over all Beacons, in the A1At form: in the common deployment experiment of a budget-respecting adversary, the probability that some owner accepted as CE-A1 describes is at most the sum over the `qCreate` creation indices `c` of the Server-authentication bound of `R_c`, with every reduction's bills. -/
theorem a1_sum (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) (caps : KemCaps)
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
    (𝒟[(fun outcome => @decide (∃ c, A1At setup codec c outcome) (Classical.propDecidable _)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime]
        {true}).toReal ≤
      ∑ c : Fin budget.create, serverAuthBound setup codec checks caps
        (serverAuthAdversary setup codec route bounds mode adversary c) qCoin Q qH qHash fallback signatureFallback ∧
    ∀ c, PqxdhServerAuthCommonAuthentication.ReductionBills setup codec checks caps
      (serverAuthAdversary setup codec route bounds mode adversary c) qCoin Q qH qHash qTotal qFinish fallback
      signatureFallback := by
  have each := fun c => a1_bound setup codec checks caps bounded route ensureInit identityIndex phase1 phase2 frameBack
    writable law spread correct adapter bounds mode adversary runtime c qCoin Q qH qHash qTotal qFinish
    (reductionCaps c) fallback signatureFallback
  refine ⟨?_, fun c => (each c).2⟩
  set run := (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run
    runtime with runEq
  have chance : ∀ c, 𝒟[a1Decision setup codec c <$> run] {true} = Pr[fun outcome => A1At setup codec c outcome | run] := by
    intro c
    classical
    exact UniformTargetSelection.chance_eq _ _
  have total : 𝒟[(fun outcome => @decide (∃ c, A1At setup codec c outcome) (Classical.propDecidable _)) <$> run]
      {true} = Pr[fun outcome => ∃ c, A1At setup codec c outcome | run] := by
    classical
    exact UniformTargetSelection.chance_eq _ _
  have ranged : Pr[fun outcome => ∃ c, A1At setup codec c outcome | run] =
      Pr[fun outcome => ∃ c ∈ (Finset.univ : Finset (Fin budget.create)), A1At setup codec c.val outcome | run] := by
    refine probEvent_ext fun outcome member => ⟨fun ⟨c, event⟩ => ?_, fun ⟨c, _, event⟩ => ⟨c.val, event⟩⟩
    exact ⟨⟨c, a1_range setup codec checks route ensureInit identityIndex phase1 phase2 bounds mode adversary budget
      respects runtime outcome member c event⟩, Finset.mem_univ _, event⟩
  have union := probEvent_exists_finset_le_sum (Finset.univ : Finset (Fin budget.create)) run
    (fun c outcome => A1At setup codec c.val outcome)
  have finite : ∑ c : Fin budget.create, Pr[fun outcome => A1At setup codec c.val outcome | run] ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun c _ => probEvent_ne_top
  rw [total, ranged]
  refine (ENNReal.toReal_mono finite union).trans ?_
  rw [ENNReal.toReal_sum fun c _ => probEvent_ne_top]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [← chance c.val]
  exact (each c.val).1

/-! ## Runs with no rejected bundle -/

/-- CE-A1 on runs with `NoBundleFailure_c`, with the public matching `Matched` in place of the plan's eleven-field common session (a weaker relation, so a smaller event than the plan's): a Server was constructed; owner `c` has no rejected bundle call in Fresh in the whole run, accepted, was created with the protected binding before its acceptance, and no session matches it. -/
def A1NoFailure {X A : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧
    PqxdhDeploymentTranscript.NoBundleFailureAt final.1.transcript c ∧
    ∃ before raw, accepted c (regsOf final.1.transcript) = some (before, raw) ∧
      (summarizeReg before).owners[c]? = some (protectedBinding setup created) ∧
      ¬ Matched setup.source.crypto codec c before raw

/-- CE-A1 on a run with `NoBundleFailure_c` is CE-A1 in the A1At form: no rejected bundle in the whole run gives none before the acceptance. -/
theorem noFailure_a1At {X A : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (event : A1NoFailure setup codec c outcome) : A1At setup codec c outcome := by
  obtain ⟨created, output, final, found, noFailure, before, raw, acceptedEq, bound, unmatched⟩ := event
  refine ⟨created, output, final, found, before, raw, acceptedEq, bound, ?_, unmatched⟩
  cases failed : (summarizeReg before).failures c with
  | false => rfl
  | true =>
      obtain ⟨rest, restEq⟩ := PqxdhDeploymentServerAuthEvent.accepted_prefix c _ before raw acceptedEq
      have later := PqxdhDeploymentServerAuthEvent.failures_append before rest c failed
      rw [restEq, ← PqxdhDeploymentServerAuthEvent.summarize_regs] at later
      unfold PqxdhDeploymentTranscript.NoBundleFailureAt at noFailure
      rw [noFailure] at later
      cases later

/-! ## The pinned matching -/

/-- Session `session` matches owner `owner` before its acceptance with the pin `pin`: `MatchedAt`, and the matching build response reads back, with the Phase 2 reader, `pin` as the Server identity (the Server-identity conjunct of CE-5's `PqxdhDeploymentTranscript.Linked`). -/
def PinnedMatchAt (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (owner session : Nat)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (before : List Reg) (raw : Pqxdh.Bytes) : Prop :=
  ∃ acceptRaw candidate keys payload reply record,
    Reg.accept acceptRaw (some session) ∈ before ∧ PqxdhDeploymentTranscript.candidateOf codec acceptRaw = some candidate ∧
    PqxdhDeploymentTranscript.acceptedKeys crypto candidate = some keys ∧
    PqxdhDeploymentServerAuthEvent.publishedKeys codec before owner = some keys ∧
    Reg.build session payload (some reply) ∈ before ∧
    (codec.read2 reply.serialized).bind codec.serverIdentity = some pin ∧
    PqxdhServerAuthRecordPublicationEvent.frame codec raw = some record ∧
    PqxdhServerAuthRecordPublicationEvent.frame codec reply.serialized = some record

/-- Some session matches the owner before its acceptance with the pin. -/
def PinnedMatch (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (owner : Nat)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (before : List Reg) (raw : Pqxdh.Bytes) : Prop :=
  ∃ session, PinnedMatchAt crypto codec owner session pin before raw

/-- A pinned match is a match. -/
theorem pinned_matched (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (owner : Nat)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (before : List Reg) (raw : Pqxdh.Bytes)
    (pinned : PinnedMatch crypto codec owner pin before raw) : Matched crypto codec owner before raw := by
  obtain ⟨session, acceptRaw, candidate, keys, payload, reply, record, acceptMember, candidateEq, keysEq, publishedEq,
    buildMember, _, frameRaw, frameReply⟩ := pinned
  exact ⟨session, acceptRaw, candidate, keys, payload, reply, record, acceptMember, candidateEq, keysEq, publishedEq,
    buildMember, frameRaw, frameReply⟩

/-- CE-A1 on runs with `NoBundleFailure_c` with the pinned matching: a Server was constructed; owner `c` has no rejected bundle call in Fresh in the whole run, accepted, was created with the protected binding before its acceptance, and no session matches it with the protected binding's pin, the constructed Server's identity key as a 32-byte word. -/
def A1NoPinnedMatch {X A : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧
    PqxdhDeploymentTranscript.NoBundleFailureAt final.1.transcript c ∧
    ∃ before raw, accepted c (regsOf final.1.transcript) = some (before, raw) ∧
      (summarizeReg before).owners[c]? = some (protectedBinding setup created) ∧
      ¬ PinnedMatch setup.source.crypto codec c (protectedBinding setup created).1 before raw

/-- On every outcome, CE-A1 with the public matching is CE-A1 with the pinned matching: the event with the pinned matching contains the one with the public matching. -/
theorem noFailure_noPinnedMatch {X A : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (event : A1NoFailure setup codec c outcome) : A1NoPinnedMatch setup codec c outcome := by
  obtain ⟨created, output, final, found, noFailure, before, raw, acceptedEq, bound, unmatched⟩ := event
  exact ⟨created, output, final, found, noFailure, before, raw, acceptedEq, bound,
    fun pinned => unmatched (pinned_matched _ codec c _ before raw pinned)⟩

/-- A build entry of the registration view is a build entry of the transcript with the same session, payload and reply. -/
theorem build_entry (transcript : List PqxdhDeploymentInterface.Entry) (session : Nat) (payload : Option Pqxdh.Bytes)
    (reply : PqxdhServerRegistrationPublication.Response)
    (member : Reg.build session payload (some reply) ∈ regsOf transcript) :
    (⟨.inl (.inr (.build session payload)), some reply⟩ : PqxdhDeploymentInterface.Entry) ∈ transcript := by
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
    | build other otherPayload =>
        simp only [PqxdhDeploymentServerAuthEvent.regOfEntry, Option.some.injEq, Reg.build.injEq] at found
        obtain ⟨rfl, rfl, rfl⟩ := found
        exact entryMember
    | _ => simp [PqxdhDeploymentServerAuthEvent.regOfEntry] at found
  · cases found

set_option linter.deprecated false in
/-- On every outcome of the experiment with a constructed Server, every successful build response of the final transcript reads back, with `Phase2ReadBack`, the constructed Server's identity key as the Server identity, which is the pin of the protected binding: the build responses are the Phase 2 writer outputs of fields carrying the Server's identity (CE-5's `Agree.builds`, kept from the initial state), and the generated Server's identity is the 32-byte word of its public identity key (`construct_origin`). -/
theorem build_pin (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds
      mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (reached : outcome.1 = some (created, output, final))
    (session : Nat) (payload : Option Pqxdh.Bytes) (reply : PqxdhServerRegistrationPublication.Response)
    (built : (⟨.inl (.inr (.build session payload)), some reply⟩ : PqxdhDeploymentInterface.Entry) ∈
      final.1.transcript) :
    (codec.read2 reply.serialized).bind codec.serverIdentity = some (protectedBinding setup created).1 := by
  simp only [PqxdhDeploymentSecrecy.game, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨born, bornMember, supported⟩ := supported
  rcases born with ⟨_ | constructed, after⟩
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    cases reached
  · simp only [support_map, Set.mem_image] at supported
    obtain ⟨executed, executedMember, rfl⟩ := supported
    cases reached
    have invariant := OracleComp.simulateQ_run_preserves_inv_of_query
      (PqxdhDeploymentSecrecy.handler setup codec checks route constructed.seed bounds)
      (fun state => PqxdhDeploymentEligibility.Agree setup codec
        (PqxdhDeploymentNative.initial (KemSK := KemSK) constructed).native.shared.2.server.server.identity
        state.1.transcript state.2.native)
      (fun query state agree result member => PqxdhDeploymentEligibility.experiment_step setup codec checks route
        constructed.seed bounds _ query state agree result member)
      (PqxdhDeploymentInterface.asModeO mode adversary) (Ledger.empty, PqxdhDeploymentNative.initial constructed)
      (PqxdhDeploymentEligibility.agree_initial setup codec constructed) _ executedMember
    obtain ⟨fields, written, identity⟩ := invariant.builds _ built
    obtain ⟨response, read, _, _, serverId, _, _⟩ := phase2 fields _ written
    obtain ⟨seed, rfl, _⟩ := PqxdhLiveServerConstruction.construct_origin setup.joint ensureInit identityIndex
      setup.serverKeyId none runtime after constructed bornMember
    rw [read, Option.bind_some, serverId, identity]
    rfl

set_option linter.deprecated false in
/-- On every outcome of the experiment, a session that matches owner `c` before its acceptance matches it with the pin of the protected binding (`build_pin`). -/
theorem matched_pinned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds
      mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (reached : outcome.1 = some (created, output, final))
    (c : Nat) (before : List Reg) (raw : Pqxdh.Bytes) (found : accepted c (regsOf final.1.transcript) = some (before, raw))
    (matched : Matched setup.source.crypto codec c before raw) :
    PinnedMatch setup.source.crypto codec c (protectedBinding setup created).1 before raw := by
  obtain ⟨session, acceptRaw, candidate, keys, payload, reply, record, acceptMember, candidateEq, keysEq, publishedEq,
    buildMember, frameRaw, frameReply⟩ := matched
  have prefixed := PqxdhDeploymentServerAuthEvent.accepted_prefix c _ before raw found
  have built := build_entry final.1.transcript session payload reply (prefixed.subset buildMember)
  exact ⟨session, acceptRaw, candidate, keys, payload, reply, record, acceptMember, candidateEq, keysEq, publishedEq,
    buildMember, build_pin setup codec checks route ensureInit identityIndex phase2 bounds mode adversary runtime outcome
      supported created output final reached session payload reply built, frameRaw, frameReply⟩

set_option linter.deprecated false in
/-- On every outcome of the experiment, CE-A1 with the pinned matching is CE-A1 with the public matching (`matched_pinned`); with `noFailure_noPinnedMatch` the two events coincide there. -/
theorem noPinnedMatch_noFailure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) (c : Nat)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds
      mode adversary).run runtime))
    (event : A1NoPinnedMatch setup codec c outcome) : A1NoFailure setup codec c outcome := by
  obtain ⟨created, output, final, found, noFailure, before, raw, acceptedEq, bound, unpinned⟩ := event
  exact ⟨created, output, final, found, noFailure, before, raw, acceptedEq, bound, fun matched => unpinned
    (matched_pinned setup codec checks route ensureInit identityIndex phase2 bounds mode adversary runtime outcome
      supported created output final found c before raw acceptedEq matched)⟩

set_option linter.deprecated false in
/-- Theorem CE-A1 (plan section 10, option (b) of section 19), with the public pinned matching in place of the plan's eleven-field common session: in the common deployment experiment with a generated Server seed, for a budget-respecting adversary, every identity index and every initialization runtime, the probability that some Beacon `c`, pinned to the constructed Server's identity and key ID before its acceptance, accepted with no session that matches it with that pin and published the decoded record it accepted earlier (`A1NoPinnedMatch`), on a run with `NoBundleFailure_c`, is at most the sum over the `qCreate` creation indices of the Server-authentication bound of `R_c`, with the bills of every constructed reduction. Premises: the approved Phase 1, Phase 2 and frame read-back contracts, `ReadWritable`, `X25519ClassLaw`, `X25519ScalarSpread`, `SourceFullCorrect`, `HasAttachedVerificationAdapter`, the KEM base caps and the query caps of each `R_c`. -/
theorem ce_a1 (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) (caps : KemCaps)
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
    (𝒟[(fun outcome => @decide (∃ c, A1NoPinnedMatch setup codec c outcome) (Classical.propDecidable _)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime]
        {true}).toReal ≤
      ∑ c : Fin budget.create, serverAuthBound setup codec checks caps
        (serverAuthAdversary setup codec route bounds mode adversary c) qCoin Q qH qHash fallback signatureFallback ∧
    ∀ c, PqxdhServerAuthCommonAuthentication.ReductionBills setup codec checks caps
      (serverAuthAdversary setup codec route bounds mode adversary c) qCoin Q qH qHash qTotal qFinish fallback
      signatureFallback := by
  have summed := a1_sum setup codec checks caps bounded route ensureInit identityIndex phase1 phase2 frameBack writable
    law spread correct adapter bounds mode adversary budget respects runtime qCoin Q qH qHash qTotal qFinish
    reductionCaps fallback signatureFallback
  refine ⟨le_trans ?_ summed.1, summed.2⟩
  set run := (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run
    runtime
  have finite : 𝒟[(fun outcome => @decide (∃ c, A1At setup codec c outcome) (Classical.propDecidable _)) <$> run]
      {true} ≠ ⊤ := by
    rw [evalDist_apply_singleton]
    exact probOutput_ne_top
  refine ENNReal.toReal_mono finite ?_
  classical
  rw [UniformTargetSelection.chance_eq, UniformTargetSelection.chance_eq]
  exact probEvent_mono fun outcome member ⟨c, event⟩ => ⟨c, noFailure_a1At setup codec c outcome
    (noPinnedMatch_noFailure setup codec checks route ensureInit identityIndex phase2 bounds mode adversary runtime c
      outcome member event)⟩

end BeaconcryptCore.Computational.PqxdhDeploymentServerAuth

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.a1At_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.a1At_merge

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.probEvent_bind_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.probEvent_bind_le

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.a1_le_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.a1_le_ordered

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.a1_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.a1_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.owners_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.owners_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.owners_foldl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.owners_foldl

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.unmatched_created' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.unmatched_created

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.compiled_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.compiled_owners

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.a1_range' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.a1_range

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.a1_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.a1_sum

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.noFailure_a1At' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.noFailure_a1At

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.pinned_matched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.pinned_matched

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.noFailure_noPinnedMatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.noFailure_noPinnedMatch

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.build_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.build_entry

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.build_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.build_pin

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.matched_pinned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.matched_pinned

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.noPinnedMatch_noFailure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.noPinnedMatch_noFailure

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.ce_a1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuth.ce_a1
