-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineOrigin
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant

/-!
# AG lift R1: the b2s Server pin on the common deployment experiment (CE-12 P4 step 2, design-v2 section 7.6)

The b2s Server-pin row of design-v2 section 7.6 (ProVerif L2-origin, b2s-C2 and b2s-C4: the Beacon that sent a record the Server accepted was pinned to this Server), from symbolic-only to computational, through the record-level agreement fact of P2b (`PqxdhDeploymentHeadlineAgree`):

- `PinAt g`: an accepted Server raw receive on a peer key ID designating `g = (i, k)`, with a decoded frame, whose counterpart owner `k` was created with a pin (the public summary's created binding) different from the Server identity field read with the Phase 2 reader from session `i`'s first build response (`PqxdhDeploymentTranscript.buildOf`). `PinFailure`, `pinEvent`, the claim `pinClaim` (the receiving handle of the first failing entry) and `pin_named`.
- Containment (`pin_agree`): on every CTX-world outcome with the two ideal-world facts (`PqxdhDeploymentHeadlinePinInvariant.PinFacts`), `dec_g ∧ ISs_g` of the pin failure implies AG's failure event (`PqxdhDeploymentHeadlineAgree.AgreeFailure`). The receiving peer holds slot 0 (Server converse) and a counterpart of it is an owner holding slot 0, hence owner `k` (Beacon restriction). If that owner produced the frame from a seal whose AD is both the peer's AD `associatedBytes(Server identity, peer identity)` and its own shell AD, then by fact (a) and the injectivity of the extracted `build_associated_data` (`PqxdhDeploymentHeadlineAgree.owner_pin`) its created pin is the record control's Server identity, which by fact (b) and `Phase2ReadBack` is the identity read from the build response.
- `idealAuth_pin_zero`: in `idealAuth` with the ideal environment of the target, the event has probability zero (`PqxdhDeploymentHeadlineAgree.agreement_statement`).
- `ce_pin_b2s_target`, `ce_pin_b2s`: on the deployment experiment the pin failure has probability at most the sum over the targets of `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g)`, each with coefficient one (`PqxdhDeploymentHeadlineChain.chain_server`, `PqxdhDeploymentHeadlineChain.auth_le` and the zero in `idealAuth`); no anomaly term and no publication term.
- CE-OR b2s with the Server pin field: `OriginPinFailure` (the frozen b2s origin failure `PqxdhDeploymentHeadlineEvents.OriginFailure .b2s` or the pin failure), `originPinEvent`, `originPinClaim`, `originPin_named`, `originPin_contain`, `idealAuth_originPin_le`, and `ce_or_pin_b2s_target`, `ce_or_pin_b2s`: at most the sum over the targets of `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g) + publicationTerm budget`, the frozen `PqxdhDeploymentHeadlineOrigin.ce_or_b2s` form with the pin field computational.

Premises: those of the frozen `ce_or_b2s` (`FunctionalDecapsulation`, `Phase1ReadBack`, `Phase2ReadBack`, `SourceFullCorrect`, `KemBound`, the initializer's query bound and `budget.Respects`; `FrameReadBack` only for the combined form); the AEAD forgery fallback is a parameter of the integrity loss. No new assumption or contract. Not claimed here: the mode-O plaintext rows (R2), the root, and any statement in the later-quantum mode. No `PqxdhBoundary*` module is imported.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn summarize buildOf)
open PqxdhDeploymentHeadlineEvents (firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePinInvariant (PinFacts)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

variable {Reader Response X : Type}

section Event
variable (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64) (budget : Budget)
  (route : RawCtxServerRouting.SenderDecoder)

/-- `PinAt g`: the entry is an accepted Server raw receive on a peer key ID designating `g` whose counterpart owner `g.2` was created with a pin different from the Server identity read with the Phase 2 reader from session `g.1`'s build response. -/
def PinAt (g : Fin budget.accept × Fin budget.capacity) (transcript : List Entry) (entry : Entry) : Prop :=
  ∃ raw decrypted keyId frame, entry.received = some (.server, raw, .Some decrypted) ∧ route raw = some keyId ∧
    designateIn crypto codec serverKid budget transcript (.peer keyId) = some g ∧ codec.frameRead raw = some frame ∧
    ∃ pin keyId' response identity, (summarize transcript).owners[g.2.val]? = some (pin, keyId') ∧
      buildOf transcript g.1.val = some response ∧
      (codec.read2 response.serialized).bind codec.serverIdentity = some identity ∧ pin ≠ identity

/-- The entry fails the pin field for some target. -/
def PinFailsAt (transcript : List Entry) (entry : Entry) : Prop :=
  ∃ g, PinAt crypto codec serverKid budget route g transcript entry

/-- The pin failure (design-v2 section 7.6, b2s Server pin): some entry of the final transcript fails the pin field for some target. -/
def PinFailure (observed : Observed X) : Prop :=
  ∃ entry ∈ observed.2.1.transcript, PinFailsAt crypto codec serverKid budget route observed.2.1.transcript entry

open Classical in
/-- The pin failure as a Boolean of the observation. -/
noncomputable def pinEvent (observed : Observed X) : Bool :=
  decide (PinFailure crypto codec serverKid budget route observed)

/-- The claim of the pin failure: the receiving handle of the first transcript entry that fails it. -/
noncomputable def pinClaim (observed : Observed X) : Option Handle :=
  firstHandle (fun _ entry => PinFailsAt crypto codec serverKid budget route observed.2.1.transcript entry)
    (receivedHandle route) observed.2.1.transcript

/-- A pin failure names a designated claim: the first failing entry's receiving Server peer designates a target. -/
theorem pin_named (observed : Observed X)
    (failed : pinEvent crypto codec serverKid budget route observed = true) :
    (PqxdhDeploymentKemTransfer.target crypto codec serverKid budget
      (pinClaim crypto codec serverKid budget route) observed).isSome := by
  classical
  unfold pinEvent at failed
  obtain ⟨entry, member, g, witness⟩ := of_decide_eq_true failed
  obtain ⟨raw, decrypted, keyId, frame, received, routed, designated, framed, rest⟩ := id witness
  obtain ⟨before, after, split⟩ := List.append_of_mem member
  have named : (receivedHandle route entry).isSome := by
    simp [receivedHandle, received, PqxdhRecordLiftIdeal.receivingHandle, routed]
  obtain ⟨claimed, found⟩ := Option.isSome_iff_exists.mp (firstHandle_isSome
    (fun _ entry => PinFailsAt crypto codec serverKid budget route observed.2.1.transcript entry) (receivedHandle route)
    _ before entry after split ⟨g, witness⟩ named)
  obtain ⟨before', entry', after', split', ⟨g', raw', decrypted', keyId', frame', received', routed', designated',
    _, _⟩, handled⟩ := firstHandle_some _ _ _ claimed found
  simp only [receivedHandle, received', Option.bind_some, PqxdhRecordLiftIdeal.receivingHandle, routed',
    Option.map_some, Option.some.injEq] at handled
  subst handled
  unfold PqxdhDeploymentKemTransfer.target pinClaim
  rw [found, Option.bind_some, designated']
  rfl

end Event

/-! ### CE-OR b2s with the Server pin field -/

section OriginPin
variable (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64) (budget : Budget)
  (route : RawCtxServerRouting.SenderDecoder)

/-- The b2s origin failure with the Server pin field: the frozen b2s origin failure (`PqxdhDeploymentHeadlineEvents.OriginFailure .b2s`: an accepted Server raw receive on a designated peer whose decoded frame its CE counterpart did not publish before) or the pin failure. -/
def OriginPinFailure (observed : Observed X) : Prop :=
  PqxdhDeploymentHeadlineEvents.OriginFailure crypto codec serverKid budget route .b2s observed ∨
    PinFailure crypto codec serverKid budget route observed

open Classical in
/-- The b2s origin failure with the Server pin field as a Boolean of the observation. -/
noncomputable def originPinEvent (observed : Observed X) : Bool :=
  decide (OriginPinFailure crypto codec serverKid budget route observed)

open Classical in
/-- The claim of the b2s origin failure with the Server pin field: the frozen origin claim when the origin fails, else the pin claim. -/
noncomputable def originPinClaim (observed : Observed X) : Option Handle :=
  if PqxdhDeploymentHeadlineEvents.OriginFailure crypto codec serverKid budget route .b2s observed then
    PqxdhDeploymentHeadlineEvents.orClaim crypto codec serverKid budget route .b2s observed
  else pinClaim crypto codec serverKid budget route observed

/-- The b2s origin failure with the Server pin field names a designated claim. -/
theorem originPin_named (observed : Observed X)
    (failed : originPinEvent crypto codec serverKid budget route observed = true) :
    (PqxdhDeploymentKemTransfer.target crypto codec serverKid budget
      (originPinClaim crypto codec serverKid budget route) observed).isSome := by
  classical
  simp only [originPinEvent, decide_eq_true_eq] at failed
  by_cases origin : PqxdhDeploymentHeadlineEvents.OriginFailure crypto codec serverKid budget route .b2s observed
  · have named := PqxdhDeploymentHeadlineEvents.origin_named crypto codec serverKid budget route .b2s observed
      (by simp only [PqxdhDeploymentHeadlineEvents.originEvent, decide_eq_true_eq]; exact origin)
    unfold PqxdhDeploymentKemTransfer.target at named ⊢
    simp only [originPinClaim, origin, ↓reduceIte]
    exact named
  · have named := pin_named crypto codec serverKid budget route observed
      (by simp only [pinEvent, decide_eq_true_eq]; exact failed.resolve_left origin)
    unfold PqxdhDeploymentKemTransfer.target at named ⊢
    simp only [originPinClaim, origin, ↓reduceIte]
    exact named

end OriginPin


/-! ### Probability helpers -/

/-- Support-restricted monotonicity of a Boolean event's probability. -/
theorem chance_mono_support {α : Type} (run : ProbComp α) (first second : α → Bool)
    (implies : ∀ a ∈ support run, first a = true → second a = true) :
    𝒟[first <$> run] {true} ≤ 𝒟[second <$> run] {true} := by
  rw [evalDist_apply_singleton, evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput,
    probEvent_map, probEvent_map]
  exact probEvent_mono fun a member held => implies a member held

/-- Union bound for Boolean events. -/
theorem chance_or_le {α : Type} (run : ProbComp α) (first second : α → Bool) :
    𝒟[(fun a => first a || second a) <$> run] {true} ≤ 𝒟[first <$> run] {true} + 𝒟[second <$> run] {true} := by
  rw [evalDist_apply_singleton, evalDist_apply_singleton, evalDist_apply_singleton, ← probEvent_eq_eq_probOutput,
    ← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, probEvent_map, probEvent_map, probEvent_map]
  refine le_trans (probEvent_mono fun a _ held => ?_) (probEvent_or_le run _ _)
  simpa only [Function.comp, Bool.or_eq_true] using held

/-! ### The containment -/

section Contain
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
  (budget : Budget) (route : RawCtxServerRouting.SenderDecoder)

/-- The containment: on every CTX-world outcome with the two ideal-world facts, `dec_g ∧ ISs_g` of the pin failure implies AG's failure event. -/
theorem pin_agree {E : Type} (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (g : Fin budget.accept × Fin budget.capacity)
    (result : PqxdhRecordLiftIdeal.Client 2 E X × PqxdhRecordLiftIdeal.CtxPrivate 2) (facts : PinFacts codec result)
    (held : serverSlotted setup codec budget (pinEvent setup.source.crypto codec setup.serverKeyId budget route)
      (pinClaim setup.source.crypto codec setup.serverKeyId budget route) g (ctxView result) = true) :
    AgreeFailure codec route result := by
  classical
  unfold serverSlotted at held
  obtain ⟨decided, server⟩ := of_decide_eq_true held
  obtain ⟨view, found, _, handle, claimed, designated⟩ :=
    PqxdhDeploymentHeadlineContain.decision_unpack setup codec budget _ _ g (ctxView result) decided
  have slots := server view found
  obtain ⟨value, valueMember, rfl⟩ : ∃ value ∈ result.1.1, view = (value.2.1.1, value.2.1.2, value.2.2) := by
    rcases existing : result.1.1 with _ | value
    · simp [ctxView, PqxdhRecordLiftIdeal.viewOf, existing] at found
    · simp only [ctxView, PqxdhRecordLiftIdeal.viewOf, existing, Option.map_some, Option.some.injEq] at found
      exact ⟨value, rfl, found.symm⟩
  obtain ⟨before, entry, after, split, ⟨g', raw, decrypted, keyId, frame, received, routed, designated', framed, pin,
    keyId', response, identity, ownersFound, built, read, differ⟩, handled⟩ := firstHandle_some _ _ _ handle claimed
  simp only [receivedHandle, received, Option.bind_some, PqxdhRecordLiftIdeal.receivingHandle, routed,
    Option.map_some, Option.some.injEq] at handled
  subst handled
  rw [designated] at designated'
  cases designated'
  obtain ⟨zero, _⟩ := PqxdhDeploymentHeadlineContain.designation_peer setup.source.crypto codec setup.serverKeyId budget g
    (ctxView result).slots value.2.1.2.transcript keyId slots designated
  have entryMember : entry ∈ value.2.1.2.transcript := by
    rw [split]
    simp
  refine ⟨value, valueMember, entry, entryMember, .server, raw, decrypted, .peer keyId, 0, frame, received,
    by simp [PqxdhRecordLiftIdeal.receivingHandle, routed], zero, framed, ?_⟩
  rintro ⟨other, ad, counter, _, adPeer, adOther⟩
  obtain ⟨owner, rfl, ownerSlot⟩ := PqxdhDeploymentHeadlineAgree.counterpart_peer _ 0 keyId other counter
  have ownerEq : owner = g.2.val := slots.2.1 owner 0 ownerSlot
  subst ownerEq
  cases existing : result.1.2.server with
  | none => simp [PqxdhDeploymentHeadlineAgreeSeal.handleAd, existing] at adPeer
  | some serverState =>
    cases peerFound : serverState.peers keyId with
    | none => simp [PqxdhDeploymentHeadlineAgreeSeal.handleAd, existing, peerFound] at adPeer
    | some peer =>
      simp only [PqxdhDeploymentHeadlineAgreeSeal.handleAd, existing, peerFound, Option.bind_some, Option.map_some,
        Option.some.injEq] at adPeer
      subst ad
      simp only [PqxdhDeploymentHeadlineAgreeSeal.handleAd, Option.bind_eq_some_iff] at adOther
      obtain ⟨phase, phaseFound, phaseAd⟩ := adOther
      cases phase with
      | inactive _ => cases phaseAd
      | established shell kernel =>
        have same : PqxdhRefinement.absBytes shell.associatedData =
            RawCtxServerRouting.associatedBytes serverState.identity peer.identity := Option.some.inj phaseAd
        obtain ⟨pin', keyId'', beacon, ownersFound', built'⟩ := (facts value valueMember).2 g.2.val shell kernel phaseFound
        rw [ownersFound] at ownersFound'
        cases ownersFound'
        have pinEq := (PqxdhDeploymentHeadlineAgree.owner_pin serverState.identity peer.identity shell same pin beacon
          built').1
        obtain ⟨payload, buildMember⟩ := PqxdhDeploymentKeyMatch.buildOf_mem _ _ _ built
        obtain ⟨fields, written, fieldsIdentity⟩ := (facts value valueMember).1 serverState existing _ buildMember
        obtain ⟨decoded, readEq, _, _, identityEq, _, _⟩ := phase2 fields _ written
        rw [readEq, Option.bind_some, identityEq, fieldsIdentity] at read
        exact differ (pinEq.trans (Option.some.inj read))

/-- A per-target decision on a view transfers to another event and claim that hold and agree on the view's observation. -/
theorem decision_transfer {E : Type} (event event' : Observed X → Bool) (claim claim' : Observed X → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (view : View 2 E X)
    (held : (viewObserved view).any (decisionOn setup codec budget event claim g) = true)
    (transfer : ∀ observed, viewObserved view = some observed → event observed = true →
      event' observed = true ∧ claim' observed = claim observed) :
    (viewObserved view).any (decisionOn setup codec budget event' claim' g) = true := by
  rcases found : viewObserved view with _ | observed
  · rw [found] at held
    cases held
  · rw [found] at held
    simp only [Option.any_some, decisionOn, Bool.and_eq_true, decide_eq_true_eq] at held ⊢
    obtain ⟨happened', claimEq⟩ := transfer observed found held.1
    refine ⟨happened', ?_⟩
    unfold PqxdhDeploymentKemTransfer.target at held ⊢
    rw [claimEq]
    exact held.2

/-- The containment of the b2s origin failure with the Server pin field: on every CTX-world outcome with the two ideal-world facts, `dec_g ∧ ISs_g` of it implies the record lift's unpublished-accept event (the frozen origin containment) or AG's failure event (`pin_agree`). -/
theorem originPin_contain {E : Type} (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (g : Fin budget.accept × Fin budget.capacity)
    (result : PqxdhRecordLiftIdeal.Client 2 E X × PqxdhRecordLiftIdeal.CtxPrivate 2) (facts : PinFacts codec result)
    (held : serverSlotted setup codec budget (originPinEvent setup.source.crypto codec setup.serverKeyId budget route)
      (originPinClaim setup.source.crypto codec setup.serverKeyId budget route) g (ctxView result) = true) :
    PqxdhRecordLiftIdeal.unpublishedEvent codec route (ctxView result) = true ∨ AgreeFailure codec route result := by
  classical
  simp only [serverSlotted, decide_eq_true_eq] at held
  obtain ⟨decided, server⟩ := held
  rcases found : viewObserved (ctxView result) with _ | observed
  · rw [found] at decided
    cases decided
  · have happened : originPinEvent setup.source.crypto codec setup.serverKeyId budget route observed = true := by
      rw [found] at decided
      simp only [Option.any_some, decisionOn, Bool.and_eq_true] at decided
      exact decided.1
    simp only [originPinEvent, decide_eq_true_eq] at happened
    by_cases origin : PqxdhDeploymentHeadlineEvents.OriginFailure setup.source.crypto codec setup.serverKeyId budget route
      .b2s observed
    · left
      apply PqxdhDeploymentHeadlineContain.origin_b2s setup codec budget route g (ctxView result)
      simp only [serverSlotted, decide_eq_true_eq]
      refine ⟨decision_transfer setup codec budget _ _ _ _ g _ decided fun other same _ => ?_, server⟩
      rw [found, Option.some.injEq] at same
      subst same
      refine ⟨by simp only [PqxdhDeploymentHeadlineEvents.originEvent, decide_eq_true_eq]; exact origin, ?_⟩
      simp only [originPinClaim, origin, ↓reduceIte]
    · right
      apply pin_agree setup codec budget route phase2 g result facts
      simp only [serverSlotted, decide_eq_true_eq]
      refine ⟨decision_transfer setup codec budget _ _ _ _ g _ decided fun other same _ => ?_, server⟩
      rw [found, Option.some.injEq] at same
      subst same
      refine ⟨by simp only [pinEvent, decide_eq_true_eq]; exact happened.resolve_left origin, ?_⟩
      simp only [originPinClaim, origin, ↓reduceIte]

end Contain


/-! ### The pin field in `idealAuth` and on the common deployment experiment -/

section Headline
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A : Type}

/-- **R1 in `idealAuth`.** With the ideal environment of the target of `g`, the probability that the record lift's view of `idealAuth` ends with `dec_g ∧ ISs_g` of the pin failure is zero: such an outcome is an AG failure (`pin_agree`, with the two ideal-world facts `PqxdhDeploymentHeadlinePinInvariant.idealAuth_pinFacts`), and AG's failure event has probability zero (`PqxdhDeploymentHeadlineAgree.agreement_statement`). -/
theorem idealAuth_pin_zero (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    𝒟[serverSlotted setup codec budget (pinEvent setup.source.crypto codec setup.serverKeyId budget route)
        (pinClaim setup.source.crypto codec setup.serverKeyId budget route) g <$>
      (ctxView <$> idealAuth setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary)] {true} = 0 := by
  apply nonpos_iff_eq_zero.mp
  rw [Functor.map_map]
  calc _ ≤ 𝒟[agreeEvent codec route <$> idealAuth setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary] {true} :=
        chance_mono_support _ _ _ fun result member held => by
          simp only [agreeEvent, decide_eq_true_eq]
          exact (pin_agree setup codec budget route phase2 g result
            (PqxdhDeploymentHeadlinePinInvariant.idealAuth_pinFacts setup codec checks route (Target.ofCE budget g)
              ensureInit 0 runtime bounds mode adversary result member) held)
    _ = 0 := PqxdhDeploymentHeadlineAgree.agreement_statement setup codec route setup.serverKeyId bounds 2 _ mode
        adversary

/-- **R1, per target** (design-v2 section 7.6, b2s Server pin): the probability that the deployment experiment ends with a pin failure whose first failing entry's receiving Server peer designates `g` is at most `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g)`, each with coefficient one; no anomaly term and no publication term. -/
theorem ce_pin_b2s_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun outcome => decide (happens (pinEvent setup.source.crypto codec setup.serverKeyId budget route)
        outcome = true ∧ designated setup.source.crypto codec setup.serverKeyId budget
          (pinClaim setup.source.crypto codec setup.serverKeyId budget route) outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
        (pinEvent setup.source.crypto codec setup.serverKeyId budget route)
        (pinClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
        (pinEvent setup.source.crypto codec setup.serverKeyId budget route)
        (pinClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime) +
      authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (serverSlotted setup codec budget (pinEvent setup.source.crypto codec setup.serverKeyId budget route)
          (pinClaim setup.source.crypto codec setup.serverKeyId budget route) g) := by
  have chain := PqxdhDeploymentHeadlineChain.chain_server setup functional codec checks route ensureInit phase1 phase2
    correct bounds mode adversary budget respects (pinEvent setup.source.crypto codec setup.serverKeyId budget route)
    (pinClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime
  have lift := PqxdhDeploymentHeadlineChain.auth_le setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects g runtime fallback
    (serverSlotted setup codec budget (pinEvent setup.source.crypto codec setup.serverKeyId budget route)
      (pinClaim setup.source.crypto codec setup.serverKeyId budget route) g)
  rw [idealAuth_pin_zero setup codec checks route ensureInit phase2 bounds mode adversary budget g runtime,
    zero_add] at lift
  calc _ ≤ _ := chain
    _ ≤ (authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
          (serverSlotted setup codec budget (pinEvent setup.source.crypto codec setup.serverKeyId budget route)
            (pinClaim setup.source.crypto codec setup.serverKeyId budget route) g) +
        ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
          (pinEvent setup.source.crypto codec setup.serverKeyId budget route)
          (pinClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime)) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
          (pinEvent setup.source.crypto codec setup.serverKeyId budget route)
          (pinClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime) :=
        add_le_add (add_le_add lift le_rfl) le_rfl
    _ = _ := by ring

/-- **R1** (design-v2 section 7.6, b2s Server pin, `ce_pin_b2s`): the probability that the deployment experiment ends with a pin failure (an accepted Server raw receive on a peer designating a target whose counterpart owner was created with a pin different from the Server identity read from the target session's build response) is at most the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g)`, each with coefficient one. -/
theorem ce_pin_b2s (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[(fun outcome => happens (pinEvent setup.source.crypto codec setup.serverKeyId budget route) outcome) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
            (pinEvent setup.source.crypto codec setup.serverKeyId budget route)
            (pinClaim setup.source.crypto codec setup.serverKeyId budget route) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
            (pinEvent setup.source.crypto codec setup.serverKeyId budget route)
            (pinClaim setup.source.crypto codec setup.serverKeyId budget route) (g.1, g.2.castSucc) runtime) +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
            fallback caps qInit (serverSlotted setup codec budget
              (pinEvent setup.source.crypto codec setup.serverKeyId budget route)
              (pinClaim setup.source.crypto codec setup.serverKeyId budget route) (g.1, g.2.castSucc))) := by
  rw [PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds mode adversary
    budget respects _ _ runtime (pin_named setup.source.crypto codec setup.serverKeyId budget route)]
  exact Finset.sum_le_sum fun g _ => ce_pin_b2s_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound bounds mode adversary budget respects runtime fallback (g.1, g.2.castSucc)

/-- With the ideal environment of the target of `g`, the probability that the record lift's view of `idealAuth` ends with `dec_g ∧ ISs_g` of the b2s origin failure with the Server pin field is at most `publicationTerm budget`: the unpublished-accept part is the frozen bound (`PqxdhDeploymentHeadlineOrigin.unpublished_final`) and the pin part has probability zero (AG). -/
theorem idealAuth_originPin_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[serverSlotted setup codec budget (originPinEvent setup.source.crypto codec setup.serverKeyId budget route)
        (originPinClaim setup.source.crypto codec setup.serverKeyId budget route) g <$>
      (ctxView <$> idealAuth setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary)] {true} ≤ publicationTerm budget := by
  have final := PqxdhDeploymentHeadlineOrigin.unpublished_final setup codec checks route caps bounded ensureInit qInit
    initBound frameReadBack bounds mode adversary budget respects g runtime
  have zero := PqxdhDeploymentHeadlineAgree.agreement_statement setup codec route setup.serverKeyId bounds 2
    (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) mode adversary
  rw [Functor.map_map] at final ⊢
  calc _ ≤ 𝒟[(fun result => PqxdhRecordLiftIdeal.unpublishedEvent codec route (ctxView result) ||
        agreeEvent codec route result) <$> idealAuth setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary] {true} :=
        chance_mono_support _ _ _ fun result member held => by
          rcases originPin_contain setup codec budget route phase2 g result
            (PqxdhDeploymentHeadlinePinInvariant.idealAuth_pinFacts setup codec checks route (Target.ofCE budget g)
              ensureInit 0 runtime bounds mode adversary result member) held with unpublished | failure
          · simp only [unpublished, Bool.true_or]
          · simp only [agreeEvent, failure, decide_true, Bool.or_true]
    _ ≤ _ := chance_or_le _ _ _
    _ ≤ publicationTerm budget := by
        rw [zero, add_zero]
        exact final

/-- **CE-OR b2s with the Server pin field, per target** (design-v2 sections 4.2 and 7.6): the probability that the deployment experiment ends with a b2s origin failure or a pin failure whose claimed receiving Server peer designates `g` is at most `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g) + publicationTerm budget`, each with coefficient one; no anomaly term. -/
theorem ce_or_pin_b2s_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun outcome => decide (happens (originPinEvent setup.source.crypto codec setup.serverKeyId budget route)
        outcome = true ∧ designated setup.source.crypto codec setup.serverKeyId budget
          (originPinClaim setup.source.crypto codec setup.serverKeyId budget route) outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
        (originPinEvent setup.source.crypto codec setup.serverKeyId budget route)
        (originPinClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
        (originPinEvent setup.source.crypto codec setup.serverKeyId budget route)
        (originPinClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime) +
      authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (serverSlotted setup codec budget (originPinEvent setup.source.crypto codec setup.serverKeyId budget route)
          (originPinClaim setup.source.crypto codec setup.serverKeyId budget route) g) +
      publicationTerm budget := by
  have chain := PqxdhDeploymentHeadlineChain.chain_server setup functional codec checks route ensureInit phase1 phase2
    correct bounds mode adversary budget respects (originPinEvent setup.source.crypto codec setup.serverKeyId budget route)
    (originPinClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime
  have lift := PqxdhDeploymentHeadlineChain.auth_le setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects g runtime fallback
    (serverSlotted setup codec budget (originPinEvent setup.source.crypto codec setup.serverKeyId budget route)
      (originPinClaim setup.source.crypto codec setup.serverKeyId budget route) g)
  have final := idealAuth_originPin_le setup codec checks route caps bounded ensureInit qInit initBound phase2
    frameReadBack bounds mode adversary budget respects g runtime
  calc _ ≤ _ := chain
    _ ≤ ((publicationTerm budget +
          authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
            (serverSlotted setup codec budget (originPinEvent setup.source.crypto codec setup.serverKeyId budget route)
              (originPinClaim setup.source.crypto codec setup.serverKeyId budget route) g)) +
        ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
          (originPinEvent setup.source.crypto codec setup.serverKeyId budget route)
          (originPinClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime)) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
          (originPinEvent setup.source.crypto codec setup.serverKeyId budget route)
          (originPinClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime) :=
        add_le_add (add_le_add (lift.trans (add_le_add final le_rfl)) le_rfl) le_rfl
    _ = _ := by ring

/-- **CE-OR b2s with the Server pin field** (`ce_or_pin_b2s`, design-v2 sections 4.2 and 7.6): the probability that the deployment experiment ends with a b2s origin failure or a pin failure is at most the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g) + publicationTerm budget`, each with coefficient one; no anomaly term. -/
theorem ce_or_pin_b2s (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[(fun outcome => happens (originPinEvent setup.source.crypto codec setup.serverKeyId budget route) outcome) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
            (originPinEvent setup.source.crypto codec setup.serverKeyId budget route)
            (originPinClaim setup.source.crypto codec setup.serverKeyId budget route) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
            (originPinEvent setup.source.crypto codec setup.serverKeyId budget route)
            (originPinClaim setup.source.crypto codec setup.serverKeyId budget route) (g.1, g.2.castSucc) runtime) +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
            fallback caps qInit (serverSlotted setup codec budget
              (originPinEvent setup.source.crypto codec setup.serverKeyId budget route)
              (originPinClaim setup.source.crypto codec setup.serverKeyId budget route) (g.1, g.2.castSucc)) +
          publicationTerm budget) := by
  rw [PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds mode adversary
    budget respects _ _ runtime (originPin_named setup.source.crypto codec setup.serverKeyId budget route)]
  exact Finset.sum_le_sum fun g _ => ce_or_pin_b2s_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback
    (g.1, g.2.castSucc)

end Headline

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.pin_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.pin_named

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.originPin_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.originPin_named

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.chance_mono_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.chance_mono_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.chance_or_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.chance_or_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.pin_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.pin_agree

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.decision_transfer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.decision_transfer

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.originPin_contain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.originPin_contain

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.idealAuth_pin_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.idealAuth_pin_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.ce_pin_b2s_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.ce_pin_b2s_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.ce_pin_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.ce_pin_b2s

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.idealAuth_originPin_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.idealAuth_originPin_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.ce_or_pin_b2s_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.ce_or_pin_b2s_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.ce_or_pin_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.ce_or_pin_b2s
