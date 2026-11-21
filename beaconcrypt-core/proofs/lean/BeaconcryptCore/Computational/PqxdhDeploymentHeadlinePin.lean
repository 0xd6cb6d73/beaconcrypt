-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCtxCollision
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineOrigin

/-!
# The computational b2s Server-pin bounds

The pin and combined origin/pin events retain their deployment definitions and all public premises. Actual CTX support supplies cached transcript receipts for installed owner shells and Server peer bindings. Outside a collision in that shared cache, equal installed AD151 values force equal response identity fields; the agreement theorem then excludes pin failure. The actual CTX birthday bound accounts for the collision case without a new security premise.

`ce_pin_b2s_target` appends `PinCollision.term budget` to the existing KEM, slot and authentication losses. `ce_or_pin_b2s_target` appends the same term after the existing publication term. The summed forms pay this term inside each original target summand. The cap is `hash + sends + receives + 2*build + 2*finish`, and the term is `choose(cap,2)/2^512`. No event, distribution or primitive assumption changes.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin

section Support
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
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
  exact prEvent_mono_of_support _ _ _ fun a member held => implies a member held

/-- Union bound for Boolean events. -/
theorem chance_or_le {α : Type} (run : ProbComp α) (first second : α → Bool) :
    𝒟[(fun a => first a || second a) <$> run] {true} ≤ 𝒟[first <$> run] {true} + 𝒟[second <$> run] {true} := by
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true,
    ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map, prEvent_map]
  refine le_trans (prEvent_mono_of_support _ _ _ fun a _ held => ?_) (prEvent_or_le run _ _)
  simpa only [Function.comp, Bool.or_eq_true] using held

/-! ### The containment -/

section Contain
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
  (budget : Budget) (route : RawCtxServerRouting.SenderDecoder)

/-- Outside a collision in the actual final shared cache, the two ideal-world facts turn the unchanged pin failure into agreement failure. -/
theorem pin_agree_of_noCollision {E : Type} (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (g : Fin budget.accept × Fin budget.capacity)
    (result : PqxdhRecordLiftIdeal.Client 2 E X × PqxdhRecordLiftIdeal.CtxPrivate 2) (facts : PinFacts codec result)
    (collisionFree : ¬ CacheHasCollision result.2.base.primitive.2)
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
            PqxdhRefinement.absBytes peer.binding.associatedData := Option.some.inj phaseAd
        obtain ⟨pin', keyId'', ownersFound', ownerReceipt⟩ :=
          (facts value valueMember).2.1 g.2.val shell kernel phaseFound
        rw [ownersFound] at ownersFound'
        cases ownersFound'
        have peerReceipt := (facts value valueMember).2.2 serverState existing keyId peer peerFound
        have samePin := PqxdhDeploymentHeadlinePinCollision.identity_eq_of_noCollision _
          ownerReceipt peerReceipt same collisionFree
        have pinEq : pin = serverState.identity := Subtype.ext ((PqxdhRefinement.absBytes_inj_iff _ _).mp samePin)
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

/-- Outside a collision in the actual final shared cache, combined b2s origin/pin failure implies unpublished acceptance or agreement failure. -/
theorem originPin_contain_of_noCollision {E : Type} (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (g : Fin budget.accept × Fin budget.capacity)
    (result : PqxdhRecordLiftIdeal.Client 2 E X × PqxdhRecordLiftIdeal.CtxPrivate 2) (facts : PinFacts codec result)
    (collisionFree : ¬ CacheHasCollision result.2.base.primitive.2)
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
      apply pin_agree_of_noCollision setup codec budget route phase2 g result facts collisionFree
      simp only [serverSlotted, decide_eq_true_eq]
      refine ⟨decision_transfer setup codec budget _ _ _ _ g _ decided fun other same _ => ?_, server⟩
      rw [found, Option.some.injEq] at same
      subst same
      refine ⟨by simp only [pinEvent, decide_eq_true_eq]; exact happened.resolve_left origin, ?_⟩
      simp only [originPinClaim, origin, ↓reduceIte]

/-- The unchanged pin failure is an agreement failure or an actual shared-cache collision. -/
theorem pin_agree_or_collision {E : Type} (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (g : Fin budget.accept × Fin budget.capacity)
    (result : PqxdhRecordLiftIdeal.Client 2 E X × PqxdhRecordLiftIdeal.CtxPrivate 2) (facts : PinFacts codec result)
    (held : serverSlotted setup codec budget (pinEvent setup.source.crypto codec setup.serverKeyId budget route)
      (pinClaim setup.source.crypto codec setup.serverKeyId budget route) g (ctxView result) = true) :
    AgreeFailure codec route result ∨ CacheHasCollision result.2.base.primitive.2 := by
  exact (Classical.em (CacheHasCollision result.2.base.primitive.2)).elim Or.inr
    (fun clear => Or.inl (pin_agree_of_noCollision setup codec budget route phase2 g result facts clear held))

/-- The combined origin/pin event is unpublished acceptance, agreement failure, or a shared-cache collision. -/
theorem originPin_contain_or_collision {E : Type} (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (g : Fin budget.accept × Fin budget.capacity)
    (result : PqxdhRecordLiftIdeal.Client 2 E X × PqxdhRecordLiftIdeal.CtxPrivate 2) (facts : PinFacts codec result)
    (held : serverSlotted setup codec budget (originPinEvent setup.source.crypto codec setup.serverKeyId budget route)
      (originPinClaim setup.source.crypto codec setup.serverKeyId budget route) g (ctxView result) = true) :
    PqxdhRecordLiftIdeal.unpublishedEvent codec route (ctxView result) = true ∨
      AgreeFailure codec route result ∨ CacheHasCollision result.2.base.primitive.2 := by
  exact (Classical.em (CacheHasCollision result.2.base.primitive.2)).elim
    (fun collides => Or.inr (Or.inr collides))
    (fun clear => (originPin_contain_of_noCollision setup codec budget route phase2 g result facts clear held).elim
      Or.inl (fun disagrees => Or.inr (Or.inl disagrees)))

end Contain
end Support

section Public
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn summarize buildOf)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePinInvariant (PinFacts)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
variable {Reader Response X : Type}
section Headline
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A : Type}

/-- In idealAuth the unchanged Server-pin failure is bounded by the actual BLAKE2b cache birthday term. -/
theorem idealAuth_pin_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[serverSlotted setup codec budget (pinEvent setup.source.crypto codec setup.serverKeyId budget route)
        (pinClaim setup.source.crypto codec setup.serverKeyId budget route) g <$>
      (ctxView <$> idealAuth setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary)] {true} ≤ PqxdhDeploymentHeadlinePinCollision.term budget := by
  classical
  rw [Functor.map_map]
  refine (chance_mono_support _ _ (fun result => agreeEvent codec route result ||
    decide (CacheHasCollision result.2.base.primitive.2)) ?_).trans ?_
  · intro result member held
    simpa only [Bool.or_eq_true, agreeEvent, decide_eq_true_eq] using
      pin_agree_or_collision setup codec budget route phase2 g result
        (PqxdhDeploymentHeadlinePinInvariant.idealAuth_pinFacts setup codec checks route (Target.ofCE budget g)
          ensureInit 0 runtime bounds mode adversary result member) held
  · refine (chance_or_le _ (agreeEvent codec route)
      (fun result => decide (CacheHasCollision result.2.base.primitive.2))).trans ?_
    rw [PqxdhDeploymentHeadlineAgree.agreement_statement setup codec route setup.serverKeyId bounds 2 _ mode
      adversary, zero_add]
    simpa only [PqxdhDeploymentHeadlinePinCollision.term, PqxdhDeploymentHeadlinePinCollision.hashCap] using
      PqxdhDeploymentHeadlinePinCtxCollision.idealAuth_collision setup codec checks route caps bounded
        (Target.ofCE budget g) ensureInit qInit initBound 0 runtime bounds mode budget adversary respects

/-- **R1, per target** (design-v2 section 7.6, b2s Server pin): the probability that the deployment experiment ends with a pin failure whose first failing entry's receiving Server peer designates `g` is at most `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g) + PinCollision.term budget`, each with coefficient one; no anomaly term and no publication term. -/
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
          (pinClaim setup.source.crypto codec setup.serverKeyId budget route) g) +
      PqxdhDeploymentHeadlinePinCollision.term budget := by
  have chain := PqxdhDeploymentHeadlineChain.chain_server setup functional codec checks route ensureInit phase1 phase2
    correct bounds mode adversary budget respects (pinEvent setup.source.crypto codec setup.serverKeyId budget route)
    (pinClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime
  have lift := PqxdhDeploymentHeadlineChain.auth_le setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects g runtime fallback
    (serverSlotted setup codec budget (pinEvent setup.source.crypto codec setup.serverKeyId budget route)
      (pinClaim setup.source.crypto codec setup.serverKeyId budget route) g)
  have ideal := idealAuth_pin_le setup codec checks route caps bounded ensureInit qInit initBound phase2
    bounds mode adversary budget respects g runtime
  calc _ ≤ _ := chain
    _ ≤ ((PqxdhDeploymentHeadlinePinCollision.term budget + authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
          (serverSlotted setup codec budget (pinEvent setup.source.crypto codec setup.serverKeyId budget route)
            (pinClaim setup.source.crypto codec setup.serverKeyId budget route) g)) +
        ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
          (pinEvent setup.source.crypto codec setup.serverKeyId budget route)
          (pinClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime)) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
          (pinEvent setup.source.crypto codec setup.serverKeyId budget route)
          (pinClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime) :=
        add_le_add (add_le_add (lift.trans (add_le_add ideal le_rfl)) le_rfl) le_rfl
    _ = _ := by ring

/-- **R1** (design-v2 section 7.6, b2s Server pin, `ce_pin_b2s`): the probability that the deployment experiment ends with a pin failure (an accepted Server raw receive on a peer designating a target whose counterpart owner was created with a pin different from the Server identity read from the target session's build response) is at most the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g) + PinCollision.term budget`, each with coefficient one. -/
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
              (pinClaim setup.source.crypto codec setup.serverKeyId budget route) (g.1, g.2.castSucc)) +
          PqxdhDeploymentHeadlinePinCollision.term budget) := by
  rw [PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds mode adversary
    budget respects _ _ runtime (pin_named setup.source.crypto codec setup.serverKeyId budget route)]
  exact Finset.sum_le_sum fun g _ => ce_pin_b2s_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound bounds mode adversary budget respects runtime fallback (g.1, g.2.castSucc)


/-- In the target ideal environment, the unchanged combined origin/pin failure is bounded by the publication term plus the proved actual-cache birthday term. Agreement failure itself has probability zero. -/
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
        setup.serverKeyId bounds mode adversary)] {true} ≤ publicationTerm budget + PqxdhDeploymentHeadlinePinCollision.term budget := by
  classical
  have final := PqxdhDeploymentHeadlineOrigin.unpublished_final setup codec checks route caps bounded ensureInit qInit
    initBound frameReadBack bounds mode adversary budget respects g runtime
  have zero := PqxdhDeploymentHeadlineAgree.agreement_statement setup codec route setup.serverKeyId bounds 2
    (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) mode adversary
  have collisionBound := PqxdhDeploymentHeadlinePinCtxCollision.idealAuth_collision setup codec checks route caps bounded
    (Target.ofCE budget g) ensureInit qInit initBound 0 runtime bounds mode budget adversary respects
  rw [Functor.map_map] at final ⊢
  refine (chance_mono_support _ _ (fun result =>
    PqxdhRecordLiftIdeal.unpublishedEvent codec route (ctxView result) ||
      (agreeEvent codec route result || decide (CacheHasCollision result.2.base.primitive.2))) ?_).trans ?_
  · exact fun result member held => by
      simpa only [Bool.or_eq_true, agreeEvent, decide_eq_true_eq] using
        originPin_contain_or_collision setup codec budget route phase2 g result
          (PqxdhDeploymentHeadlinePinInvariant.idealAuth_pinFacts setup codec checks route (Target.ofCE budget g)
            ensureInit 0 runtime bounds mode adversary result member) held
  · refine (chance_or_le _ (fun result => PqxdhRecordLiftIdeal.unpublishedEvent codec route (ctxView result))
      (fun result => agreeEvent codec route result || decide (CacheHasCollision result.2.base.primitive.2))).trans ?_
    refine add_le_add final ((chance_or_le _ (agreeEvent codec route)
      (fun result => decide (CacheHasCollision result.2.base.primitive.2))).trans ?_)
    rw [zero, zero_add]
    simpa only [PqxdhDeploymentHeadlinePinCollision.term, PqxdhDeploymentHeadlinePinCollision.hashCap] using
      collisionBound


/-- **CE-OR b2s with the Server pin field, per target** (design-v2 sections 4.2 and 7.6): the probability that the deployment experiment ends with a b2s origin failure or a pin failure whose claimed receiving Server peer designates `g` is at most `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g) + publicationTerm budget + PinCollision.term budget`, each with coefficient one; no anomaly term. -/
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
      publicationTerm budget + PqxdhDeploymentHeadlinePinCollision.term budget := by
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
    _ ≤ (((publicationTerm budget + PqxdhDeploymentHeadlinePinCollision.term budget) +
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

/-- **CE-OR b2s with the Server pin field** (`ce_or_pin_b2s`, design-v2 sections 4.2 and 7.6): the probability that the deployment experiment ends with a b2s origin failure or a pin failure is at most the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g) + publicationTerm budget + PinCollision.term budget`, each with coefficient one; no anomaly term. -/
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
          publicationTerm budget + PqxdhDeploymentHeadlinePinCollision.term budget) := by
  rw [PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds mode adversary
    budget respects _ _ runtime (originPin_named setup.source.crypto codec setup.serverKeyId budget route)]
  exact Finset.sum_le_sum fun g _ => ce_or_pin_b2s_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback
    (g.1, g.2.castSucc)


end Headline
end Public

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin

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
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.pin_agree_of_noCollision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.pin_agree_of_noCollision

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.decision_transfer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.decision_transfer

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.originPin_contain_of_noCollision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.originPin_contain_of_noCollision

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.pin_agree_or_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.pin_agree_or_collision

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.originPin_contain_or_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.originPin_contain_or_collision

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.idealAuth_pin_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin.idealAuth_pin_le

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
