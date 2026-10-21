-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentSessionFields
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills

/-!
# The ten-field session agreement at the CE-A1 bound (O21, part 3)

`A1NoAgreement c` is CE-A1's event `PqxdhDeploymentServerAuth.A1NoPinnedMatch c` with "no session pin-matches `c`" strengthened to "no session handle both pin-matches `c` and agrees with it on the ten fields read from the experiment's final state" (`PqxdhDeploymentSessionFields.FieldsAgree`). It contains CE-A1's event on every outcome (`noPinnedMatch_noAgreement`) and is contained in it on the support of the experiment at identity index 0 (`noAgreement_noPinnedMatch`, from `PqxdhDeploymentSessionFields.pinned_agree`), so the two coincide there (`noAgreement_iff`). The new event therefore adds no probability content: its content is the support-level fact that whenever the public pinned match holds, the ten fields read from the final state agree.

- `ce_a1_agreement`: the probability of `∃ c, A1NoAgreement c` is at most `∑ c : Fin qCreate, serverAuthBound … (R_c) …`, with the bills of every `R_c`; the premises and the right-hand side are those of `PqxdhDeploymentServerAuth.ce_a1` at index 0, verbatim. `ce_a1_agreement_billed` is the same at the transported caps of `PqxdhDeploymentServerAuthBills.ce_a1_billed`.
- `pinnedLookup`, `lookup_agree`: the handle looked up deterministically (the first handle below the accept count that pin-matches) agrees on the ten fields whenever some handle pin-matches.

Not stated: root agreement (the experiment's outcome has no labelled Beacon root; inside the ServerAuth run of each `R_c`, non-failure includes root agreement, but carrying it over to this experiment's roots needs a state-carrying coupling that is not built, so no root guarantee about this experiment is claimed, not even informally at the bound), and the payload and the assigned key ID (outside the eleven fields). No new assumption or contract.
-/

open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentSessionAgreement
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthSourceCosts
open PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh PqxdhServerAuthAssumptions
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhEd25519EufCma CtxNonceAeadIntCtxt
open PqxdhJointIdentity
open PqxdhDeploymentInterface (FreshBounds ModeSpec Mode Budget)
open PqxdhDeploymentServerAuthEvent (Reg regsOf accepted summarizeReg protectedBinding)
open PqxdhDeploymentServerAuth (PinnedMatchAt PinnedMatch A1NoPinnedMatch serverAuthBound serverAuthAdversary reduction
  ReductionCaps)
open PqxdhDeploymentServerAuthBills (coinCap romCap hashCap totalCap)
open PqxdhDeploymentSessionFields (FieldsAgree)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- CE-A1 with the ten-field session agreement: a Server was constructed; owner `c` has no rejected bundle call in Fresh, accepted, was created with the protected binding `(S, serverKid)` before its acceptance, and no session handle both pin-matches its accepted initial response and agrees with it on the ten fields read from the experiment's final state (`PqxdhDeploymentSessionFields.FieldsAgree`). On the support of the experiment at identity index 0 this is CE-A1's event (`noAgreement_iff`); root agreement is not stated (the experiment retains no labelled Beacon root), nor the payload or the assigned key ID. -/
def A1NoAgreement (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) ×
      A) : Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧
    PqxdhDeploymentTranscript.NoBundleFailureAt final.1.transcript c ∧
    ∃ before raw, accepted c (regsOf final.1.transcript) = some (before, raw) ∧
      (summarizeReg before).owners[c]? = some (protectedBinding setup created) ∧
      ¬ ∃ session, PinnedMatchAt setup.source.crypto codec c session (protectedBinding setup created).1 before raw ∧
        FieldsAgree setup codec final c session

/-- On every outcome, CE-A1's event is contained in the ten-field event: the extra conjunct is dropped. -/
theorem noPinnedMatch_noAgreement (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) ×
      A)
    (event : A1NoPinnedMatch setup codec c outcome) : A1NoAgreement setup codec c outcome := by
  obtain ⟨created, output, final, reached, noFailure, before, raw, acceptedEq, bound, unpinned⟩ := event
  exact ⟨created, output, final, reached, noFailure, before, raw, acceptedEq, bound,
    fun ⟨session, pinned, _⟩ => unpinned ⟨session, pinned⟩⟩

/-- On every outcome of the experiment at identity index 0, the ten-field event is contained in CE-A1's event: a pinned match of an accepted owner pinned to the protected binding agrees with it on the ten fields (`PqxdhDeploymentSessionFields.pinned_agree`). Premises: the approved Phase 1 and Phase 2 read-back contracts. -/
theorem noAgreement_noPinnedMatch (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) ×
      A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime)) (c : Nat)
    (event : A1NoAgreement setup codec c outcome) : A1NoPinnedMatch setup codec c outcome := by
  obtain ⟨created, output, final, reached, noFailure, before, raw, acceptedEq, bound, disagree⟩ := event
  exact ⟨created, output, final, reached, noFailure, before, raw, acceptedEq, bound, fun ⟨session, pinned⟩ =>
    disagree ⟨session, pinned, PqxdhDeploymentSessionFields.pinned_agree setup codec checks route ensureInit phase1
      phase2 bounds mode adversary runtime outcome supported created output final reached c before raw acceptedEq bound
      session pinned⟩⟩

/-- On the support of the experiment at identity index 0, the ten-field event is CE-A1's event. -/
theorem noAgreement_iff (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) ×
      A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime)) (c : Nat) :
    A1NoAgreement setup codec c outcome ↔ A1NoPinnedMatch setup codec c outcome :=
  ⟨noAgreement_noPinnedMatch setup codec checks route ensureInit phase1 phase2 bounds mode adversary runtime outcome
    supported c, noPinnedMatch_noAgreement setup codec c outcome⟩

/-- O21 at the CE-A1 bound (ten of the eleven ServerAuth fields; identity index 0, generated seed): for a budget-respecting adversary, the probability that some Beacon `c`, pinned to the constructed Server's identity and key ID before its acceptance, accepted on a run with `NoBundleFailure_c` with no session handle that both pin-matches its accepted initial response and agrees with it on the ten fields read from the final state (`A1NoAgreement`), is at most the sum over the `qCreate` creation indices of the Server-authentication bound of `R_c`, with the bills of every constructed reduction. This is `PqxdhDeploymentServerAuth.ce_a1` at index 0 with its premises and right-hand side verbatim; the events coincide on the support (`noAgreement_iff`), so the content is the support-level agreement. Root agreement is not stated: the experiment retains no labelled Beacon root, and the root agreement inside the ServerAuth run of each `R_c` is not carried over to this experiment; the payload and the assigned key ID are not among the fields. -/
theorem ce_a1_agreement (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
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
    (𝒟[(fun outcome => @decide (∃ c, A1NoAgreement setup codec c outcome) (Classical.propDecidable _)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime]
        {true}).toReal ≤
      ∑ c : Fin budget.create, serverAuthBound setup codec checks caps
        (serverAuthAdversary setup codec route bounds mode adversary c) qCoin Q qH qHash fallback signatureFallback ∧
    ∀ c, PqxdhServerAuthCommonAuthentication.ReductionBills setup codec checks caps
      (serverAuthAdversary setup codec route bounds mode adversary c) qCoin Q qH qHash qTotal qFinish fallback
      signatureFallback := by
  have headline := PqxdhDeploymentServerAuth.ce_a1 setup codec checks caps bounded route ensureInit 0 phase1 phase2
    frameBack writable law spread correct adapter bounds mode adversary budget respects runtime qCoin Q qH qHash qTotal
    qFinish reductionCaps fallback signatureFallback
  refine ⟨le_trans ?_ headline.1, headline.2⟩
  set run := (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime
  have finite : 𝒟[(fun outcome => @decide (∃ c, A1NoPinnedMatch setup codec c outcome) (Classical.propDecidable _)) <$>
      run] {true} ≠ ⊤ := by
    rw [← prEvent_eq_evalDist_singleton _ true]
    exact prEvent_ne_top _
  refine ENNReal.toReal_mono finite ?_
  classical
  rw [UniformTargetSelection.chance_eq, UniformTargetSelection.chance_eq]
  exact prEvent_mono_of_support _ _ _ fun outcome member ⟨c, event⟩ => ⟨c, noAgreement_noPinnedMatch setup codec checks route
    ensureInit phase1 phase2 bounds mode adversary runtime outcome member c event⟩

/-- O21 at the transported deployment budget: `ce_a1_agreement` with the query caps of every `R_c` discharged from the deployment budget, the right-hand side of `PqxdhDeploymentServerAuthBills.ce_a1_billed` at index 0 verbatim. -/
theorem ce_a1_agreement_billed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[(fun outcome => @decide (∃ c, A1NoAgreement setup codec c outcome) (Classical.propDecidable _)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime]
        {true}).toReal ≤
      ∑ c : Fin budget.create, serverAuthBound setup codec checks caps
        (serverAuthAdversary setup codec route bounds mode adversary c)
        (coinCap caps bounds budget) budget.accept (romCap budget) (hashCap budget) fallback signatureFallback ∧
    ∀ c, PqxdhServerAuthCommonAuthentication.ReductionBills setup codec checks caps
      (serverAuthAdversary setup codec route bounds mode adversary c)
      (coinCap caps bounds budget) budget.accept (romCap budget) (hashCap budget) (totalCap caps bounds budget)
      budget.finish fallback signatureFallback :=
  ce_a1_agreement setup codec checks caps bounded route ensureInit phase1 phase2 frameBack writable law spread correct
    adapter bounds mode adversary budget respects runtime _ _ _ _ _ _
    (fun c => PqxdhDeploymentServerAuthBills.reduction_caps setup codec caps bounded route bounds mode adversary budget
      respects c) fallback signatureFallback

/-- The session handle looked up for owner `c`'s acceptance: the first handle below the number of accept attempts that pin-matches its accepted initial response. -/
noncomputable def pinnedLookup (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (transcript : List PqxdhDeploymentInterface.Entry) (c : Nat) (pin : PqxdhBeaconPhase2Preparation.Word32)
    (before : List Reg) (raw : Pqxdh.Bytes) : Option Nat :=
  (List.range (PqxdhDeploymentTranscript.acceptCount transcript)).find? fun session =>
    @decide (PinnedMatchAt crypto codec c session pin before raw) (Classical.propDecidable _)

/-- On every outcome of the experiment at identity index 0, a pinned match of an accepted owner pinned to the protected binding is found by the lookup, and the looked-up handle agrees with the owner on the ten fields. Premises: the approved Phase 1 and Phase 2 read-back contracts. -/
theorem lookup_agree (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) ×
      A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (reached : outcome.1 = some (created, output, final)) (c : Nat)
    (before : List Reg) (raw : Pqxdh.Bytes) (found : accepted c (regsOf final.1.transcript) = some (before, raw))
    (bound : (summarizeReg before).owners[c]? = some (protectedBinding setup created))
    (matched : PinnedMatch setup.source.crypto codec c (protectedBinding setup created).1 before raw) :
    ∃ session, pinnedLookup setup.source.crypto codec final.1.transcript c (protectedBinding setup created).1 before
      raw = some session ∧ FieldsAgree setup codec final c session := by
  obtain ⟨matchedSession, pinned⟩ := matched
  have below : matchedSession < PqxdhDeploymentTranscript.acceptCount final.1.transcript := by
    obtain ⟨acceptRaw, _, _, _, _, _, acceptMember, _⟩ := pinned
    have prefixed := PqxdhDeploymentServerAuthEvent.accepted_prefix c _ before raw found
    exact (PqxdhDeploymentHeadlineGap.accept_positional setup codec checks route ensureInit phase1 phase2 bounds mode
      adversary runtime outcome supported created output final reached acceptRaw matchedSession
      (PqxdhDeploymentHeadlineGap.accept_entry final.1.transcript acceptRaw (some matchedSession)
        (prefixed.subset acceptMember))).1
  have isSome : (pinnedLookup setup.source.crypto codec final.1.transcript c (protectedBinding setup created).1 before
      raw).isSome := by
    unfold pinnedLookup
    rw [List.find?_isSome]
    exact ⟨matchedSession, List.mem_range.mpr below, @decide_eq_true _ (Classical.propDecidable _) pinned⟩
  obtain ⟨session, lookedUp⟩ := Option.isSome_iff_exists.mp isSome
  have pinnedSession : PinnedMatchAt setup.source.crypto codec c session (protectedBinding setup created).1 before
      raw := by
    unfold pinnedLookup at lookedUp
    have hit := List.find?_some lookedUp
    exact @of_decide_eq_true _ (Classical.propDecidable _) hit
  exact ⟨session, lookedUp, PqxdhDeploymentSessionFields.pinned_agree setup codec checks route ensureInit phase1 phase2
    bounds mode adversary runtime outcome supported created output final reached c before raw found bound session
    pinnedSession⟩

end BeaconcryptCore.Computational.PqxdhDeploymentSessionAgreement

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionAgreement.noPinnedMatch_noAgreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionAgreement.noPinnedMatch_noAgreement

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionAgreement.noAgreement_noPinnedMatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionAgreement.noAgreement_noPinnedMatch

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionAgreement.noAgreement_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionAgreement.noAgreement_iff

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionAgreement.ce_a1_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionAgreement.ce_a1_agreement

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionAgreement.ce_a1_agreement_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionAgreement.ce_a1_agreement_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionAgreement.lookup_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionAgreement.lookup_agree
