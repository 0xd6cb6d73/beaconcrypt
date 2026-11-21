-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurity
import BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots
import BeaconcryptCore.Computational.PqxdhDeploymentSessionResume

/-! Publicly selected acceptance prefixes for causal publication. A prefix is selected by its accept-attempt ordinal, including rejected accepts. No reduction detects a privately bad acceptance. Every stopped adversary retains the original deployment caps, and the unrestricted publication theorem applies separately to every prefix, displaying the extra acceptance-position sum. The bounded event concerns actual saved successful-acceptance prefixes in the legacy/source14 experiment. Complete historical-acceptance coverage, journal/ledger linkage and transfer into RegistrationNativeExperiment remain separate obligations. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication
open PqxdhServerAuthExperiment
open PqxdhDeploymentInterface
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

/-- Count every accept attempt in the public journal. Rejections retain their original positions. -/
def attempts (journal : PqxdhDeploymentSessionSnapshot.Journal FullSpec) : Nat :=
  journal.countP fun entry => queryClass entry.1 = 3

/-- Stop immediately after the selected public accept attempt, irrespective of its private origin status. -/
def stopAt (ordinal : Nat)
    (journal : PqxdhDeploymentSessionSnapshot.Journal FullSpec) : Prop := ordinal < attempts journal

instance (ordinal : Nat) : DecidablePred (stopAt ordinal) :=
  fun journal => Nat.decLt ordinal (attempts journal)

theorem stopAt_empty (ordinal : Nat) : ¬ stopAt ordinal [] := by
  simp [stopAt, attempts]

/-- Default replies are supplied only to the adversary's unexecuted suffix; they make no primitive queries. -/
def dflt : (query : FullSpec.Domain) → FullSpec.Range query
  | .inl (.inl coin) => (0 : Fin (coin + 1))
  | .inl (.inr (.create _ _)) => none
  | .inl (.inr (.bundle _)) => none
  | .inl (.inr (.accept _)) => none
  | .inl (.inr (.build _ _)) => none
  | .inl (.inr (.finish _ _)) => none
  | .inl (.inr (.hmac _ _)) => PqxdhSecretInputKdf.zeroSalt
  | .inl (.inr (.hash _)) => List.Vector.replicate 64 0
  | .inl (.inr (.serverSend _ _)) => none
  | .inl (.inr (.serverRaw _)) => .None
  | .inl (.inr (.beaconSend _ _)) => none
  | .inl (.inr (.beaconRaw _ _)) => .None
  | .inr (.test _ _ _) => none
  | .inr (.fresh _ _) => none

/-- The public selected-prefix adversary. It never tests a private forgery predicate. -/
def stopped (ordinal : Nat) (adversary : OracleComp FullSpec X) :=
  PqxdhDeploymentServerAuthEmbed.freeze dflt (stopAt ordinal) adversary

/-- A stopped program preserves every query-class cap. -/
theorem freeze_query_bound {κ : Type} {spec : OracleSpec κ} {Result : Type}
    (defaults : (query : spec.Domain) → spec.Range query)
    (stop : PqxdhDeploymentSessionSnapshot.Journal spec → Prop) [DecidablePred stop]
    (program : OracleComp spec Result) (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (n : Nat) (bounded : program.IsQueryBoundP predicate n)
    (start : PqxdhDeploymentSessionSnapshot.Journal spec) :
    ((simulateQ (PqxdhDeploymentServerAuthEmbed.freezeImpl defaults stop) program).run start).IsQueryBoundP
      predicate n := by
  induction program using OracleComp.inductionOn generalizing start n with
  | pure value => simp
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, PqxdhDeploymentServerAuthLocalize.freezeImpl_run]
      split_ifs with reached
      · obtain ⟨value, same⟩ := PqxdhDeploymentServerAuthFreeze.frozen_pure defaults stop
          (next (defaults query)) start reached
        simp only [pure_bind, same, isQueryBoundP_pure]
      · simp only [bind_map_left]
        rw [isQueryBoundP_query_bind_iff]
        exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply) _⟩

theorem stopped_respects (ordinal : Nat) (adversary : OracleComp FullSpec X) (budget : Budget)
    (respects : budget.Respects (mode := .O) adversary) : budget.Respects (mode := .O) (stopped ordinal adversary) :=
  fun kind => freeze_query_bound dflt (stopAt ordinal) adversary _ _ (respects kind) []

abbrev Snapshots (count : Nat) (KemSK : Type) :=
  PqxdhDeploymentSessionSnapshots.State (Fin count) FullSpec (PqxdhDeploymentSecrecy.State KemSK)

abbrev Outcome (count : Nat) (KemSK A X : Type) :=
  Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × Snapshots count KemSK) × A

/-- Capture every bounded public accept-attempt prefix in one complete adaptive execution. Constructor failures and all post-acceptance callbacks remain present. -/
noncomputable def instrumented (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (count : Nat) (adversary : OracleComp FullSpec X) : StateT A ProbComp (Option
      (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × Snapshots count KemSK)) := fun runtime => do
  let born ← (PqxdhLiveServerConstruction.construct setup.joint ensureInit 0 setup.serverKeyId none).run runtime
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some (PqxdhRegistrationJointServerBirth.encode created, result), born.2)) <$>
      PqxdhDeploymentSessionSnapshots.run (PqxdhDeploymentSecrecy.handler setup codec checks route created.seed bounds)
        (fun ordinal : Fin count => stopAt ordinal.val) adversary
        (PqxdhDeploymentSecrecy.Ledger.empty, PqxdhDeploymentNative.initial created)

def erase {count : Nat} (outcome : Outcome count KemSK A X) :
    PqxdhDeploymentPublicationSecurityEvents.Outcome KemSK A X :=
  (outcome.1.map fun result => (result.1, result.2.1, result.2.2.native), outcome.2)

/-- Erasing all selected-prefix receipts preserves the constructor, output, ledger, primitive caches, live kernels, counters, owners, pending tokens and runtime together. -/
theorem instrumented_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (count : Nat) (adversary : OracleComp FullSpec X) (runtime : A) :
    erase <$> (instrumented setup codec checks route ensureInit bounds count adversary).run runtime =
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .O adversary).run runtime := by
  simp only [instrumented, PqxdhDeploymentSecrecy.game, StateT.run, map_bind]
  apply bind_congr
  rintro ⟨_ | created, after⟩
  · rfl
  · simpa only [Functor.map_map, erase, Option.map_some, asModeO, StateT.run] using
      congrArg (fun work => (fun result =>
        (some (PqxdhRegistrationJointServerBirth.encode created, result), after)) <$> work)
        (PqxdhDeploymentSessionSnapshots.erase
          (PqxdhDeploymentSecrecy.handler setup codec checks route created.seed bounds)
          (fun ordinal : Fin count => stopAt ordinal.val) adversary
          (PqxdhDeploymentSecrecy.Ledger.empty, PqxdhDeploymentNative.initial created))

/-- Failure at a saved acceptance prefix is evaluated against that prefix's actual owner identities and publications. Later publication cannot change the saved state. -/
def SelectedEvent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {count : Nat}
    (ordinal : Fin count) (outcome : Outcome count KemSK A X) : Prop :=
  ∃ created output final snapshot, outcome.1 = some (created, output, final) ∧
    final.captured ordinal = some snapshot ∧
    PqxdhDeploymentPublishedTuple.PublishedForgery setup.source.crypto codec snapshot.2.1.transcript
      (PqxdhDeploymentPublishedTuple.ownerIdentities setup snapshot.2.2.native)

/-- Causal publication failure anywhere in this single run, retaining failed bundle writes and the actual prefix owner map. -/
def Event (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {count : Nat}
    (outcome : Outcome count KemSK A X) : Prop := ∃ ordinal, SelectedEvent setup codec ordinal outcome

/-- A successful acceptance whose decoded tuple was not published by that owner before this acceptance. Owner identities are read from this prefix's state, not from the final deployment. -/
def AcceptanceFailure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (state : PqxdhDeploymentSecrecy.State KemSK) : Prop :=
  ∃ before raw session candidate identity decoded owner,
    state.1.transcript = before ++ [⟨.inl (.inr (.accept raw)), some session⟩] ∧
    PqxdhDeploymentTranscript.candidateOf codec raw = some candidate ∧
    PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto candidate = some (identity, decoded) ∧
    (PqxdhDeploymentPublishedTuple.ownerIdentities setup state.2.native)[owner]? = some identity ∧
    PqxdhDeploymentPublishedTuple.publishedTuple codec before owner ≠ some decoded

/-- Accepting does not itself publish a bundle; the prefix event therefore tests only earlier publications. -/
theorem publication_before_accept (codec : Codec Reader Response) (before : List Entry)
    (raw : Pqxdh.Bytes) (session owner : Nat) :
    PqxdhDeploymentPublishedTuple.publishedTuple codec
      (before ++ [⟨.inl (.inr (.accept raw)), some session⟩]) owner =
      PqxdhDeploymentPublishedTuple.publishedTuple codec before owner := by
  simp [PqxdhDeploymentPublishedTuple.publishedTuple, PqxdhDeploymentTranscript.bundleOf,
    List.findSome?_append]

theorem acceptance_failure_published (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (state : PqxdhDeploymentSecrecy.State KemSK) (failed : AcceptanceFailure setup codec state) :
    PqxdhDeploymentPublishedTuple.PublishedForgery setup.source.crypto codec state.1.transcript
      (PqxdhDeploymentPublishedTuple.ownerIdentities setup state.2.native) := by
  obtain ⟨before, raw, session, candidate, identity, decoded, owner, transcript, parsed, accepted, found, other⟩ := failed
  exact ⟨raw, session, by simp [transcript], candidate, identity, decoded, owner, parsed, accepted, found,
    by simpa only [transcript, publication_before_accept] using other⟩

/-- Successful-acceptance origin failure at a saved public ordinal, with every later callback still executed. -/
def CausalSelectedEvent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {count : Nat}
    (ordinal : Fin count) (outcome : Outcome count KemSK A X) : Prop :=
  ∃ created output final snapshot, outcome.1 = some (created, output, final) ∧
    final.captured ordinal = some snapshot ∧ AcceptanceFailure setup codec snapshot.2

def CausalEvent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {count : Nat}
    (outcome : Outcome count KemSK A X) : Prop := ∃ ordinal, CausalSelectedEvent setup codec ordinal outcome

theorem causal_selected (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {count : Nat}
    (ordinal : Fin count) (outcome : Outcome count KemSK A X)
    (failed : CausalSelectedEvent setup codec ordinal outcome) : SelectedEvent setup codec ordinal outcome := by
  obtain ⟨created, output, final, snapshot, reached, saved, failure⟩ := failed
  exact ⟨created, output, final, snapshot, reached, saved, acceptance_failure_published setup codec snapshot.2 failure⟩

/-- A captured prefix of the full run is coupled to the publicly stopped game, retaining the actual prefix native state. -/
theorem selected_le_stopped (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (count : Nat) (adversary : OracleComp FullSpec X) (ordinal : Fin count) (runtime : A) :
    Pr{let outcome ← (instrumented setup codec checks route ensureInit bounds count adversary).run runtime}[
      SelectedEvent setup codec ordinal outcome] ≤
      Pr{let outcome ← (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .O
        (stopped ordinal.val adversary)).run runtime}[
          PqxdhDeploymentPublicationSecurityEvents.GameEvent setup codec outcome] := by
  simp only [instrumented, PqxdhDeploymentSecrecy.game, StateT.run]
  apply prEvent_bind_mono_of_forall_le_of_support
  rintro ⟨_ | created, after⟩ _
  · simp [SelectedEvent, PqxdhDeploymentPublicationSecurityEvents.GameEvent,
      PqxdhDeploymentPublishedTuple.GameHolds]
  · simpa [prEvent_map, SelectedEvent, PqxdhDeploymentPublicationSecurityEvents.GameEvent,
      Prod.eq_iff_fst_eq_snd_eq,
      PqxdhDeploymentPublishedTuple.GameHolds, stopped, StateT.run, asModeO] using
      PqxdhDeploymentSessionSnapshots.captured_le_frozen
        (PqxdhDeploymentSecrecy.handler setup codec checks route created.seed bounds) dflt
        (fun ordinal : Fin count => stopAt ordinal.val) ordinal adversary
        (PqxdhDeploymentSecrecy.Ledger.empty, PqxdhDeploymentNative.initial created)
        (stopAt_empty ordinal.val)
        (fun state => PqxdhDeploymentPublishedTuple.PublishedForgery setup.source.crypto codec state.1.transcript
          (PqxdhDeploymentPublishedTuple.ownerIdentities setup state.2.native))

/-- The unrestricted publication bound applies to every explicitly selected public prefix, with the unchanged deployment budgets and all failed bundle writes. -/
theorem stopped_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (adversary : OracleComp FullSpec X) (budget : Budget)
    (respects : budget.Respects (mode := .O) adversary) (ordinal : Nat) (runtime : A)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    Pr{let outcome ← ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .O
      (stopped ordinal adversary)).run runtime)}[
        PqxdhDeploymentPublicationSecurityEvents.GameEvent setup codec outcome] ≤
      PqxdhDeploymentPublicationSecurity.totalAdvantage setup codec checks route ensureInit bounds .O
        (stopped ordinal adversary) budget runtime fallback ordinaryFallback :=
  PqxdhDeploymentPublicationSecurity.published_bound setup codec checks shortRejects phase1 phase2 route ensureInit
    bounds .O (stopped ordinal adversary) budget (stopped_respects ordinal adversary budget respects)
    runtime fallback ordinaryFallback

/-- Saved-prefix provenance failure in one complete run. The extra loss is an explicit sum over at most `qAccept` publicly selected positions, each with its original ordinary and failed-bundle reduction families. -/
theorem prefix_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (adversary : OracleComp FullSpec X) (budget : Budget)
    (respects : budget.Respects (mode := .O) adversary) (runtime : A)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    Pr{let outcome ← (instrumented setup codec checks route ensureInit bounds budget.accept adversary).run runtime}[
      Event setup codec outcome] ≤
      ∑ ordinal : Fin budget.accept,
        PqxdhDeploymentPublicationSecurity.totalAdvantage setup codec checks route ensureInit bounds .O
          (stopped ordinal.val adversary) budget runtime fallback ordinaryFallback := by
  apply (prEvent_exists_le _ (SelectedEvent setup codec)).trans
  exact Finset.sum_le_sum fun ordinal _ =>
    (selected_le_stopped setup codec checks route ensureInit bounds budget.accept adversary ordinal runtime).trans
      (stopped_bound setup codec checks shortRejects phase1 phase2 route ensureInit bounds adversary budget respects
        ordinal.val runtime fallback ordinaryFallback)

/-- Captured successful-acceptance origin failure has the same explicit public-position sum. Later publication cannot repair any saved causal violation. -/
theorem causal_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (adversary : OracleComp FullSpec X) (budget : Budget)
    (respects : budget.Respects (mode := .O) adversary) (runtime : A)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    Pr{let outcome ← (instrumented setup codec checks route ensureInit bounds budget.accept adversary).run runtime}[
      CausalEvent setup codec outcome] ≤
      ∑ ordinal : Fin budget.accept,
        PqxdhDeploymentPublicationSecurity.totalAdvantage setup codec checks route ensureInit bounds .O
          (stopped ordinal.val adversary) budget runtime fallback ordinaryFallback :=
  (prEvent_mono _ _ _ fun outcome ⟨ordinal, failed⟩ =>
    ⟨ordinal, causal_selected setup codec ordinal outcome failed⟩).trans
      (prefix_bound setup codec checks shortRejects phase1 phase2 route ensureInit bounds adversary budget respects
        runtime fallback ordinaryFallback)

/-- Prefix selection adds no callback or coin allowance to the existing per-reduction resource bills. -/
theorem prefix_family_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (kemBound : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (bounds : FreshBounds) (adversary : OracleComp FullSpec X) (budget : Budget)
    (respects : budget.Respects (mode := .O) adversary) (ordinal : Nat) (runtime : A)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    PqxdhDeploymentPublicationSecurity.FamilyBills setup codec checks route ensureInit qInit caps bounds .O
      (stopped ordinal adversary) budget runtime fallback ordinaryFallback :=
  PqxdhDeploymentPublicationSecurity.family_bills setup codec checks route ensureInit qInit initBound caps kemBound
    bounds .O (stopped ordinal adversary) budget (stopped_respects ordinal adversary budget respects) runtime
    fallback ordinaryFallback

end BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.stopAt_empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.stopAt_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.freeze_query_bound' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.freeze_query_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.stopped_respects' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.stopped_respects

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.instrumented_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.instrumented_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.selected_le_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.selected_le_stopped

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.stopped_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.stopped_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.causal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.causal_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.prefix_family_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.prefix_family_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.publication_before_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.publication_before_accept

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.acceptance_failure_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.acceptance_failure_published

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.causal_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.causal_selected

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.prefix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication.prefix_bound
