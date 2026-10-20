import BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality
import BeaconcryptCore.Computational.RawCtxSelectedKeyProbes

/-!
Bound of the key-disclosure game of first-record confidentiality (step S7). `PqxdhFirstRecordConfidentiality.first_record_confidentiality` leaves, for each challenge bit, the explicit game `keyGame`: in the key-last run with a uniform record key drawn after the preparation, the first-record event and the absence of hidden disclosure hold while the record key equals a value that the adversary revealed. `key_bound` bounds it by the CTX key-recovery loss `recoveryLoss` of a constructed key-free client, the initial half-alias term `2^-256` and the nonce-repeat stop bound of `PqxdhFirstRecordStopTagged.stop_bound`. `first_record_confidentiality_key` and `first_record_confidentiality_key_budget` restate the confidentiality theorem with this bound, so that the two `collGame` terms are its only remaining explicit game terms.

The proof first moves from the source run to the instrumented compiled run (`keyRun_le`), paying the restricted stop game once more. In the compiled run the record key is used only by selected CTX operations, and a reveal of a hidden slot stops the compiled run with no reply and is recorded in the history only as a nonce-only marker, which `known` excludes, so every revealed value is computed without the key; the hit is membership of the key in the list of revealed 32-byte values (`RawCtxSelectedMessageFreshness.keys_hit`). The event is weakened to this hit alone. The candidate list is truncated to `qCand` entries (`candidates`). The truncation loses nothing on the actual runs: the prepared history has at most the initial observations plus the prechallenge allowance (`PqxdhInitialPreparedSourceCaps.prepared_history`), the first Server builder keeps the history (`build_history`), and each compiled post request adds at most one observation (`ins_history_step`, `ins_history_run`), so the whole list has at most `candidateCount` entries (`insKey_le_hit`, `key_le_hit`).

Outside the initial half alias (`hit_le_separated`), the key-hit game is the key-retaining source game of the key-free candidate client `keyClient`, which runs the forwarded preparation prelude and the instrumented first-record suffix and returns the revealed values as CTX keys. This uses the C5 client step generalized to events that mention the fixed key (`postBit_client`, `hitObserve_eq`) and the key-first reordering `RawCtxPrefixKeyOrder.complete` (`hitSource_reorder`, `separated_le_source`). The dynamic known-key reduction turns this game into the retained canonical CTX game of an ordinary one-key client `recvClient` (`AdaptiveCtxDynamicKnownKeys.schedule_interpretation`, `AdaptiveCtxSharedModes.real_schedule`, `canonical_hit`, `source_candidate`), whose candidate hit `RawCtxSelectedKeyProbes.candidate_bound` bounds by `keyLoss`: twice the sum of the IND$ advantage of the constructed validation reduction of the probed client, the hash-guessing term `(qHash + qCand)/2^128` and the INT-CTXT advantages of the constructed attempt-indexed reductions. The client's hash, seal and raw budgets are those of the confidentiality client, `qPrelude + 1 + qPost`, `1 + qPost` and `1 + qPost` (`keyClient_uses`).

The candidate count is derived from the certificate: the target's prior disclosures (none for the first Beacon record), the initial reveal observations of the environment, the prechallenge allowance `preCap` and the post budget (`candidateCount`, `candidateCount_first`). No new premise, cryptographic assumption or primitive law is introduced: the certificate, the preparation hash budget `PrepareHashBudget` and the seal-count side condition are those of `first_record_confidentiality`. Messages are abstract byte strings that each side can decode; no serialization-library behaviour is used.
-/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound
open PqxdhFirstRecordConfidentiality
section KeyFirst
open PqxdhNativeSharedPrefix PqxdhSelectedStateInterpreter PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open RawCtxSelectedParentTable PqxdhSelectedFirstRecord PqxdhFirstBeaconRecordIntegrity PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily PqxdhInitialBeaconAmbient
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
    (before : PqxdhInitialOriginPostPath.Front M P I D K S B) (selected : RawCtxProtocolReveals.Owner S B)
    (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)
    (store : RawCtxSelectiveChainGame.Store) (key : RootOutput) (nonce : NonceOutput) (next : RootOutput) (b : Fin B)

local notation "target" => PqxdhInitialSourceExperiment.root source previousRoot response64 selected

/-- The instrumented key-disclosure run: the selected builder, then the instrumented evaluated post; the event is `InsEvent` with the selected message key among the disclosed values. -/
noncomputable def insKeyRun (number : Std.U64) (ancestors disclosed : List RatchetChain) : ProbComp Bool := do
  let built ← firstBuild pre application initial selector aux source writer previousRoot response64 sender index metadata ready
    before selected shared privateState cache store key nonce next
  (fun result => @decide (InsEvent source previousRoot response64 selected number ancestors disclosed result ∧
      RawCtxFreshChainCut.concreteChain key ∈ RawCtxSelectedMessageFreshness.known disclosed (insProject result.2).1.1.roles.2)
      (Classical.propDecidable _)) <$>
    (simulateQ (insEvaluated pre application initial selector aux source writer (productionStream source.crypto) none key target nonce next
      sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b)
      (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run (insStart index built)

set_option linter.deprecated false in
/-- The key-disclosure run is dominated by the instrumented key-disclosure run plus the restricted stop run. -/
theorem keyRun_le (number : Std.U64) (ancestors disclosed : List RatchetChain) :
    𝒟[keyRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode index
      metadata ready post before selected shared privateState cache store key nonce next number ancestors disclosed] {true} ≤
    𝒟[insKeyRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode index
      metadata ready post before selected shared privateState cache store key nonce next b number ancestors disclosed] {true} +
    𝒟[stopRun pre application initial selector aux source writer previousRoot response64 sender route decode index metadata ready
      post before selected shared privateState cache store key nonce next ancestors disclosed] {true} := by
  unfold keyRun insKeyRun
  rw [firstRun_bind]
  refine PqxdhFirstBeaconRecordIntegrity.true_bind_le _ _ _ _ fun built => ?_
  have same := post_source_augmented pre application initial selector aux source writer (productionStream source.crypto) none key target
    nonce next sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b (post built.1.1) (insStart index built)
    (fun result => FirstEvent source previousRoot response64 selected number ancestors disclosed result ∧
      RawCtxFreshChainCut.concreteChain key ∈ RawCtxSelectedMessageFreshness.known disclosed result.2.1.1.roles.2)
  have left : 𝒟[(fun result => @decide (FirstEvent source previousRoot response64 selected number ancestors disclosed result ∧
      PqxdhSelectedPostDisclosure.Good result.2.1 ∧
      RawCtxFreshChainCut.concreteChain key ∈ RawCtxSelectedMessageFreshness.known disclosed result.2.1.1.roles.2)
      (Classical.propDecidable _)) <$>
      (simulateQ (traced pre application initial selector aux source writer (productionStream source.crypto) none key target nonce next
        sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage))
        (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run
        ((built.1.2, built.2), selectedAfter PqxdhInitialSourcePublication.empty built.1.2 index true built.1.1)] {true} =
      Pr[fun result => (FirstEvent source previousRoot response64 selected number ancestors disclosed result ∧
        RawCtxFreshChainCut.concreteChain key ∈ RawCtxSelectedMessageFreshness.known disclosed result.2.1.1.roles.2) ∧
        PqxdhSelectedPostDisclosure.Good result.2.1 |
        (simulateQ (traced pre application initial selector aux source writer (productionStream source.crypto) none key target nonce next
          sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage))
          (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run (insProject (insStart index built))] := by
    rw [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map]
    refine probEvent_ext fun result _ => ?_
    simp only [Function.comp_apply, decide_eq_true_eq]
    tauto
  rw [left, same]
  have right : Pr[fun result => (FirstEvent source previousRoot response64 selected number ancestors disclosed
        (result.1, insProject result.2) ∧
      RawCtxFreshChainCut.concreteChain key ∈ RawCtxSelectedMessageFreshness.known disclosed (insProject result.2).1.1.roles.2) ∧
      PqxdhSelectedPostDisclosure.Good (insProject result.2).1 |
      (simulateQ (insAugmented pre application initial selector aux source writer (productionStream source.crypto) none key target nonce next
        sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b)
        (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run (insStart index built)] =
      𝒟[(fun result => @decide (InsEvent source previousRoot response64 selected number ancestors disclosed result ∧
        RawCtxFreshChainCut.concreteChain key ∈ RawCtxSelectedMessageFreshness.known disclosed (insProject result.2).1.1.roles.2)
        (Classical.propDecidable _)) <$>
      (simulateQ (insAugmented pre application initial selector aux source writer (productionStream source.crypto) none key target nonce next
        sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b)
        (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run (insStart index built)] {true} := by
    rw [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map]
    refine probEvent_ext fun result _ => ?_
    simp only [Function.comp_apply, decide_eq_true_eq]
    unfold InsEvent
    tauto
  rw [right]
  let event : Option Bool × InsFull M P I D K A N RootOracle.QueryCache S B → Bool := fun result =>
    @decide (InsEvent source previousRoot response64 selected number ancestors disclosed result ∧
      RawCtxFreshChainCut.concreteChain key ∈ RawCtxSelectedMessageFreshness.known disclosed (insProject result.2).1.1.roles.2)
      (Classical.propDecidable _)
  refine (augmented_le_evaluated pre application initial selector aux source writer (productionStream source.crypto) none key target nonce
    next sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b (post built.1.1) (insStart index built)
    event).trans ?_
  refine add_le_add le_rfl ?_
  exact flagged_le_stop pre application initial selector aux source writer (productionStream source.crypto) none key target nonce
    next sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b (post built.1.1) (insStart index built) event
    (fun state => decide (Undisclosed target ancestors disclosed state)) (fun result holds => by
      simp only [event, decide_eq_true_eq] at holds
      simp only [decide_eq_true_eq]
      exact holds.1.1.2.2)

end KeyFirst

section History
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry PqxdhSelectedFirstRecord
variable {ι I D K X Response Shared A N C M P : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The number of reveal observations in the history of a compiled front. -/
def obsCount (front : PqxdhSelectedPostCompiler.Front M P I D K S B) : Nat := front.roles.2.observations.length

/-- A compiled record or reveal request adds at most one observation to the history: records only advance the position, reveals note one observation. -/
theorem live_history (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (request : (RawCtxProtocolReveals.SourceSpec S B).Domain) (before : RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B)
    (result : Option ((RawCtxProtocolReveals.SourceSpec S B).Range request) × RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B)
    (supported : result ∈ support (((RawCtxSelectedFamilyLiveCompiler.impl source writer prior parent target nonce next sender route read
      request).run).run before)) :
    result.2.2.observations.length ≤ before.2.observations.length + 1 := by
  rcases request with request | request
  · simp only [RawCtxSelectedFamilyLiveCompiler.impl, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    rcases reply with _ | ⟨value, roles⟩ <;>
      simp [RawCtxSelectedFamilyLiveCompiler.publish, RawCtxSelectedMessageFamily.tick]
  · simp only [RawCtxSelectedFamilyLiveCompiler.impl, OptionT.run_mk, StateT.run, support_pure, Set.mem_singleton_iff] at supported
    subst result
    simp [RawCtxSelectedMessageReveals.step, RawCtxSelectedMessageFreshness.note]

variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) (b : Fin B)

/-- Every instrumented compiled post request adds at most one observation to the history. -/
theorem ins_history_step (query : (PqxdhInitialGenericPost.Spec extra S B).Domain) (before : InsState M P I D K A N C S B)
    (result : Option ((PqxdhInitialGenericPost.Spec extra S B).Range query) × InsState M P I D K A N C S B)
    (supported : result ∈ support (((insImpl pre application initial selector aux source writer prior parent target nonce next sender
      route read mark b query).run).run before)) :
    obsCount result.2.1.1 ≤ obsCount before.1.1 + 1 := by
  rcases query with (request | request) | request
  · simp only [insImpl, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨inner, innerSupported, rfl⟩ := supported
    exact live_history source writer prior parent target nonce next sender route read request before.1.1.roles inner innerSupported
  · simp only [insImpl, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨inner, _, rfl⟩ := supported
    exact Nat.le_add_right _ 1
  · cases request with
    | finish index raw =>
      simp only [insImpl, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨inner, _, rfl⟩ := supported
      simp [obsCount, PqxdhSelectedPostCompiler.install, RawCtxSelectedMessageFamily.tick]

/-- The instrumented compiled post run of a client with at most `qPost` requests adds at most `qPost` observations to the history. -/
theorem ins_history_run {Result : Type} (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result) (qPost : Nat)
    (bounded : work.IsTotalQueryBound qPost) (before : InsState M P I D K A N C S B)
    (result : Option Result × InsState M P I D K A N C S B)
    (supported : result ∈ support (((simulateQ (insImpl pre application initial selector aux source writer prior parent target nonce next
      sender route read mark b) work).run).run before)) :
    obsCount result.2.1.1 ≤ obsCount before.1.1 + qPost := by
  induction work using OracleComp.inductionOn generalizing qPost before result with
  | pure value =>
    simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query continuation ih =>
    rw [isTotalQueryBound_query_bind_iff] at bounded
    obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt bounded.1)
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind, mem_support_bind_iff]
      at supported
    obtain ⟨step, stepSupported, tail⟩ := supported
    have grow := ins_history_step pre application initial selector aux source writer prior parent target nonce next sender route read
      mark b query before step stepSupported
    rcases step with ⟨none | answer, after⟩
    · dsimp only at grow
      simp only [Option.elim, StateT.run_pure, support_pure, Set.mem_singleton_iff] at tail
      subst result
      dsimp only
      omega
    · dsimp only at grow
      simp only [Option.elim] at tail
      have rest := ih answer remaining (by simpa using bounded.2 answer) after result tail
      omega

/-- Every result of the instrumented evaluated post comes from a result of the key-free instrumented compiled post from the same instrumented state. -/
theorem evaluated_support {Result : Type} (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (start : InsFull M P I D K A N C S B) (result : Option Result × InsFull M P I D K A N C S B)
    (supported : result ∈ support ((simulateQ (insEvaluated pre application initial selector aux source writer prior parent key target
      nonce next sender route read mark b) (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run start)) :
    (result.1, result.2.1) ∈ support (((simulateQ (insImpl pre application initial selector aux source writer prior parent target nonce
      next sender route read mark b) work).run).run start.1) := by
  rw [← insEvaluated_program] at supported
  simp only [PqxdhSelectedStateInterpreter.evaluate, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨inner, innerSupported, rfl⟩ := supported
  refine support_simulateQ_run'_subset (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read)
    source.crypto key) _ start.2 ?_
  rw [StateT.run'_eq, support_map]
  exact ⟨inner, innerSupported, rfl⟩

end History

section Build
open PqxdhNativeSharedPrefix PqxdhSelectedStateInterpreter PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open RawCtxSelectedParentTable PqxdhSelectedFirstRecord PqxdhFirstBeaconRecordIntegrity PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhInitialBeaconAmbient
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The selected all-known front keeps the observation count of the prepared front. -/
theorem initialFront_count (before : PqxdhInitialOriginPostPath.Front M P I D K S B) :
    obsCount (initialFront before) = before.roles.2.observations.length := by
  simp [obsCount, initialFront, RawCtxSelectedMessageRevealInitialization.fromState,
    RawCtxSelectedMessageRevealInitialization.fromHistory, RawCtxGenericFamilyLive.nativeState]

/-- Reinstalling a builder result keeps the history of the front. -/
theorem reinstall_history (index : Fin S) (before : PqxdhSelectedPostCompiler.Front M P I D K S B)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhInitialGenericPublication.State RawCtxSelectedMessageReveals.Kernel M P (List Pqxdh.Bytes))) :
    (reinstallServer index before result).2.roles.2 = before.roles.2 := by
  cases result <;> rfl

variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (before : PqxdhInitialOriginPostPath.Front M P I D K S B) (selected : RawCtxProtocolReveals.Owner S B)
    (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)
    (store : RawCtxSelectiveChainGame.Store) (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)

/-- The selected first Server builder keeps the observation count of the prepared front. -/
theorem build_history (built : Built M P I D K A N S B)
    (supported : built ∈ support (firstBuild pre application initial selector aux source writer previousRoot response64 sender index
      metadata ready before selected shared privateState cache store key nonce next)) :
    obsCount built.1.2 = before.roles.2.observations.length := by
  simp only [firstBuild, selectedBuild, StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  rw [← initialFront_count]
  unfold obsCount
  rw [reinstall_history]
  rfl

end Build

section Support

/-- Pointwise domination of Boolean continuations on the support of the first computation is preserved by bind. -/
theorem true_bind_mono_support {α : Type} (mx : ProbComp α) (f g : α → ProbComp Bool)
    (le : ∀ a ∈ support mx, 𝒟[f a] {true} ≤ 𝒟[g a] {true}) : 𝒟[mx >>= f] {true} ≤ 𝒟[mx >>= g] {true} := by
  simp only [evalDist_apply_singleton] at le ⊢
  simp only [probOutput_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases member : a ∈ support mx
  · gcongr
    exact le a member
  · simp [probOutput_eq_zero_of_not_mem_support member]

/-- A Boolean projection implied by another one on the support has at most its `true` mass. -/
theorem map_mono_support {α : Type} (mx : ProbComp α) (f g : α → Bool)
    (weaker : ∀ a ∈ support mx, f a = true → g a = true) : 𝒟[f <$> mx] {true} ≤ 𝒟[g <$> mx] {true} := by
  simp only [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map]
  exact _root_.probEvent_mono fun a member holds => weaker a member holds

end Support

section Candidates
variable {M P I D K : Type} {S B : Nat}

/-- The CTX candidate keys of a compiled front: the 32-byte values of the prior disclosed chains and of every known value revealed so far, in disclosure order, truncated to `qCand` entries. -/
def candidates (qCand : Nat) (disclosed : List RatchetChain) (front : PqxdhSelectedPostCompiler.Front M P I D K S B) :
    List CtxRomAuth.CtxKey :=
  (RawCtxSelectedMessageFreshness.keys disclosed front.roles.2).take qCand

/-- The truncated candidate list has at most `qCand` entries. -/
theorem candidates_length (qCand : Nat) (disclosed : List RatchetChain) (front : PqxdhSelectedPostCompiler.Front M P I D K S B) :
    (candidates qCand disclosed front).length ≤ qCand :=
  List.length_take_le _ _

/-- When the history is short enough, a revealed value equal to the selected key is a candidate key. -/
theorem candidates_hit (qCand : Nat) (disclosed : List RatchetChain) (front : PqxdhSelectedPostCompiler.Front M P I D K S B)
    (key : PqxdhSecretInputKdf.RootOutput) (short : disclosed.length + obsCount front ≤ qCand)
    (hit : RawCtxFreshChainCut.concreteChain key ∈ RawCtxSelectedMessageFreshness.known disclosed front.roles.2) :
    key ∈ candidates qCand disclosed front := by
  unfold candidates
  rw [List.take_of_length_le ((RawCtxSelectedMessageFreshness.keys_length disclosed front.roles.2).trans short)]
  exact (RawCtxSelectedMessageFreshness.keys_hit key disclosed front.roles.2).mp hit

end Candidates

section Hit
open PqxdhNativeSharedPrefix PqxdhSelectedStateInterpreter PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open RawCtxSelectedParentTable PqxdhSelectedFirstRecord PqxdhFirstBeaconRecordIntegrity PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily PqxdhInitialBeaconAmbient
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
    (before : PqxdhInitialOriginPostPath.Front M P I D K S B) (selected : RawCtxProtocolReveals.Owner S B)
    (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)
    (store : RawCtxSelectiveChainGame.Store) (key : RootOutput) (nonce : NonceOutput) (next : RootOutput) (b : Fin B)

local notation "target" => PqxdhInitialSourceExperiment.root source previousRoot response64 selected

/-- The instrumented key-hit run: the selected builder, then the instrumented evaluated post; the event is that the selected message key is among the first `qCand` candidate keys of the final front. -/
noncomputable def insHitRun (qCand : Nat) (disclosed : List RatchetChain) : ProbComp Bool := do
  let built ← firstBuild pre application initial selector aux source writer previousRoot response64 sender index metadata ready
    before selected shared privateState cache store key nonce next
  (fun result => decide (key ∈ candidates qCand disclosed result.2.1.1.1)) <$>
    (simulateQ (insEvaluated pre application initial selector aux source writer (productionStream source.crypto) none key target nonce next
      sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b)
      (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run (insStart index built)

/-- When the prepared history, the prior disclosures and the post budget fit into `qCand`, the instrumented key-disclosure run is dominated by the instrumented key-hit run. -/
theorem insKey_le_hit (number : Std.U64) (ancestors disclosed : List RatchetChain) (qPost qCand : Nat)
    (bounded : ∀ reply, (post reply).IsTotalQueryBound qPost)
    (count : disclosed.length + before.roles.2.observations.length + qPost ≤ qCand) :
    𝒟[insKeyRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode index
      metadata ready post before selected shared privateState cache store key nonce next b number ancestors disclosed] {true} ≤
    𝒟[insHitRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode index
      metadata ready post before selected shared privateState cache store key nonce next b qCand disclosed] {true} := by
  unfold insKeyRun insHitRun
  refine true_bind_mono_support _ _ _ fun built builtSupported => ?_
  refine map_mono_support _ _ _ fun result supported holds => ?_
  have holds' := @of_decide_eq_true _ (Classical.propDecidable _) holds
  refine decide_eq_true ?_
  have reached := evaluated_support pre application initial selector aux source writer (productionStream source.crypto) none key target
    nonce next sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b (post built.1.1) (insStart index built)
    result supported
  have grown := ins_history_run pre application initial selector aux source writer (productionStream source.crypto) none target
    nonce next sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b (post built.1.1) qPost
    (bounded built.1.1) (insStart index built).1 (result.1, result.2.1) reached
  have start := build_history pre application initial selector aux source writer previousRoot response64 sender
    index metadata ready before selected shared privateState cache store key nonce next built builtSupported
  change obsCount result.2.1.1.1 ≤ obsCount built.1.2 + qPost at grown
  exact candidates_hit qCand disclosed result.2.1.1.1 key (by omega) holds'.2

/-- The key-disclosure run is dominated by the instrumented key-hit run plus the restricted stop run, when the prepared history, the prior disclosures and the post budget fit into `qCand`. -/
theorem keyRun_le_hit (number : Std.U64) (ancestors disclosed : List RatchetChain) (qPost qCand : Nat)
    (bounded : ∀ reply, (post reply).IsTotalQueryBound qPost)
    (count : disclosed.length + before.roles.2.observations.length + qPost ≤ qCand) :
    𝒟[keyRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode index
      metadata ready post before selected shared privateState cache store key nonce next number ancestors disclosed] {true} ≤
    𝒟[insHitRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode index
      metadata ready post before selected shared privateState cache store key nonce next b qCand disclosed] {true} +
    𝒟[stopRun pre application initial selector aux source writer previousRoot response64 sender route decode index metadata ready
      post before selected shared privateState cache store key nonce next ancestors disclosed] {true} :=
  (keyRun_le pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode index
    metadata ready post before selected shared privateState cache store key nonce next b number ancestors disclosed).trans
    (add_le_add (insKey_le_hit pre application initial selector aux source writer selectedMessage previousRoot response64 sender route
      decode index metadata ready post before selected shared privateState cache store key nonce next b number ancestors disclosed
      qPost qCand bounded count) le_rfl)

end Hit

/-- A Boolean game whose continuation is dominated on the support of the first computation by the sum of two continuations is dominated by the two games. -/
theorem true_bind_le_support {α : Type} (mx : ProbComp α) (f g h : α → ProbComp Bool)
    (le : ∀ a ∈ support mx, 𝒟[f a] {true} ≤ 𝒟[g a] {true} + 𝒟[h a] {true}) :
    𝒟[mx >>= f] {true} ≤ 𝒟[mx >>= g] {true} + 𝒟[mx >>= h] {true} := by
  simp only [evalDist_apply_singleton] at le ⊢
  simp only [probOutput_bind_eq_tsum, ← ENNReal.tsum_add, ← mul_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases member : a ∈ support mx
  · gcongr
    exact le a member
  · simp [probOutput_eq_zero_of_not_mem_support member]

section HitGame
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCtx
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)) (b : Fin (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

/-- The key-hit continuation of one prepared context: completed preparations give `false`; a pending preparation runs the selected builder and the instrumented evaluated post and reports whether the selected key is among the first `qCand` candidate keys. -/
noncomputable def hitObserve (qCand : Nat) (target : Target S (B + 1))
    (context : PqxdhInitialLegalObserver.Context env0 kem attachedVerify primitives program post)
    (initialBlock : HmacBlock) (nonce : NonceOutput) (chain key : RootOutput) : ProbComp Bool :=
  match PqxdhInitialPreparedSourceInput.input env0 baseImpl kem attachedVerify primitives program post context
      target.owner target.number target.ancestors target.disclosed with
  | .inl _ => pure false
  | .inr input => insHitRun
      (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        context.secretKey context.ciphertext)
      (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        context.secretKey context.ciphertext)
      (initialLocal (A := A) (N := BareState 1) (env0).source input.selectedMessage zeroRoot
        (RawCtxSelectedInitialConstructor.response64 initialBlock))
      (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A)
        (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem context.secretKey context.ciphertext))
      (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks)
      (env0).source (env0).recordWriter input.selectedMessage zeroRoot (RawCtxSelectedInitialConstructor.response64 initialBlock)
      (env0).senderId (env0).route (env0).decode input.index input.metadata { input.ready with root := zeroRoot } input.post
      input.before input.selected input.shared input.privateState input.cache emptyStore key nonce chain b qCand target.disclosed

/-- The key-hit game: the actual preparation, the initializer block, the selected nonce and next chain, then the selected key, then the key-hit continuation. -/
noncomputable def hitGame (qCand : Nat) (target : Target S (B + 1)) : ProbComp Bool := do
  let context ← PqxdhCorrelatedExtractFamily.prepare baseImpl kem
    (PqxdhAuthenticatedRootExperiment.protocol env0 kem attachedVerify primitives program post)
  let initialBlock ← $ᵗ HmacBlock
  let nonce ← $ᵗ NonceOutput
  let chain ← $ᵗ RootOutput
  let key ← $ᵗ RootOutput
  hitObserve setup env callbacks baseImpl kem attachedVerify primitives program post b qCand target context initialBlock nonce chain key

/-- The candidate count of a certificate: the prior disclosures of the target, the initial and prechallenge reveal observations, and the post budget. -/
def candidateCount (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (target : Target S (B + 1)) : Nat :=
  target.disclosed.length + (env0).initial.roles.2.observations.length +
    PqxdhInitialPreparedSourceCaps.preCap env0 baseImpl kem program post c + postTotal setup env callbacks baseImpl kem program c

/-- The key-disclosure game is dominated by the key-hit game with the certificate's candidate count plus the restricted stop game. -/
theorem key_le_hit (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (target : Target S (B + 1)) :
    𝒟[keyGame setup env callbacks baseImpl kem attachedVerify primitives program post target] {true} ≤
    𝒟[hitGame setup env callbacks baseImpl kem attachedVerify primitives program post b
      (candidateCount setup env callbacks baseImpl kem program post c target) target] {true} +
    𝒟[stopGame setup env callbacks baseImpl kem attachedVerify primitives program post target] {true} := by
  have postBound : ∀ selection reply, (post selection reply).IsTotalQueryBound (postTotal setup env callbacks baseImpl kem program c) :=
    fun selection reply => total_of_kinds PqxdhPhase2SourceSchedulerBounds.classify (post selection reply) c.postBudget
      (c.postBound selection reply)
  unfold keyGame hitGame stopGame
  refine true_bind_le_support _ _ _ _ fun context supported => ?_
  refine true_bind_le _ _ _ _ fun initialBlock => ?_
  refine true_bind_le _ _ _ _ fun nonce => ?_
  refine true_bind_le _ _ _ _ fun chain => ?_
  refine true_bind_le _ _ _ _ fun key => ?_
  unfold keyObserve hitObserve stopObserve
  cases hstate : context.state with
  | completed decision =>
    simp only [PqxdhInitialPreparedSourceInput.input, hstate]
    simp
  | pending prepared ephemeral =>
    have history := PqxdhInitialPreparedSourceCaps.prepared_history env0 baseImpl kem attachedVerify primitives program post c context
      supported prepared ephemeral hstate
    simp only [PqxdhInitialPreparedSourceInput.input, hstate]
    refine keyRun_le_hit (bounded := postBound prepared.1.context.selection.1) (count := ?_) ..
    unfold candidateCount
    change target.disclosed.length + prepared.1.context.selection.2.roles.2.observations.length +
      postTotal setup env callbacks baseImpl kem program c ≤ _
    omega

end HitGame

section ClientGeneral
open PqxdhNativeSharedPrefix PqxdhSelectedStateInterpreter PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open RawCtxSelectedParentTable PqxdhSelectedFirstRecord PqxdhFirstBeaconRecordIntegrity PqxdhCorrelatedExpand
open PqxdhInitialBeaconAmbient PqxdhFirstBeaconRecordCtx
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (selectedMessage : PqxdhCorrelatedExtractFamily.Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
    (before : PqxdhInitialOriginPostPath.Front M P I D K S B) (selected : RawCtxProtocolReveals.Owner S B)
    (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)
    (store : RawCtxSelectiveChainGame.Store) (key : RootOutput) (nonce : NonceOutput) (next : RootOutput) (b : Fin B)

local notation "target" => PqxdhInitialSourceExperiment.root source previousRoot response64 selected
local notation "challenger" => AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder decode) source.crypto key

/-- Any event of the instrumented evaluated post, read from the post result and the instrumented state, is the instrumented post bit of that event. -/
theorem evaluated_postBit (event : Option Bool × InsState M P I D K A N RootOracle.QueryCache S B → Bool)
    (reply : RustM (Option PqxdhServerRegistrationPublication.Response)) (start : InsFull M P I D K A N RootOracle.QueryCache S B) :
    (fun result => event (result.1, result.2.1)) <$>
      (simulateQ (insEvaluated pre application initial selector aux source writer (productionStream source.crypto) none key target nonce next
        sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b)
        (RawCtxSelectedFamilyNonceCoupling.optionalClient (post reply))).run start =
      insPostBit pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode post selected
        key nonce next b event reply start := by
  unfold insPostBit
  rw [← insEvaluated_program]

/-- When every first send of the initial Server kernel is known, the builder followed by the instrumented post bit of any event (which may mention the fixed selected key) is the key-free instrumented client with that output, evaluated by the selected-key challenger from any start that differs from the initial challenger only by the preparation cache and a public-hash log. -/
theorem postBit_client (event : Option Bool × InsState M P I D K A N RootOracle.QueryCache S B → Bool)
    (known : ∀ kernel, initialKernel response64 = .ok kernel → ∀ context,
      KnownSend (productionStream source.crypto) none target nonce next kernel context)
    (log : List Pqxdh.Bytes) :
    (firstBuild pre application initial selector aux source writer previousRoot response64 sender index metadata ready
      before selected shared privateState cache store key nonce next >>= fun built =>
      insPostBit pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode post
        selected key nonce next b event built.1.1 (insStart index built)) =
      Prod.fst <$> (simulateQ challenger (insFirstClient pre application initial selector aux source writer selectedMessage previousRoot
        response64 sender route decode index metadata ready post before selected shared privateState cache store nonce next b
        event)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log)) := by
  have related := build_rel pre application initial selector aux source writer (productionStream source.crypto) none key target
    nonce next decode sender (initialKernel response64) index metadata ready (initialFront before) known
    ((initialShared shared privateState cache store).1,
      RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log))
  simp only [evaluate, StateT.run] at related
  have clientEq : Prod.fst <$> (simulateQ challenger (insFirstClient pre application initial selector aux source writer selectedMessage
      previousRoot response64 sender route decode index metadata ready post before selected shared privateState cache store nonce next b
        event)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log)) =
      (simulateQ challenger (((compiledBuild pre application initial selector aux source writer (productionStream source.crypto) none
        target nonce next sender (initialKernel response64) index metadata ready).run (initialFront before)).run
          (initialShared shared privateState cache store).1)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log)) >>= fun result =>
        insPostBit pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode post
          selected key nonce next b event result.1.1.1
          (((result.1.1.2, result.1.2), (selectedAfter PqxdhInitialSourcePublication.empty result.1.1.2 index true result.1.1.1, none, false)),
            result.2) := by
    simp only [insFirstClient, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure]
    refine bind_congr fun result => ?_
    simp only [insPostBit, bind_pure_comp]
    change _ = (fun result => event (result.1, result.2.1)) <$>
      (pair <$> (simulateQ challenger (((simulateQ (insImpl pre application initial selector aux source writer
        (productionStream source.crypto) none target nonce next sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage)
          b) (post result.1.1.1)).run).run ((result.1.1.2, result.1.2),
            (selectedAfter PqxdhInitialSourcePublication.empty result.1.1.2 index true result.1.1.1, none, false)))).run result.2)
    rw [Functor.map_map]
    rfl
  have cleaned : ((simulateQ challenger (((compiledBuild pre application initial selector aux source writer
      (productionStream source.crypto) none target nonce next sender (initialKernel response64) index metadata ready).run
        (initialFront before)).run (initialShared shared privateState cache store).1)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log)) >>= fun result =>
        insPostBit pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode post
          selected key nonce next b event result.1.1.1
          (((result.1.1.2, result.1.2), (selectedAfter PqxdhInitialSourcePublication.empty result.1.1.2 index true result.1.1.1, none, false)),
            result.2)) =
      ((simulateQ challenger (((compiledBuild pre application initial selector aux source writer
      (productionStream source.crypto) none target nonce next sender (initialKernel response64) index metadata ready).run
        (initialFront before)).run (initialShared shared privateState cache store).1)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log)) >>= fun result =>
        insPostBit pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode post
          selected key nonce next b event result.1.1.1
          (((result.1.1.2, result.1.2), (selectedAfter PqxdhInitialSourcePublication.empty result.1.1.2 index true result.1.1.1, none, false)),
            { AdaptiveCtxDynamicKnownKeys.initialSource with cache := result.2.cache })) := by
    refine bind_congr_of_forall_mem_support _ fun result supported => ?_
    obtain ⟨shared', clean⟩ := related.2 (pair result) (by
      simp only [support_map, Set.mem_image]
      exact ⟨result, supported, rfl⟩)
    rw [insPostBit_ghost]
    change result.2 = _ at clean
    rw [clean]
    rfl
  have build : firstBuild pre application initial selector aux source writer previousRoot response64 sender index metadata ready
      before selected shared privateState cache store key nonce next =
      Prod.map id project <$> (pair <$> (simulateQ challenger (((compiledBuild pre application initial selector aux source writer
        (productionStream source.crypto) none target nonce next sender (initialKernel response64) index metadata ready).run
          (initialFront before)).run (initialShared shared privateState cache store).1)).run
          (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log))) :=
    related.1.symm
  rw [clientEq, cleaned, build, bind_map_left, bind_map_left]
  rfl


/-- The instrumented key-hit run is the builder followed by the instrumented post bit of the truncated candidate hit. -/
theorem insHitRun_postBit (qCand : Nat) (disclosed : List RatchetChain) :
    insHitRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode index
      metadata ready post before selected shared privateState cache store key nonce next b qCand disclosed =
    (firstBuild pre application initial selector aux source writer previousRoot response64 sender index metadata ready
      before selected shared privateState cache store key nonce next >>= fun built =>
      insPostBit pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode post
        selected key nonce next b (fun result => decide (key ∈ candidates qCand disclosed result.2.1.1)) built.1.1
        (insStart index built)) := by
  unfold insHitRun
  refine bind_congr fun built => ?_
  exact evaluated_postBit pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode
    post selected key nonce next b (fun result => decide (key ∈ candidates qCand disclosed result.2.1.1)) built.1.1 (insStart index built)

end ClientGeneral

section HitClient
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCtx CtxRomAuth AdaptiveCtxSharedHash
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)) (b : Fin (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

/-- The key-free candidate output of a prepared result: no candidates for completed preparations, otherwise the CTX key bytes of the prior disclosures and of every known value revealed in the final front, in disclosure order. -/
def hitOut (target : Target S (B + 1)) : PrepResult M P I (DhPair setup) K A S (B + 1) → List CtxKey
  | none => []
  | some result => RawCtxSelectedMessageFreshness.keys target.disclosed result.2.2.2.1.1.roles.2

/-- The key-free candidate suffix after the prelude. -/
noncomputable def keySuffix (target : Target S (B + 1))
    (sample : Packet (M := M) (P := P) (I := I) (K := K) (A := A) (KemSK := KemSK) setup program × HmacBlock × NonceOutput × RootOutput) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec (List CtxKey) :=
  hitOut setup target <$> insSuffixRun setup env callbacks baseImpl kem attachedVerify primitives program post b target sample

/-- The constructed key-free candidate client: the forwarded preparation prelude, then the instrumented first-record suffix, returning the candidate keys of the final front. It never reads the selected key. -/
noncomputable def keyClient (target : Target S (B + 1)) : OracleComp AdaptiveCtxDynamicKnownKeys.Spec (List CtxKey) :=
  simulateQ RawCtxSourceSharedRom.forward (prelude setup env callbacks baseImpl kem attachedVerify primitives program post) >>=
    keySuffix setup env callbacks baseImpl kem attachedVerify primitives program post b target

/-- Outside the initial half alias, the key-hit continuation of the first Beacon record is the truncated candidate hit of the key-free candidate suffix, evaluated by the selected-key challenger from the reached cache and public log. -/
theorem hitObserve_eq (qCand : Nat)
    (sample : Packet (M := M) (P := P) (I := I) (K := K) (A := A) (KemSK := KemSK) setup program × HmacBlock × NonceOutput × RootOutput)
    (cache : CtxRO.QueryCache) (log : List Pqxdh.Bytes) (key : RootOutput)
    (aliased : ¬ RawCtxSendLineageCollision.InitialAlias sample.2.1) :
    hitObserve setup env callbacks baseImpl kem attachedVerify primitives program post b qCand (firstBeacon b)
        (restoreSample setup env callbacks kem attachedVerify primitives program post sample cache).1
        sample.2.1 sample.2.2.1 sample.2.2.2 key =
      (fun result => decide (key ∈ result.1.take qCand)) <$>
        (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder (env0).decode)
          (env0).source.crypto key) (keySuffix setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)
            sample)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (cache, log)) := by
  unfold hitObserve keySuffix insSuffixRun restoreSample
  rw [← PqxdhSourceSharedInput.input_cache setup env callbacks program post attachedVerify primitives baseImpl kem]
  cases pending : PqxdhSourceSharedInput.input setup env callbacks program post attachedVerify primitives baseImpl kem
      (firstBeacon b).owner (firstBeacon b).number (firstBeacon b).ancestors (firstBeacon b).disclosed sample.1 with
  | inl decision => simp [PqxdhSourceSharedInput.restore, hitOut]
  | inr input =>
    have owner := input_selected setup env callbacks baseImpl kem attachedVerify primitives program post _ _ _ _ sample.1 input pending
    simp only [PqxdhSourceSharedInput.restore]
    have known : ∀ kernel, initialKernel (RawCtxSelectedInitialConstructor.response64 sample.2.1) = .ok kernel → ∀ context,
        KnownSend (productionStream (env0).source.crypto) none (PqxdhInitialSourceExperiment.root (env0).source zeroRoot
          (RawCtxSelectedInitialConstructor.response64 sample.2.1) (firstBeacon b).owner) sample.2.2.1 sample.2.2.2 kernel context :=
      fun kernel initialized context => initial_known (S := S) (env0).source sample.2.1 b sample.2.2.1 sample.2.2.2
        aliased kernel initialized context
    rw [owner] at *
    rw [insHitRun_postBit, postBit_client (known := known) (log := log), insFirstClient_run, simulateQ_map, StateT.run_map, simulateQ_map,
      StateT.run_map, simulateQ_map, StateT.run_map, Functor.map_map, Functor.map_map, Functor.map_map]
    rfl

/-- The key-hit game with the initial half-alias runs mapped to `false`. -/
noncomputable def hitSeparated (qCand : Nat) (target : Target S (B + 1)) : ProbComp Bool := do
  let context ← PqxdhCorrelatedExtractFamily.prepare baseImpl kem
    (PqxdhAuthenticatedRootExperiment.protocol env0 kem attachedVerify primitives program post)
  let initialBlock ← $ᵗ HmacBlock
  let nonce ← $ᵗ NonceOutput
  let chain ← $ᵗ RootOutput
  let key ← $ᵗ RootOutput
  @ite _ (RawCtxSendLineageCollision.InitialAlias initialBlock) (Classical.propDecidable _) (pure false)
    (hitObserve setup env callbacks baseImpl kem attachedVerify primitives program post b qCand target context initialBlock nonce chain key)

/-- The key-hit game is dominated by the initial half-alias term `2^-256` plus the separated key-hit game. -/
theorem hit_le_separated (qCand : Nat) (target : Target S (B + 1)) :
    𝒟[hitGame setup env callbacks baseImpl kem attachedVerify primitives program post b qCand target] {true} ≤
      (1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) +
        𝒟[hitSeparated setup env callbacks baseImpl kem attachedVerify primitives program post b qCand target] {true} := by
  refine le_trans ?_ (add_le_add (alias_bound setup env callbacks baseImpl kem attachedVerify primitives program post) le_rfl)
  unfold hitGame hitSeparated aliasGame
  refine true_bind_le _ _ _ _ fun context => ?_
  refine true_bind_le _ _ _ _ fun initialBlock => ?_
  refine true_bind_le _ _ _ _ fun nonce => ?_
  refine true_bind_le _ _ _ _ fun chain => ?_
  refine true_bind_le _ _ _ _ fun key => ?_
  classical
  by_cases aliased : RawCtxSendLineageCollision.InitialAlias initialBlock
  · rw [ite_eq_left_iff.mpr fun impossible => absurd aliased impossible,
      show (@decide (RawCtxSendLineageCollision.InitialAlias initialBlock) (Classical.propDecidable _)) = true from
        @decide_eq_true _ (Classical.propDecidable _) aliased]
    refine le_add_right ?_
    simp only [evalDist_apply_singleton, probOutput_pure_self]
    exact probOutput_le_one
  · rw [ite_eq_right_iff.mpr fun holds => absurd holds aliased]
    exact le_add_self

/-- The key-retaining source game of the candidate client: the selected key, the client run by the selected-key challenger from the ordinary initial state, and the event that the key is among the first `qCand` candidates. -/
noncomputable def hitSource (qCand : Nat) (target : Target S (B + 1)) : ProbComp Bool := do
  let key ← $ᵗ CtxKey
  let result ← (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto key)
    (keyClient setup env callbacks baseImpl kem attachedVerify primitives program post b target)).run
      AdaptiveCtxDynamicKnownKeys.initialSource
  pure (decide (key ∈ result.1.take qCand))

/-- Sampling the selected key after the forwarded prelude in the key-retaining source game of the candidate client. -/
theorem hitSource_reorder (qCand : Nat) (target : Target S (B + 1)) :
    𝒟[hitSource setup env callbacks baseImpl kem attachedVerify primitives program post b qCand target] =
    𝒟[do
      let result ← (simulateQ AdaptiveCtxSharedTarget.sharedImpl
        (prelude setup env callbacks baseImpl kem attachedVerify primitives program post)).run (∅, [])
      let key ← $ᵗ RootOutput
      (fun final : List CtxKey × AdaptiveCtxDynamicKnownKeys.SourceState => decide (key ∈ final.1.take qCand)) <$>
        (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder (env0).decode)
          (env0).source.crypto key) (keySuffix setup env callbacks baseImpl kem attachedVerify primitives program post b target
            result.1)).run (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource result.2)] := by
  have exchanged := RawCtxPrefixKeyOrder.complete true (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
    (prelude setup env callbacks baseImpl kem attachedVerify primitives program post)
    (fun key context state => (fun final : List CtxKey × AdaptiveCtxDynamicKnownKeys.SourceState =>
      decide (key ∈ final.1.take qCand)) <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto key)
        (keySuffix setup env callbacks baseImpl kem attachedVerify primitives program post b target context)).run state)
  refine evalDist_eq_of_evalSPMF_eq _ _ ?_
  rw [exchanged]
  unfold hitSource keyClient
  simp only [simulateQ_bind, StateT.run_bind, bind_pure_comp, map_bind]

/-- The separated key-hit game of the first Beacon record is dominated by the key-retaining source game of the candidate client. -/
theorem separated_le_source (qCand : Nat) :
    𝒟[hitSeparated setup env callbacks baseImpl kem attachedVerify primitives program post b qCand (firstBeacon b)] {true} ≤
    𝒟[hitSource setup env callbacks baseImpl kem attachedVerify primitives program post b qCand (firstBeacon b)] {true} := by
  have reorder := prepared_reorder setup env callbacks baseImpl kem attachedVerify primitives program post
    (fun context initialBlock nonce chain key =>
      @ite _ (RawCtxSendLineageCollision.InitialAlias initialBlock) (Classical.propDecidable _) (pure false)
        (hitObserve setup env callbacks baseImpl kem attachedVerify primitives program post b qCand (firstBeacon b) context
          initialBlock nonce chain key))
  change hitSeparated setup env callbacks baseImpl kem attachedVerify primitives program post b qCand (firstBeacon b) = _ at reorder
  rw [reorder, hitSource_reorder]
  refine true_bind_mono _ _ _ fun result => true_bind_mono _ _ _ fun key => ?_
  classical
  by_cases aliased : RawCtxSendLineageCollision.InitialAlias result.1.2.1
  · rw [ite_eq_left_iff.mpr fun impossible => absurd aliased impossible]
    simp
  · rw [ite_eq_right_iff.mpr fun holds => absurd holds aliased,
      hitObserve_eq setup env callbacks baseImpl kem attachedVerify primitives program post b qCand result.1 result.2.1 result.2.2 key
        aliased]

end HitClient

section Canonical
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxQueryBounds AdaptiveCtxDynamicKnownBounds
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation

/-- The ordinary one-key CTX candidate client of a key-free dynamic candidate client: the dynamic known-key reduction of `AdaptiveCtxDynamicKnownKeys`, returning the first `qCand` candidates of the dynamic client. It contains no selected key. -/
noncomputable def recvClient (c : Pqxdh.Crypto) (qCand : Nat)
    (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec (List CtxKey)) : OracleComp ReceiveSpec (Unit × List CtxKey) :=
  (fun result => ((), result.1.take qCand)) <$>
    AdaptiveCtxDynamicKnownKeys.wrapped c client AdaptiveCtxDynamicKnownKeys.initialReduction

/-- Every candidate list of the ordinary candidate client has at most `qCand` entries. -/
theorem recvClient_length (c : Pqxdh.Crypto) (qCand : Nat) (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec (List CtxKey)) :
    ∀ result ∈ support (recvClient c qCand client), result.2.length ≤ qCand := by
  intro result supported
  simp only [recvClient, support_map, Set.mem_image] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  exact List.length_take_le _ _

/-- For a fixed selected key, the truncated candidate hit of the ordinary candidate client in the canonical shared-ROM game is the truncated candidate hit of the dynamic client in the selected-key source game. -/
theorem canonical_hit (decode : RawDecoder) (c : Pqxdh.Crypto) (qCand : Nat)
    (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec (List CtxKey)) (key : CtxKey) :
    (fun result => decide (key ∈ result.1.2)) <$> AdaptiveCtxCanonical.canonicalGame decode c key (recvClient c qCand client) =
    (fun result => decide (key ∈ result.1.take qCand)) <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true decode c key) client).run AdaptiveCtxDynamicKnownKeys.initialSource := by
  have scheduled := AdaptiveCtxDynamicKnownKeys.schedule_interpretation true decode c key client
    AdaptiveCtxDynamicKnownKeys.initialReduction AdaptiveCtxSharedModes.initialState
  have canonical := AdaptiveCtxSharedModes.real_schedule decode c key (recvClient c qCand client) AdaptiveCtxSharedModes.initialState
  rw [AdaptiveCtxSharedModes.canonical_initial] at canonical
  unfold AdaptiveCtxCanonical.canonicalGame
  rw [← canonical, show AdaptiveCtxDynamicKnownKeys.initialSource =
    AdaptiveCtxDynamicKnownKeys.project (AdaptiveCtxDynamicKnownKeys.initialReduction, AdaptiveCtxSharedModes.initialState) from rfl,
    ← scheduled]
  unfold recvClient
  simp only [simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

/-- The retained candidate-hit event is decided by list membership. -/
local instance candidateDecidable (result : CtxKey × ((Unit × List CtxKey) × AdaptiveCtxCanonical.CanonicalState)) :
    Decidable (RawCtxSelectedKeyProbes.CandidateHit result) :=
  inferInstanceAs (Decidable (result.1 ∈ result.2.1.2))

set_option linter.deprecated false in
/-- The key-retaining source game of a key-free dynamic candidate client has the probability of the retained candidate-hit event of the ordinary candidate client. -/
theorem source_candidate (decode : RawDecoder) (c : Pqxdh.Crypto) (qCand : Nat)
    (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec (List CtxKey)) :
    𝒟[do
      let key ← $ᵗ CtxKey
      let result ← (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true decode c key) client).run
        AdaptiveCtxDynamicKnownKeys.initialSource
      pure (decide (key ∈ result.1.take qCand))] {true} =
    Pr[RawCtxSelectedKeyProbes.CandidateHit |
      AdaptiveCtxPrefixValidation.retainedCanonicalGame decode c (recvClient c qCand client)] := by
  have games : (do
      let key ← $ᵗ CtxKey
      let result ← (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true decode c key) client).run
        AdaptiveCtxDynamicKnownKeys.initialSource
      pure (decide (key ∈ result.1.take qCand))) =
      (fun result => decide (RawCtxSelectedKeyProbes.CandidateHit result)) <$>
        AdaptiveCtxPrefixValidation.retainedCanonicalGame decode c (recvClient c qCand client) := by
    simp only [AdaptiveCtxPrefixValidation.retainedCanonicalGame, map_bind, map_pure]
    refine bind_congr fun key => ?_
    rw [bind_pure_comp, ← canonical_hit, map_eq_bind_pure_comp]
    rfl
  rw [games, true_mass_eq]

/-- The CTX key-recovery loss of an ordinary candidate client: twice the sum of the IND$ advantage of the constructed validation reduction of the probed client, the hash-guessing term over the source hashes and candidate probes, and the INT-CTXT advantages of the constructed attempt-indexed reductions. -/
noncomputable def keyLoss (decode : RawDecoder) (c : Pqxdh.Crypto) (fallback : ModifiedNonceAeadForgery)
    (client : OracleComp ReceiveSpec (Unit × List CtxKey)) (qHash qCand qRaw : Nat) : ℝ≥0∞ :=
  2 * (ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
    (AdaptiveCtxPrefixValidation.validationReduction decode c (RawCtxSelectedKeyProbes.finish client) (qHash + qCand))) +
    ((qHash + qCand : Nat) : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
    ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
      (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback
        (AdaptiveCtxReceive.wrapped decode (RawCtxSelectedKeyProbes.finish client)) index))

/-- The key-retaining source game of a key-free dynamic candidate client is bounded by the CTX key-recovery loss of its ordinary candidate client (`RawCtxSelectedKeyProbes.candidate_bound`), with the dynamic client's hash, seal and raw budgets. -/
theorem source_candidate_bound (decode : RawDecoder) (c : Pqxdh.Crypto) (fallback : ModifiedNonceAeadForgery) (qCand : Nat)
    (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec (List CtxKey)) (qHash qSeal qRaw : Nat)
    (hashBound : client.IsQueryBoundP HashRoute qHash)
    (sealBound : client.IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass IsRawQuery) qRaw)
    (small : qSeal < 2 ^ 96) :
    𝒟[do
      let key ← $ᵗ CtxKey
      let result ← (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true decode c key) client).run
        AdaptiveCtxDynamicKnownKeys.initialSource
      pure (decide (key ∈ result.1.take qCand))] {true} ≤
    keyLoss decode c fallback (recvClient c qCand client) qHash qCand qRaw := by
  rw [source_candidate]
  refine RawCtxSelectedKeyProbes.candidate_bound decode c fallback (recvClient c qCand client) qHash qCand qSeal qRaw ?_
    (recvClient_length c qCand client) ?_ ?_ small
  · exact (isQueryBoundP_map_iff _ _ _).mpr (hash_bound c client qHash hashBound _)
  · exact (isQueryBoundP_map_iff _ _ _).mpr (target_bound c _ AdaptiveCtxSharedTarget.forward_seal_class client qSeal sealBound _)
  · exact (isQueryBoundP_map_iff _ _ _).mpr (target_bound c _ AdaptiveCtxSharedTarget.forward_raw_class client qRaw rawBound _)

end Canonical

section KeyBound
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCtx CtxRomAuth AdaptiveCtxSharedHash
open RawCtxSelectedAuthenticationObserver AdaptiveCtxDynamicKnownBounds AdaptiveCtxQueryBounds AdaptiveCtxReceive
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)) (b : Fin (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

/-- The candidate client's request budget in any class that the source-local callbacks never use: the forwarded prelude's budget, one builder request and the post budget. -/
theorem keyClient_uses (target : Target S (B + 1))
    (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate]
    (externalZero : ∀ (secret : KemSK) (challenge : MlKem768Ciphertext) (selectedMessage : Message) (response : PqxdhInitialRootLabelService.Response)
      query state, ((PqxdhSelectedCallbackCompiler.lower (extra := SelectorSpec baseSpec)
        (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem secret challenge)
        (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem secret challenge)
        (initialLocal (A := A) (N := BareState 1) (env0).source selectedMessage zeroRoot response)
        (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A)
          (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem secret challenge))
        (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) (.inl query)).run state).IsQueryBoundP predicate 0)
    (qPrelude : Nat)
    (preludeBound : (simulateQ RawCtxSourceSharedRom.forward
      (prelude setup env callbacks baseImpl kem attachedVerify primitives program post)).IsQueryBoundP predicate qPrelude)
    (qPost : Nat) (postBound : ∀ selection reply, (post selection reply).IsTotalQueryBound qPost) :
    (keyClient setup env callbacks baseImpl kem attachedVerify primitives program post b target).IsQueryBoundP predicate
      (qPrelude + (1 + qPost)) := by
  refine isQueryBoundP_bind preludeBound fun sample _ => ?_
  unfold keySuffix insSuffixRun
  split
  · simp
  · rename_i input pending
    obtain ⟨selection, selected⟩ := input_post setup env callbacks baseImpl kem attachedVerify primitives program post _ _ _ _
      sample.1 input pending
    rw [isQueryBoundP_map_iff, isQueryBoundP_map_iff]
    apply insFirstRun_uses (predicate := predicate) (externalZero := externalZero _ _ _ _) (qPost := qPost)
    exact fun reply => selected ▸ postBound selection reply

/-- The key-recovery loss of the first Beacon record with the certificate budgets: the CTX key-recovery loss of the ordinary candidate client of `keyClient`, with `qPrelude + 1 + qPost` hash requests, `1 + qPost` raw openings and the certificate's candidate count. -/
noncomputable def recoveryLoss (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (ctxFallback : ModifiedNonceAeadForgery) (qPrelude : Nat) : ℝ≥0∞ :=
  keyLoss (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto ctxFallback
    (recvClient (env0).source.crypto (candidateCount setup env callbacks baseImpl kem program post c (firstBeacon b))
      (keyClient setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)))
    (qPrelude + (1 + postTotal setup env callbacks baseImpl kem program c))
    (candidateCount setup env callbacks baseImpl kem program post c (firstBeacon b))
    (1 + postTotal setup env callbacks baseImpl kem program c)

/-- The key-disclosure game of the first Beacon record is bounded by the CTX key-recovery loss of the constructed candidate client, the initial half-alias term `2^-256` and the restricted stop game. -/
theorem key_bound_stop (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (ctxFallback : ModifiedNonceAeadForgery) (qPrelude : Nat)
    (prepareHash : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program post qPrelude)
    (small : 1 + postTotal setup env callbacks baseImpl kem program c < 2 ^ 96) :
    𝒟[keyGame setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)] {true} ≤
      recoveryLoss setup env callbacks baseImpl kem attachedVerify primitives program post b c ctxFallback qPrelude +
      (1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) +
      𝒟[stopGame setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)] {true} := by
  have postBound : ∀ selection reply, (post selection reply).IsTotalQueryBound (postTotal setup env callbacks baseImpl kem program c) :=
    fun selection reply => total_of_kinds PqxdhPhase2SourceSchedulerBounds.classify (post selection reply) c.postBudget
      (c.postBound selection reply)
  have hashBound := keyClient_uses setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)
    HashRoute (fun _ _ _ _ query state => external_no_hash _ _ _ _ _ query state) qPrelude
    (prelude_hash setup env callbacks baseImpl kem attachedVerify primitives program post qPrelude prepareHash) _ postBound
  have sealBound := keyClient_uses setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)
    (TargetClass SourceSeal) (fun _ _ _ _ query state => external_no_seal _ _ _ _ _ query state) 0 (forward_no_seal _) _ postBound
  have rawBound := keyClient_uses setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)
    (TargetClass AdaptiveCtxReceive.IsRawQuery)
    (fun _ _ _ _ query state => PqxdhSelectedInitialOwnerCompiler.external_no_open _ _ _ _ _ query state) 0 (forward_no_open _) _
      postBound
  rw [Nat.zero_add] at sealBound rawBound
  have recovery := source_candidate_bound (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto ctxFallback
    (candidateCount setup env callbacks baseImpl kem program post c (firstBeacon b))
    (keyClient setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)) _ _ _ hashBound sealBound
    rawBound small
  have hit := (key_le_hit setup env callbacks baseImpl kem attachedVerify primitives program post b c (firstBeacon b)).trans
    (add_le_add ((hit_le_separated setup env callbacks baseImpl kem attachedVerify primitives program post b _ (firstBeacon b)).trans
      (add_le_add le_rfl ((separated_le_source setup env callbacks baseImpl kem attachedVerify primitives program post b _).trans
        recovery))) le_rfl)
  refine hit.trans (le_of_eq ?_)
  unfold recoveryLoss
  ring

end KeyBound

section KeyHeadline
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCtx CtxRomAuth AdaptiveCtxSharedHash
open RawCtxSelectedAuthenticationObserver AdaptiveCtxDynamicKnownBounds AdaptiveCtxQueryBounds AdaptiveCtxReceive
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅

/-- The candidate count of the first Beacon record: the initial and prechallenge reveal observations and the post budget (the first-record target has no prior disclosures). -/
theorem candidateCount_first (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (b : Fin (B + 1)) :
    candidateCount setup env callbacks baseImpl kem program post c (firstBeacon b) =
      (env0).initial.roles.2.observations.length + PqxdhInitialPreparedSourceCaps.preCap env0 baseImpl kem program post c +
        postTotal setup env callbacks baseImpl kem program c := by
  simp [candidateCount, firstBeacon]

/-- The CTX key-recovery loss is finite. -/
theorem keyLoss_ne_top (decode : RawDecoder) (c : Pqxdh.Crypto) (fallback : ModifiedNonceAeadForgery)
    (client : OracleComp ReceiveSpec (Unit × List CtxKey)) (qHash qCand qRaw : Nat) :
    keyLoss decode c fallback client qHash qCand qRaw ≠ ⊤ := by
  unfold keyLoss
  refine ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ?_⟩, ?_⟩)
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.inv_ne_top.mpr (by positivity))
  · exact ENNReal.sum_ne_top.mpr fun index _ => prEvent_ne_top _

/-- `key_bound`: the key-disclosure game of the first Beacon record (in the key-last run, the first-record event and no hidden disclosure hold while the uniform record key equals a revealed value) is at most the CTX key-recovery loss `recoveryLoss` of the constructed candidate client, the initial half-alias term `2^-256` and the nonce-repeat stop bound of `PqxdhFirstRecordStopTagged.stop_bound`. -/
theorem key_bound (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)) (b : Fin (B + 1))
    (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (ctxFallback : ModifiedNonceAeadForgery) (qPrelude : Nat)
    (prepareHash : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program post qPrelude)
    (small : 1 + postTotal setup env callbacks baseImpl kem program c < 2 ^ 96) :
    𝒟[keyGame setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)] {true} ≤
      recoveryLoss setup env callbacks baseImpl kem attachedVerify primitives program post b c ctxFallback qPrelude +
      (1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) +
      ((1 + c.postBudget (.inl .send) + 51 * (c.postBudget (.inl .raw) + c.postBudget (.inr 5)) : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  (key_bound_stop setup env callbacks baseImpl kem attachedVerify primitives program post b c ctxFallback qPrelude prepareHash small).trans
    (add_le_add le_rfl (PqxdhFirstRecordStopTagged.stop_bound setup env callbacks baseImpl kem attachedVerify primitives program post
      c.postBudget c.postBound b))

/-- The real form of `key_bound`. -/
theorem key_real (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)) (b : Fin (B + 1))
    (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (ctxFallback : ModifiedNonceAeadForgery) (qPrelude : Nat)
    (prepareHash : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program post qPrelude)
    (small : 1 + postTotal setup env callbacks baseImpl kem program c < 2 ^ 96) :
    (𝒟[keyGame setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)] {true}).toReal ≤
      (recoveryLoss setup env callbacks baseImpl kem attachedVerify primitives program post b c ctxFallback qPrelude).toReal +
      1 / 2 ^ 256 +
      ((1 + c.postBudget (.inl .send) + 51 * (c.postBudget (.inl .raw) + c.postBudget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256 := by
  have bound := key_bound setup env callbacks baseImpl kem attachedVerify primitives program post b c ctxFallback qPrelude prepareHash small
  have lossFinite := keyLoss_ne_top (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto ctxFallback
    (recvClient (env0).source.crypto (candidateCount setup env callbacks baseImpl kem program post c (firstBeacon b))
      (keyClient setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)))
    (qPrelude + (1 + postTotal setup env callbacks baseImpl kem program c))
    (candidateCount setup env callbacks baseImpl kem program post c (firstBeacon b))
    (1 + postTotal setup env callbacks baseImpl kem program c)
  change recoveryLoss setup env callbacks baseImpl kem attachedVerify primitives program post b c ctxFallback qPrelude ≠ ⊤ at lossFinite
  have halfFinite : (1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top ENNReal.one_ne_top (by positivity)
  have stopFinite : ((1 + c.postBudget (.inl .send) + 51 * (c.postBudget (.inl .raw) + c.postBudget (.inr 5)) : ℕ) : ℝ≥0∞) /
      2 ^ 256 ≠ ⊤ := ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)
  have real := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨lossFinite, halfFinite⟩, stopFinite⟩) bound
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨lossFinite, halfFinite⟩) stopFinite, ENNReal.toReal_add lossFinite halfFinite,
    ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast] at real
  simpa using real

end KeyHeadline

section KeyCorollary
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCtx CtxRomAuth AdaptiveCtxSharedHash
open RawCtxSelectedAuthenticationObserver AdaptiveCtxDynamicKnownBounds AdaptiveCtxQueryBounds AdaptiveCtxReceive
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅

/-- First-record left-or-right confidentiality with the key-disclosure games bounded: `first_record_confidentiality` with each `keyGame` replaced through `key_bound` by the CTX key-recovery loss `recoveryLoss` of the constructed candidate client (IND$ advantage of the constructed validation reduction, `(qHash + qCand)/2^128`, INT-CTXT advantages of the constructed attempt-indexed reductions, all doubled), a second nonce-repeat stop bound and `2^-256`. The only remaining explicit game terms are the two `collGame` terms. -/
theorem first_record_confidentiality_key (b : Fin (B + 1))
    (adversary : program.Selection → RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (c0 : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program (confPost adversary b false))
    (c1 : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program (confPost adversary b true))
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem (env0).native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect (env0).source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (ctxFallback : ModifiedNonceAeadForgery) (qPrelude0 qPrelude1 : Nat)
    (prepareHash0 : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false)
      qPrelude0)
    (prepareHash1 : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true)
      qPrelude1)
    (small0 : 1 + postTotal setup env callbacks baseImpl kem program c0 < 2 ^ 96)
    (small1 : 1 + postTotal setup env callbacks baseImpl kem program c1 < 2 ^ 96) :
    |(𝒟[confGame setup env callbacks baseImpl kem attachedVerify primitives program b adversary false] {true}).toReal -
      (𝒟[confGame setup env callbacks baseImpl kem attachedVerify primitives program b adversary true] {true}).toReal| ≤
    (twinLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b c0 ctxFallback
      qPrelude0).toReal +
    (twinLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b c1 ctxFallback
      qPrelude1).toReal +
    (PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (confPost adversary b false)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (confPost adversary b false) c0) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (confPost adversary b false) hmac fallback
      ordinaryFallback) +
    (PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (confPost adversary b true)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (confPost adversary b true) c1) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (confPost adversary b true) hmac fallback
      ordinaryFallback) +
    (𝒟[collGame setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b (firstBeacon b)]
      {true}).toReal +
    (𝒟[collGame setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b (firstBeacon b)]
      {true}).toReal +
    (recoveryLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b c0 ctxFallback
      qPrelude0).toReal +
    (recoveryLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b c1 ctxFallback
      qPrelude1).toReal +
    2 * (((1 + c0.postBudget (.inl .send) + 51 * (c0.postBudget (.inl .raw) + c0.postBudget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256) +
    2 * (((1 + c1.postBudget (.inl .send) + 51 * (c1.postBudget (.inl .raw) + c1.postBudget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256) +
    4 / 2 ^ 256 := by
  have main := first_record_confidentiality setup env callbacks baseImpl kem attachedVerify primitives program b adversary c0 c1
    compatible adapter functional hmac correct fallback ordinaryFallback ctxFallback qPrelude0 qPrelude1 prepareHash0 prepareHash1
    small0 small1
  have key0 := key_real setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b c0 ctxFallback
    qPrelude0 prepareHash0 small0
  have key1 := key_real setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b c1 ctxFallback
    qPrelude1 prepareHash1 small1
  linarith

/-- First-record left-or-right confidentiality with the adversary's own budget and the key-disclosure games bounded: `first_record_confidentiality_budget` with each `keyGame` replaced through `key_bound` for the certificates `confCertificate`. The candidate count of each `recoveryLoss` is the initial and prechallenge reveal observations of the base certificate plus the adversary's total budget. The only remaining explicit game terms are the two `collGame` terms. -/
theorem first_record_confidentiality_key_budget (b : Fin (B + 1))
    (adversary : program.Selection → RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    {post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)}
    (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post0)
    (budget : PqxdhPhase2SourceSchedulerBounds.Budget) (bounded : AdvBounded program b adversary budget)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem (env0).native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect (env0).source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (ctxFallback : ModifiedNonceAeadForgery) (qPrelude0 qPrelude1 : Nat)
    (prepareHash0 : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false)
      qPrelude0)
    (prepareHash1 : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true)
      qPrelude1)
    (small : 1 + ∑ kind, budget kind < 2 ^ 96) :
    |(𝒟[confGame setup env callbacks baseImpl kem attachedVerify primitives program b adversary false] {true}).toReal -
      (𝒟[confGame setup env callbacks baseImpl kem attachedVerify primitives program b adversary true] {true}).toReal| ≤
    (twinLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b
      (confCertificate env0 baseImpl kem program c b adversary budget bounded false) ctxFallback qPrelude0).toReal +
    (twinLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b
      (confCertificate env0 baseImpl kem program c b adversary budget bounded true) ctxFallback qPrelude1).toReal +
    (PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (confPost adversary b false)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (confPost adversary b false)
        (confCertificate env0 baseImpl kem program c b adversary budget bounded false)) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (confPost adversary b false) hmac fallback
      ordinaryFallback) +
    (PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (confPost adversary b true)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (confPost adversary b true)
        (confCertificate env0 baseImpl kem program c b adversary budget bounded true)) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (confPost adversary b true) hmac fallback
      ordinaryFallback) +
    (𝒟[collGame setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b (firstBeacon b)]
      {true}).toReal +
    (𝒟[collGame setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b (firstBeacon b)]
      {true}).toReal +
    (recoveryLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b
      (confCertificate env0 baseImpl kem program c b adversary budget bounded false) ctxFallback qPrelude0).toReal +
    (recoveryLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b
      (confCertificate env0 baseImpl kem program c b adversary budget bounded true) ctxFallback qPrelude1).toReal +
    4 * (((1 + budget (.inl .send) + 51 * (budget (.inl .raw) + budget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256) +
    4 / 2 ^ 256 := by
  have main := first_record_confidentiality_budget setup env callbacks baseImpl kem attachedVerify primitives program b adversary c
    budget bounded compatible adapter functional hmac correct fallback ordinaryFallback ctxFallback qPrelude0 qPrelude1 prepareHash0
    prepareHash1 small
  have key0 := key_real setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b
    (confCertificate env0 baseImpl kem program c b adversary budget bounded false) ctxFallback qPrelude0 prepareHash0 small
  have key1 := key_real setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b
    (confCertificate env0 baseImpl kem program c b adversary budget bounded true) ctxFallback qPrelude1 prepareHash1 small
  have budget0 : (confCertificate env0 baseImpl kem program c b adversary budget bounded false).postBudget = budget := rfl
  have budget1 : (confCertificate env0 baseImpl kem program c b adversary budget bounded true).postBudget = budget := rfl
  rw [budget0] at key0
  rw [budget1] at key1
  linarith

end KeyCorollary

end BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.keyRun_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.keyRun_le

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.live_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.live_history

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.ins_history_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.ins_history_step

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.ins_history_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.ins_history_run

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.evaluated_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.evaluated_support

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.initialFront_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.initialFront_count

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.reinstall_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.reinstall_history

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.build_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.build_history

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.true_bind_mono_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.true_bind_mono_support

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.map_mono_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.map_mono_support

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.candidates_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.candidates_length

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.candidates_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.candidates_hit

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.insKey_le_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.insKey_le_hit

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.keyRun_le_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.keyRun_le_hit

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.true_bind_le_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.true_bind_le_support

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.key_le_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.key_le_hit

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.evaluated_postBit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.evaluated_postBit

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.postBit_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.postBit_client

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.insHitRun_postBit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.insHitRun_postBit

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.hitObserve_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.hitObserve_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.hit_le_separated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.hit_le_separated

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.hitSource_reorder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.hitSource_reorder

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.separated_le_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.separated_le_source

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.recvClient_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.recvClient_length

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.canonical_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.canonical_hit

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.source_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.source_candidate

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.source_candidate_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.source_candidate_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.keyClient_uses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.keyClient_uses

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.key_bound_stop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.key_bound_stop

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.candidateCount_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.candidateCount_first

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.keyLoss_ne_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.keyLoss_ne_top

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.key_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.key_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.key_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.key_real

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.first_record_confidentiality_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.first_record_confidentiality_key

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.first_record_confidentiality_key_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound.first_record_confidentiality_key_budget
