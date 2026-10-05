-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeTwin

/-! The complete later-record suffix retains the original raw screening and explicitly marks selected raw openings inside unscreened finish operations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeSuffix
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry PqxdhFirstRecordConfidentiality
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) (monitor : Fin B)


open PqxdhLaterChallengeTwin (handler)

/-- The existing finish instrumentation records an actual selected raw call; no ordinary optional rejection is identified with this event. -/
def Dead (state : InsState M P I D K A N C S B) : Prop := state.2.2.2 = true

set_option backward.isDefEq.respectTransparency false in
/-- Every ordinary wrapper request executes the original full interpreter before applying its literal screen and publication observation. -/
theorem adv_run (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (query : (ConfPostSpec extra S B).Domain) (current : PqxdhRecordConfidentialityChallenge.State)
    (before : InsState M P I D K A N C S B) :
    runStepper (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
      owner number bit (.inl query)) current before =
    (fun result => (result.1.map (fun reply =>
      (PqxdhRecordConfidentialityChallenge.screen current query reply,
        PqxdhRecordConfidentialityChallenge.observe owner number current query reply)), result.2)) <$>
      ((insImpl pre application initial selector aux source writer prior (some parent) target nonce next sender route read mark monitor
        query).run).run before := by
  simp only [runStepper, handler, StateT.run, PqxdhRecordConfidentialityChallenge.handler, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, OptionT.run_map]
  exact StateT.run_map _ _ _

/-- A stable original request gives equal complete wrapper views and preserves the chosen pair. -/
theorem twin_of_stable (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (left right : Pqxdh.Bytes) (query : (ConfPostSpec extra S B).Domain)
    (current : PqxdhRecordConfidentialityChallenge.State) (paired : current.pair = some (left, right))
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option ((ConfPostSpec extra S B).Range query) × InsState M P I D K A N C S B))
    (stable : Stable left right (fun result => (result.1.map (fun reply =>
      (PqxdhRecordConfidentialityChallenge.screen current query reply,
        PqxdhRecordConfidentialityChallenge.observe owner number current query reply)), result.2)) work) :
    Twin left right (fun a b => a = b ∧ ∀ (reply : (AdvSpec extra S B).Range (.inl query)) after,
      a.1 = some (reply, after) → after.pair = some (left, right))
      (fun result => Dead result.2) (fun result => Dead result.2)
      ((fun result => (result.1.map (fun reply =>
        (PqxdhRecordConfidentialityChallenge.screen current query reply,
          PqxdhRecordConfidentialityChallenge.observe owner number current query reply)), result.2)) <$> work)
      ((fun result => (result.1.map (fun reply =>
        (PqxdhRecordConfidentialityChallenge.screen current query reply,
          PqxdhRecordConfidentialityChallenge.observe owner number current query reply)), result.2)) <$> work) := by
  refine twin_map left right stable _ _ (fun _ _ same => ⟨same, ?_⟩)
    (fun _ impossible => impossible.elim) (fun _ impossible => impossible.elim)
  intro reply after returned
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at returned
  obtain ⟨answer, _, _, rfl⟩ := returned
  exact paired

set_option backward.isDefEq.respectTransparency false in
/-- After an accepted challenge, every literal request retains equal screened views until an actual selected finish opening raises the existing flag. The retained parent, arbitrary later receive counter and all competing publication observations remain in the state. -/
theorem step_twin (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (left right : Pqxdh.Bytes) (query : (AdvSpec extra S B).Domain)
    (current : PqxdhRecordConfidentialityChallenge.State) (before : InsState M P I D K A N C S B)
    (paired : current.pair = some (left, right)) (alive : ¬ Dead before) :
    Twin left right (fun a b => a = b ∧ ∀ reply after, a.1 = some (reply, after) → after.pair = some (left, right))
      (fun result => Dead result.2) (fun result => Dead result.2)
      (runStepper (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
        owner number false query) current before)
      (runStepper (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
        owner number true query) current before) := by
  rcases query with request | ⟨x0, x1⟩
  · rw [adv_run pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
      owner number false request current before,
      adv_run pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
      owner number true request current before]
    rcases request with (record | ext) | ⟨index, raw⟩
    · refine twin_of_stable owner number left right _ current paired _ ?_
      simp only [insImpl, OptionT.run_mk, StateT.run]
      apply stable_map
      rcases record with family | reveal
      · simp only [RawCtxSelectedFamilyLiveCompiler.impl, OptionT.run_mk]
        apply stable_map
        by_cases receive : FamilyReceive family
        · rcases family with ⟨index, (⟨plaintext, kid⟩ | raw)⟩ | (⟨index, (plaintext | raw)⟩ | request)
          · exact absurd receive id
          · rw [RawCtxSelectedFamilyCompiler.family_cases]
            apply stable_map
            refine server_raw_stable left right source writer prior (some parent) target nonce next sender route read raw _ _ ?_
            intro state d0 d1 related
            simp only [Function.comp_apply, Option.map_some, RawCtxSelectedFamilyLiveCompiler.publish, traceRecord_server_receive,
              PqxdhRecordConfidentialityChallenge.screen, screen_server_receive, PqxdhRecordConfidentialityChallenge.observe,
              PqxdhRecordConfidentialityChallenge.publications, RawCtxPublishedRecords.record, paired]
            rw [suppress_rel left right d0 d1 related]
          · exact absurd receive id
          · rw [RawCtxSelectedFamilyCompiler.family_cases]
            apply stable_map
            refine beacon_raw_stable left right source writer prior (some parent) target nonce next read raw _ _ ?_
            intro state d0 d1 related
            simp only [Function.comp_apply, Option.map_some, RawCtxSelectedFamilyLiveCompiler.publish, traceRecord_beacon_receive,
              PqxdhRecordConfidentialityChallenge.screen, screen_beacon_receive, PqxdhRecordConfidentialityChallenge.observe,
              PqxdhRecordConfidentialityChallenge.publications, RawCtxPublishedRecords.record, paired]
            rw [suppress_rel left right d0 d1 related]
          · exact absurd receive id
        · exact stable_rawfree left right _ _
            (family_raw source writer prior (some parent) target nonce next sender route read family receive _)
      · exact stable_pure left right _ _
    · refine twin_of_stable owner number left right _ current paired _ ?_
      simp only [insImpl, OptionT.run_mk, StateT.run]
      refine stable_rawfree left right _ _ ?_
      rw [isQueryBoundP_map_iff]
      exact raw_of_target _ (PqxdhSelectedInitialOwnerCompiler.external_no_open pre application initial selector aux _ _)
    · have flag : before.2.2.2 = false := Bool.eq_false_iff.mpr alive
      simp only [insImpl, OptionT.run_mk, StateT.run, Functor.map_map, flag]
      refine twin_map left right (twin_markRaw left right _ false) _ _ ?_ ?_ ?_
      · rintro a _ rfl
        refine ⟨rfl, ?_⟩
        intro reply after returned
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at returned
        rw [← returned.2]
        exact paired
      · intro a flagged; exact flagged
      · intro a flagged; exact flagged
  · simp only [runStepper, handler, PqxdhRecordConfidentialityChallenge.handler, StateT.run, paired,
      Option.isSome_some, true_or, ite_true, simulateQ_pure, OptionT.run_pure]
    refine Twin.pure ⟨rfl, ?_⟩
    intro reply after returned
    simp only [Option.some.injEq, Prod.mk.injEq] at returned
    rw [← returned.2]
    exact paired

/-- The existing selected-finish-opening flag remains raised through every complete retained-parent Post callback. -/
theorem ins_flag (query : (ConfPostSpec extra S B).Domain) (before : InsState M P I D K A N C S B)
    (raised : Dead before) (result : Option ((ConfPostSpec extra S B).Range query) × InsState M P I D K A N C S B)
    (supported : result ∈ support (((insImpl pre application initial selector aux source writer prior (some parent) target nonce next
      sender route read mark monitor query).run).run before)) : Dead result.2 := by
  rcases query with (record | ext) | ⟨index, raw⟩
  · simp only [insImpl, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨value, _, rfl⟩ := supported
    exact raised
  · simp only [insImpl, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨value, _, rfl⟩ := supported
    exact raised
  · simp only [Dead] at raised ⊢
    simp only [insImpl, OptionT.run_mk, StateT.run, support_map, Set.mem_image, raised] at supported
    obtain ⟨value, member, rfl⟩ := supported
    exact markRaw_sticky _ value member

/-- Actual optional Post execution preserves the flag through every continuation, including the full state returned on the first outer refusal. -/
theorem program_flag {Result : Type} (work : OracleComp (ConfPostSpec extra S B) Result)
    (before : InsState M P I D K A N C S B) (raised : Dead before)
    (result : Option Result × InsState M P I D K A N C S B)
    (supported : result ∈ support (((simulateQ
      (insImpl pre application initial selector aux source writer prior (some parent) target nonce next sender route read mark monitor)
      work).run).run before)) : Dead result.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      rw [supported]
      exact raised
  | query_bind query continuation ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind,
        mem_support_bind_iff] at supported
      obtain ⟨step, member, supported⟩ := supported
      have kept := ins_flag pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
        query before raised step member
      rcases step with ⟨_ | reply, after⟩
      · rw [supported]
        exact kept
      · exact ih reply after kept supported

/-- The literal wrapper preserves an already reached selected-finish-opening event on either challenge bit, including refused challenges. -/
theorem query_flag (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (query : (AdvSpec extra S B).Domain) (current : PqxdhRecordConfidentialityChallenge.State)
    (before : InsState M P I D K A N C S B) (raised : Dead before)
    (result : Option ((AdvSpec extra S B).Range query × PqxdhRecordConfidentialityChallenge.State) × InsState M P I D K A N C S B)
    (supported : result ∈ support (runStepper (handler pre application initial selector aux source writer prior parent target nonce next
      sender route read mark monitor owner number bit query) current before)) : Dead result.2 := by
  exact program_flag pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
    ((PqxdhRecordConfidentialityChallenge.handler owner number bit query).run current) before raised result supported

/-- Every complete adaptive continuation after the accepted challenge retains equal full views until a selected raw opening inside a finish. There is no bound on the continuation's schedule or assumption about successful replies. -/
theorem after_twin {Result : Type} (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (left right : Pqxdh.Bytes) (work : OracleComp (AdvSpec extra S B) Result)
    (current : PqxdhRecordConfidentialityChallenge.State) (before : InsState M P I D K A N C S B)
    (paired : current.pair = some (left, right)) (alive : ¬ Dead before) :
    Twin left right (fun a b => a = b) (fun result => Dead result.2) (fun result => Dead result.2)
      (runStepper (simulateQ (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark
        monitor owner number false) work) current before)
      (runStepper (simulateQ (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark
        monitor owner number true) work) current before) := by
  exact twin_run_inv left right _ _ Dead (fun current => current.pair = some (left, right))
    (step_twin pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
      owner number left right)
    (query_flag pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor owner number false)
    (query_flag pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor owner number true)
    work current before paired alive

/-- The literal selected challenge and its entire reply-dependent continuation are twin, retaining the full wrapper and private state. The operational input condition belongs to this reached request; an earlier or later matching counter is not substituted for it. -/
theorem challenge_then_twin {Result : Type} (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (left right : Pqxdh.Bytes) (equal : left.length = right.length)
    (continuation : Option RawCtxSourceSend.Encrypted → OracleComp (AdvSpec extra S B) Result)
    (current : PqxdhRecordConfidentialityChallenge.State) (unused : current.pair = none)
    (before : InsState M P I D K A N C S B)
    (selected : ∀ kernel, RawCtxGenericRoleFamily.selectedKernel owner before.1.1.roles.1 = some kernel →
      RawCtxSelectedPendingCut.requestAddress kernel.send_chain = RawCtxSelectedParentPrivatePatch.targetAddress target)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ parent.address) :
    Twin left right (fun a b => a = b) (fun result => Dead result.2) (fun result => Dead result.2)
      (runStepper (simulateQ (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark
        monitor owner number false) ((liftM ((AdvSpec extra S B).query (.inr (left, right)))) >>= continuation)) current before)
      (runStepper (simulateQ (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark
        monitor owner number true) ((liftM ((AdvSpec extra S B).query (.inr (left, right)))) >>= continuation)) current before) := by
  rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query, runStepper_bind, runStepper_bind]
  refine twin_bind left right
    (PqxdhLaterChallengeTwin.challenge_twin pre application initial selector aux source writer prior parent target nonce next sender route read
      mark monitor owner number left right equal current unused before selected separate) ?_
    (fun _ impossible => impossible.elim) (fun _ impossible => impossible.elim)
  rintro result _ ⟨rfl, paired⟩
  rcases result with ⟨_ | ⟨reply, current'⟩, after⟩
  · exact Twin.pure rfl
  · by_cases raised : Dead after
    · apply Twin.dead
      · exact runStepper_dead _ Dead
          (query_flag pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor owner number false)
          (continuation reply) current' after raised
      · exact runStepper_dead _ Dead
          (query_flag pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor owner number true)
          (continuation reply) current' after raised
    · exact after_twin pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
        owner number left right (continuation reply) current' after (paired reply current' rfl) raised

/-- The original target decision restricted to the explicit complement of the selected-finish-opening flag. This is an observed event; the executed callbacks are unchanged. -/
noncomputable def observed (number : Std.U64)
    (result : Option (Bool × PqxdhRecordConfidentialityChallenge.State) × InsState M P I D K A N C S B) : Bool :=
  if result.2.2.2.2 then false else result.1.elim false (PqxdhRecordConfidentialityChallenge.output number)

/-- The exact selected challenge followed by its complete adaptive continuation and the restricted original target observation. -/
noncomputable def selectedClient (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (left right : Pqxdh.Bytes)
    (continuation : Option RawCtxSourceSend.Encrypted → OracleComp (AdvSpec extra S B) Bool)
    (current : PqxdhRecordConfidentialityChallenge.State) (before : InsState M P I D K A N C S B) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool :=
  observed number <$> runStepper
    (simulateQ (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
      owner number bit) ((liftM ((AdvSpec extra S B).query (.inr (left, right)))) >>= continuation)) current before

/-- In the existing ordinary random view, the actual selected challenge and arbitrary continuation have identical restricted target probability for both plaintexts. This statement retains the reached input and parent-separation conditions and the explicit finish-opening event restriction. -/
theorem random_challenge (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (left right : Pqxdh.Bytes) (equal : left.length = right.length)
    (continuation : Option RawCtxSourceSend.Encrypted → OracleComp (AdvSpec extra S B) Bool)
    (current : PqxdhRecordConfidentialityChallenge.State) (unused : current.pair = none)
    (before : InsState M P I D K A N C S B)
    (selected : ∀ kernel, RawCtxGenericRoleFamily.selectedKernel owner before.1.1.roles.1 = some kernel →
      RawCtxSelectedPendingCut.requestAddress kernel.send_chain = RawCtxSelectedParentPrivatePatch.targetAddress target)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ parent.address) :
    𝒟[AdaptiveCtxPrivacyGuard.randomView (RawCtxUniversalDecoder.decoder read)
      (AdaptiveCtxDynamicKnownKeys.decisionClient source.crypto
        (selectedClient pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
          owner number false left right continuation current before))] {true} =
    𝒟[AdaptiveCtxPrivacyGuard.randomView (RawCtxUniversalDecoder.decoder read)
      (AdaptiveCtxDynamicKnownKeys.decisionClient source.crypto
        (selectedClient pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
          owner number true left right continuation current before))] {true} := by
  apply randomView_twin left right _ source.crypto equal
  refine twin_map left right
    (challenge_then_twin pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
      owner number left right equal continuation current unused before selected separate) _ _
    (fun _ _ same => congrArg _ same) ?_ ?_
  all_goals intro result flagged
  all_goals simp only [observed, show result.2.2.2.2 = true from flagged, ite_true]

end BeaconcryptCore.Computational.PqxdhLaterChallengeSuffix

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSuffix.adv_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSuffix.adv_run
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSuffix.twin_of_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSuffix.twin_of_stable
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSuffix.step_twin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSuffix.step_twin
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSuffix.ins_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSuffix.ins_flag
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSuffix.program_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSuffix.program_flag
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSuffix.query_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSuffix.query_flag
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSuffix.after_twin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSuffix.after_twin
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSuffix.challenge_then_twin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSuffix.challenge_then_twin
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSuffix.random_challenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSuffix.random_challenge
