-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeSuffix

/-! Private request-time designation for the unchanged later challenge. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor
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


/-- The selected input condition is read from this exact request state, without assuming that a counter or final marker identifies it. -/
def Selected (target : RootOutput) (owner : RawCtxProtocolReveals.Owner S B)
    (state : InsState M P I D K A N C S B) : Prop :=
  ∀ kernel, RawCtxGenericRoleFamily.selectedKernel owner state.1.1.roles.1 = some kernel →
    RawCtxSelectedPendingCut.requestAddress kernel.send_chain = RawCtxSelectedParentPrivatePatch.targetAddress target

abbrev State (M P I D K A N C : Type) (S B : Nat) := InsState M P I D K A N C S B × Option Bool

/-- The private annotation records the actual admitted challenge's input condition and cannot be overwritten. It neither admits nor refuses a source request. -/
noncomputable def record (target : RootOutput) (owner : RawCtxProtocolReveals.Owner S B)
    (query : (AdvSpec extra S B).Domain) (current : PqxdhRecordConfidentialityChallenge.State)
    (before : State M P I D K A N C S B) : Option Bool := by
  classical
  exact match before.2 with
  | some value => some value
  | none => match query with
    | .inl _ => none
    | .inr (left, right) =>
        if current.pair.isSome ∨ left.length ≠ right.length then none
        else some (decide (Selected target owner before.1))

/-- The existing full callback executes before its private annotation is returned, including completed work on an outer-refusal branch. -/
noncomputable def handler (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool) :
    QueryImpl (AdvSpec extra S B) (Stepper PqxdhRecordConfidentialityChallenge.State (State M P I D K A N C S B)) :=
  fun query current => OptionT.mk fun before =>
    (fun result => (result.1, (result.2, record target owner query current before))) <$>
      runStepper (PqxdhLaterChallengeTwin.handler pre application initial selector aux source writer prior parent target nonce next sender route
        read mark monitor owner number bit query) current before.1

/-- Erasing only the new private marker recovers one complete original callback, its optional reply, wrapper state and original full private state. -/
theorem query_source (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (query : (AdvSpec extra S B).Domain) (current : PqxdhRecordConfidentialityChallenge.State)
    (before : State M P I D K A N C S B) :
    Prod.map id Prod.fst <$> runStepper (handler pre application initial selector aux source writer prior parent target nonce next sender route
      read mark monitor owner number bit query) current before =
    runStepper (PqxdhLaterChallengeTwin.handler pre application initial selector aux source writer prior parent target nonce next sender route
      read mark monitor owner number bit query) current before.1 := by
  simp only [handler, runStepper, StateT.run, OptionT.run_mk, Functor.map_map]
  exact id_map _

/-- The complete adaptive program erases to the original execution, including the full poststate on refusal. -/
theorem program_source {Result : Type} (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (work : OracleComp (AdvSpec extra S B) Result) (current : PqxdhRecordConfidentialityChallenge.State)
    (before : State M P I D K A N C S B) :
    Prod.map id Prod.fst <$> runStepper (simulateQ (handler pre application initial selector aux source writer prior parent target nonce next sender
      route read mark monitor owner number bit) work) current before =
    runStepper (simulateQ (PqxdhLaterChallengeTwin.handler pre application initial selector aux source writer prior parent target nonce next sender
      route read mark monitor owner number bit) work) current before.1 := by
  induction work using OracleComp.inductionOn generalizing current before with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, runStepper_bind, map_bind]
    rw [← query_source pre application initial selector aux source writer prior parent target nonce _ sender route read mark monitor
      owner number bit query current before, bind_map_left]
    congr 1
    funext result
    rcases result with ⟨_ | ⟨reply, current'⟩, after⟩
    · rfl
    · exact ih reply current' after

/-- Once recorded, the private request marker is constant through the entire original adaptive continuation. -/
theorem recorded_program {Result : Type} (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit value : Bool)
    (work : OracleComp (AdvSpec extra S B) Result) (current : PqxdhRecordConfidentialityChallenge.State)
    (before : InsState M P I D K A N C S B) :
    runStepper (simulateQ (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark
      monitor owner number bit) work) current (before, some value) =
    (fun result => (result.1, (result.2, some value))) <$>
      runStepper (simulateQ (PqxdhLaterChallengeTwin.handler pre application initial selector aux source writer prior parent target nonce next
        sender route read mark monitor owner number bit) work) current before := by
  induction work using OracleComp.inductionOn generalizing current before with
  | pure result => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, runStepper_bind, map_bind]
    change ((fun result => (result.1, (result.2, some value))) <$>
      runStepper (PqxdhLaterChallengeTwin.handler pre application initial selector aux source writer prior parent target nonce _ sender route
        read mark monitor owner number bit query) current before) >>= _ = _
    rw [bind_map_left]
    congr 1
    funext result
    rcases result with ⟨_ | ⟨reply, current'⟩, after⟩
    · rfl
    · exact ih reply current' after

/-- A source-admitted challenge records its exact pre-request input condition after executing the full original callback. -/
theorem admitted_query (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (left right : Pqxdh.Bytes) (equal : left.length = right.length)
    (current : PqxdhRecordConfidentialityChallenge.State) (unused : current.pair = none)
    (before : InsState M P I D K A N C S B) :
    runStepper (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
      owner number bit (.inr (left, right))) current (before, none) =
    (fun result => (result.1, (result.2, some (@decide (Selected target owner before) (Classical.propDecidable _))))) <$>
      runStepper (PqxdhLaterChallengeTwin.handler pre application initial selector aux source writer prior parent target nonce next sender route
        read mark monitor owner number bit (.inr (left, right))) current before := by
  simp only [handler, runStepper, StateT.run, OptionT.run_mk, record, unused, Option.isSome_none, Bool.false_eq_true,
    equal, ne_eq, not_true_eq_false, or_self, ite_false]

/-- The request-time marker is retained by the complete reply-dependent suffix, including native failure and outer component refusal. -/
theorem admitted_program {Result : Type} (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (left right : Pqxdh.Bytes) (equal : left.length = right.length)
    (continuation : Option RawCtxSourceSend.Encrypted → OracleComp (AdvSpec extra S B) Result)
    (current : PqxdhRecordConfidentialityChallenge.State) (unused : current.pair = none)
    (before : InsState M P I D K A N C S B) :
    runStepper (simulateQ (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
      owner number bit) ((liftM ((AdvSpec extra S B).query (.inr (left, right)))) >>= continuation)) current (before, none) =
    (fun result => (result.1, (result.2, some (@decide (Selected target owner before) (Classical.propDecidable _))))) <$>
      runStepper (simulateQ (PqxdhLaterChallengeTwin.handler pre application initial selector aux source writer prior parent target nonce next sender
        route read mark monitor owner number bit) ((liftM ((AdvSpec extra S B).query (.inr (left, right)))) >>= continuation)) current before := by
  rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query, runStepper_bind, runStepper_bind,
    admitted_query pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
      owner number bit left right equal current unused before, bind_map_left, map_bind]
  congr 1
  funext result
  rcases result with ⟨_ | ⟨reply, current'⟩, after⟩
  · rfl
  · exact recorded_program pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
      owner number bit _ (continuation reply) current' after

/-- Only the private failed designation or the actual selected finish-opening event restricts the final observation. Neither event changes source execution. -/
def Dead (state : State M P I D K A N C S B) : Prop :=
  state.2 = some false ∨ PqxdhLaterChallengeSuffix.Dead state.1

/-- An admitted challenge is adaptively twin with its complete suffix. The actual source request determines designation; it is not an admission premise. -/
theorem admitted_pre {Result : Type} (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (left right : Pqxdh.Bytes) (equal : left.length = right.length)
    (continuation : Option RawCtxSourceSend.Encrypted → OracleComp (AdvSpec extra S B) Result)
    (current : PqxdhRecordConfidentialityChallenge.State) (unused : current.pair = none)
    (before : InsState M P I D K A N C S B)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ parent.address) :
    Pre (fun a b => a = b) (fun result => Dead result.2) (fun result => Dead result.2)
      (runStepper (simulateQ (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
        owner number false) ((liftM ((AdvSpec extra S B).query (.inr (left, right)))) >>= continuation)) current (before, none))
      (runStepper (simulateQ (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
        owner number true) ((liftM ((AdvSpec extra S B).query (.inr (left, right)))) >>= continuation)) current (before, none)) := by
  classical
  rw [admitted_program pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
    owner number false left right equal continuation current unused before,
    admitted_program pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
    owner number true left right equal continuation current unused before]
  by_cases selected : Selected target owner before
  · apply Pre.switch left right equal
    refine twin_map left right
      (PqxdhLaterChallengeSuffix.challenge_then_twin pre application initial selector aux source writer prior parent target nonce next sender route
        read mark monitor owner number left right equal continuation current unused before selected separate) _ _
      (fun _ _ same => by cases same; rfl) (fun _ raised => Or.inr raised) (fun _ raised => Or.inr raised)
  · apply Pre.dead
    all_goals intro result supported
    all_goals rcases (by simpa only [support_map, Set.mem_image] using supported) with ⟨inner, _, rfl⟩
    all_goals exact Or.inl (by simp only [decide_eq_false selected])

/-- Before the challenge, every ordinary request uses the same actual callback in both worlds and leaves the private designation unset. -/
theorem ordinary_query (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (query : (ConfPostSpec extra S B).Domain) (current : PqxdhRecordConfidentialityChallenge.State)
    (before : InsState M P I D K A N C S B) :
    runStepper (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
      owner number bit (.inl query)) current (before, none) =
    (fun result => (result.1, (result.2, none))) <$>
      runStepper (PqxdhLaterChallengeTwin.handler pre application initial selector aux source writer prior parent target nonce next sender route
        read mark monitor owner number false (.inl query)) current before := by
  rfl

/-- Ordinary replies preserve the wrapper's challenge pair and cannot create a request designation. All original state effects still occur. -/
theorem ordinary_normal (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (query : (ConfPostSpec extra S B).Domain) (current after : PqxdhRecordConfidentialityChallenge.State)
    (before : InsState M P I D K A N C S B) (finalState : State M P I D K A N C S B)
    (reply : (ConfPostSpec extra S B).Range query)
    (supported : (some (reply, after), finalState) ∈ support (runStepper
      (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
        owner number bit (.inl query)) current (before, none))) :
    after.pair = current.pair ∧ finalState.2 = none := by
  rw [ordinary_query, PqxdhLaterChallengeSuffix.adv_run, Functor.map_map, support_map] at supported
  obtain ⟨⟨outcome, state⟩, _, same⟩ := supported
  cases outcome with
  | none => cases same
  | some value =>
    cases same
    exact ⟨rfl, rfl⟩

/-- A malformed unequal-length challenge keeps the original immediate rejection and does not set the private marker. -/
theorem unequal_query (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (left right : Pqxdh.Bytes) (unequal : left.length ≠ right.length)
    (current : PqxdhRecordConfidentialityChallenge.State) (before : InsState M P I D K A N C S B) :
    runStepper (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
      owner number bit (.inr (left, right))) current (before, none) = pure (some (none, current), (before, none)) := by
  simp only [handler, record, runStepper, StateT.run, OptionT.run_mk,
    PqxdhLaterChallengeTwin.handler, PqxdhRecordConfidentialityChallenge.handler]
  simp only [ite_eq_left (Or.inr unequal), simulateQ_pure]
  rfl

/-- Every original adaptive adversary is identical until its chosen challenge and twin afterwards, restricted only by the two explicit private events. No selected-request condition is supplied by the caller. -/
theorem program_pre {Result : Type} (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (work : OracleComp (AdvSpec extra S B) Result) (current : PqxdhRecordConfidentialityChallenge.State)
    (unused : current.pair = none) (before : InsState M P I D K A N C S B)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ parent.address) :
    Pre (fun a b => a = b) (fun result => Dead result.2) (fun result => Dead result.2)
      (runStepper (simulateQ (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
        owner number false) work) current (before, none))
      (runStepper (simulateQ (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
        owner number true) work) current (before, none)) := by
  induction work using OracleComp.inductionOn generalizing current before with
  | pure value => exact Pre.pure rfl
  | query_bind query next ih =>
    cases query with
    | inl query =>
      rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query, runStepper_bind, runStepper_bind,
        ordinary_query, ordinary_query]
      apply pre_bind_refl
      intro result supported
      rcases result with ⟨_ | ⟨reply, current'⟩, ⟨after, choice⟩⟩
      · exact Pre.pure rfl
      · obtain ⟨paired, same⟩ := ordinary_normal pre application initial selector aux source writer prior parent target nonce _ sender route
          read mark monitor owner number false query current current' before (after, choice) reply (by rwa [ordinary_query])
        cases same
        exact ih reply current' (paired.trans unused) after
    | inr pair =>
      rcases pair with ⟨left, right⟩
      by_cases equal : left.length = right.length
      · exact admitted_pre pre application initial selector aux source writer prior parent target nonce _ sender route read mark monitor
          owner number left right equal next current unused before separate
      · rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query, runStepper_bind, runStepper_bind,
          unequal_query pre application initial selector aux source writer prior parent target nonce _ sender route read mark monitor
            owner number false left right equal current before,
          unequal_query pre application initial selector aux source writer prior parent target nonce _ sender route read mark monitor
            owner number true left right equal current before, pure_bind, pure_bind]
        exact ih none current unused before

/-- The original final target decision restricted to the explicit designation and finish-opening events. This terminal observation does not alter the source program. -/
noncomputable def observed (number : Std.U64)
    (result : Option (Bool × PqxdhRecordConfidentialityChallenge.State) × State M P I D K A N C S B) : Bool := by
  classical
  exact if Dead result.2 then false else result.1.elim false (PqxdhRecordConfidentialityChallenge.output number)

/-- The unchanged complete adaptive adversary, from the literal initial challenge wrapper, with private request designation and terminal event restriction. -/
noncomputable def client (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (work : OracleComp (AdvSpec extra S B) Bool) (before : InsState M P I D K A N C S B) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool :=
  observed number <$> runStepper (simulateQ
    (handler pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor owner number bit)
    work) PqxdhRecordConfidentialityChallenge.initial (before, none)

/-- The monitored client preserves every complete query budget of the original adaptive program; refusal and dead-event branches retain all executed work. -/
theorem client_budget {Budget : Type} (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (work : OracleComp (AdvSpec extra S B) Bool) (before : InsState M P I D K A N C S B)
    (available : Budget) (allowed : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Budget → Prop)
    (cost : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Budget → Budget) :
    (client pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
      owner number bit work before).IsQueryBound available allowed cost ↔
    (runStepper (simulateQ (PqxdhLaterChallengeTwin.handler pre application initial selector aux source writer prior parent target nonce next sender
      route read mark monitor owner number bit) work) PqxdhRecordConfidentialityChallenge.initial before).IsQueryBound available allowed cost := by
  rw [← program_source pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
    owner number bit work PqxdhRecordConfidentialityChallenge.initial (before, none)]
  simp only [client, isQueryBound_map_iff]

/-- The actual full adaptive client has equal restricted target probability in both ordinary random worlds. Source designation is recorded operationally; only the separately charged parent-address equality remains explicit here. -/
theorem random_client (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (work : OracleComp (AdvSpec extra S B) Bool) (before : InsState M P I D K A N C S B)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ parent.address) :
    𝒟[AdaptiveCtxPrivacyGuard.randomView (RawCtxUniversalDecoder.decoder read)
      (AdaptiveCtxDynamicKnownKeys.decisionClient source.crypto
        (client pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
          owner number false work before))] {true} =
    𝒟[AdaptiveCtxPrivacyGuard.randomView (RawCtxUniversalDecoder.decoder read)
      (AdaptiveCtxDynamicKnownKeys.decisionClient source.crypto
        (client pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
          owner number true work before))] {true} := by
  apply randomView_pre
  exact pre_map
    (program_pre pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
      owner number work PqxdhRecordConfidentialityChallenge.initial rfl before separate)
    _ _ (fun _ _ same => congrArg _ same)
    (fun _ dead => by simp only [observed, ite_eq_left dead])
    (fun _ dead => by simp only [observed, ite_eq_left dead])

end BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.query_source

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.program_source

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.recorded_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.recorded_program

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.admitted_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.admitted_query

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.admitted_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.admitted_program

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.admitted_pre' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.admitted_pre

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.ordinary_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.ordinary_query

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.ordinary_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.ordinary_normal

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.unequal_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.unequal_query

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.program_pre' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.program_pre

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.client_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.client_budget

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.random_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor.random_client
