import BeaconcryptCore.Computational.PqxdhLaterSavedCompilerSupport
import BeaconcryptCore.Computational.PqxdhLaterChallengeMonitor

/-! Complete successful monitored prefixes ending before the challenge retain the incoming marker and full component state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeMarkerPrefix
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry PqxdhFirstRecordConfidentiality
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}

/-- If an original wrapper callback returns an unused challenge pair, its input pair was unused and the monitor preserves any incoming marker. Every original source reply is covered. -/
theorem callback_unmarked (target : RootOutput) (owner : RawCtxProtocolReveals.Owner S B)
    (number : Std.U64) (bit : Bool) (query : (AdvSpec extra S B).Domain)
    (current : PqxdhRecordConfidentialityChallenge.State) (before : InsState M P I D K A N C S B)
    (choice : Option Bool)
    (result : (AdvSpec extra S B).Range query × PqxdhRecordConfidentialityChallenge.State)
    (supported : result ∈ support ((PqxdhRecordConfidentialityChallenge.handler owner number bit query).run current))
    (unused : result.2.pair = none) :
    current.pair = none ∧ PqxdhLaterChallengeMonitor.record target owner query current (before, choice) = choice := by
  rcases query with request | ⟨left, right⟩
  · simp only [PqxdhRecordConfidentialityChallenge.handler, StateT.run, mem_support_bind_iff,
      mem_support_pure_iff] at supported
    obtain ⟨_, _, rfl⟩ := supported
    exact ⟨unused, by cases choice <;> rfl⟩
  · simp only [PqxdhRecordConfidentialityChallenge.handler, StateT.run] at supported
    split at supported
    · simp only [mem_support_pure_iff] at supported
      subst result
      refine ⟨unused, ?_⟩
      rename_i refused
      cases choice <;> simp only [PqxdhLaterChallengeMonitor.record, ite_eq_left refused]
    · simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
      obtain ⟨_, _, rfl⟩ := supported
      cases unused

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


/-- The actual optional monitored callback inherits the source bookkeeping fact on success, retaining its complete instrumented output state. Outer refusal remains outside this successful-return implication. -/
theorem query_unmarked (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (query : (AdvSpec extra S B).Domain) (current after : PqxdhRecordConfidentialityChallenge.State)
    (before : PqxdhLaterChallengeMonitor.State M P I D K A N C S B)
    (finalState : PqxdhLaterChallengeMonitor.State M P I D K A N C S B)
    (reply : (AdvSpec extra S B).Range query)
    (supported : (some (reply, after), finalState) ∈ support (runStepper
      (PqxdhLaterChallengeMonitor.handler pre application initial selector aux source writer prior parent target nonce next sender route
        read mark monitor owner number bit query) current before))
    (unused : after.pair = none) : current.pair = none ∧ finalState.2 = before.2 := by
  simp only [PqxdhLaterChallengeMonitor.handler, runStepper, OptionT.run_mk, StateT.run, support_map] at supported
  obtain ⟨outcome, actual, same⟩ := supported
  rcases outcome with ⟨_ | ⟨value, updated⟩, state⟩
  · cases same
  · cases same
    apply callback_unmarked target owner number bit query current before.1 before.2 (reply, after) _ unused
    exact PqxdhLaterSavedCompilerSupport.interpreted_support _
      ((PqxdhRecordConfidentialityChallenge.handler owner number bit query).run current) before.1 state (reply, after) actual

/-- Along any complete adaptive monitored prefix with a successful unused-wrapper result, no challenge was selected and its arbitrary incoming private marker is preserved. No source call or optional refusal is removed from the program. -/
theorem program_unmarked {Result : Type} (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (client : OracleComp (AdvSpec extra S B) Result) (current after : PqxdhRecordConfidentialityChallenge.State)
    (before finalState : PqxdhLaterChallengeMonitor.State M P I D K A N C S B) (value : Result)
    (supported : (some (value, after), finalState) ∈ support (runStepper
      (simulateQ (PqxdhLaterChallengeMonitor.handler pre application initial selector aux source writer prior parent target nonce next
        sender route read mark monitor owner number bit) client) current before))
    (unused : after.pair = none) : current.pair = none ∧ finalState.2 = before.2 := by
  induction client using OracleComp.inductionOn generalizing current before with
  | pure result =>
      simp only [simulateQ_pure, runStepper, StateT.run_pure, OptionT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact ⟨unused, rfl⟩
  | query_bind query continuation ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, runStepper_bind, mem_support_bind_iff] at supported
      obtain ⟨step, actual, later⟩ := supported
      rcases step with ⟨_ | ⟨reply, intermediate⟩, state⟩
      · simp only [mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at later
      · have tail := ih reply intermediate state later
        have first := query_unmarked pre application initial selector aux source writer prior parent target nonce next sender route read
          mark monitor owner number bit query current intermediate before state reply actual tail.1
        exact ⟨first.1, tail.2.trans first.2⟩

/-- The same prefix fact after any stateful probabilistic component interpreter, retaining its complete initial and final backend states. This is support transport, not equality of prefix probabilities under changed interpreters. -/
theorem evaluated_unmarked {Result Backend : Type}
    (impl : QueryImpl AdaptiveCtxDynamicKnownKeys.Spec (StateT Backend ProbComp))
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (client : OracleComp (AdvSpec extra S B) Result) (current after : PqxdhRecordConfidentialityChallenge.State)
    (before finalState : PqxdhLaterChallengeMonitor.State M P I D K A N C S B) (value : Result)
    (initialBackend finalBackend : Backend)
    (supported : ((some (value, after), finalState), finalBackend) ∈ support ((simulateQ impl (runStepper
      (simulateQ (PqxdhLaterChallengeMonitor.handler pre application initial selector aux source writer prior parent target nonce next
        sender route read mark monitor owner number bit) client) current before)).run initialBackend))
    (unused : after.pair = none) : current.pair = none ∧ finalState.2 = before.2 := by
  apply program_unmarked pre application initial selector aux source writer prior parent target nonce next sender route read mark monitor
    owner number bit client current after before finalState value _ unused
  apply support_simulateQ_run'_subset impl _ initialBackend
  simpa only [StateT.run'_eq, support_map, Set.mem_image] using
    (show ∃ result ∈ support ((simulateQ impl (runStepper
      (simulateQ (PqxdhLaterChallengeMonitor.handler pre application initial selector aux source writer prior parent target nonce next
        sender route read mark monitor owner number bit) client) current before)).run initialBackend),
      result.1 = (some (value, after), finalState) from ⟨_, supported, rfl⟩)

end BeaconcryptCore.Computational.PqxdhLaterChallengeMarkerPrefix

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMarkerPrefix.callback_unmarked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMarkerPrefix.callback_unmarked

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMarkerPrefix.query_unmarked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMarkerPrefix.query_unmarked

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMarkerPrefix.program_unmarked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMarkerPrefix.program_unmarked

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeMarkerPrefix.evaluated_unmarked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeMarkerPrefix.evaluated_unmarked
