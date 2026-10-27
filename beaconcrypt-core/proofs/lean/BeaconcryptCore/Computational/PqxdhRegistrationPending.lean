-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget
import BeaconcryptCore.Computational.PqxdhServerAuthNative

/-! The actual source pending registry allocates attempts monotonically and consumes moved response tokens on every build outcome. Arbitrary later API calls cannot resurrect an allocated consumed token. Missing future indices remain eligible for later allocation; this is not a restriction on adversarial scheduling or a cryptographic freshness premise. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationPending
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment
open PqxdhServerAuthPendingBudget
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- An allocated handle whose moved source token has been consumed. -/
def Spent (index : Nat) (state : GameState KemSK) : Prop :=
  index < state.sessions ∧ state.pending index = none

/-- Later admission allocates above every previously consumed handle. -/
theorem accept_spent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) (raw : Pqxdh.Bytes)
    (index : Nat) (state : GameState KemSK) (result : Option Nat × GameState KemSK)
    (spent : Spent index state)
    (supported : result ∈ support ((acceptOracle setup codec checks publicValue raw).run state)) :
    Spent index result.2 := by
  obtain ⟨allocated, unchanged | ⟨token, inserted⟩⟩ :=
    accept_pending setup codec checks publicValue raw state result supported
  · exact ⟨by rw [allocated]; exact Nat.lt_succ_of_lt spent.1, unchanged ▸ spent.2⟩
  · refine ⟨by rw [allocated]; exact Nat.lt_succ_of_lt spent.1, ?_⟩
    rw [inserted, Function.update_of_ne (Nat.ne_of_lt spent.1)]
    exact spent.2
/-- Any build, successful or failed, preserves every previously spent handle. -/
theorem build_spent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (index session : Nat) (payload : Option Pqxdh.Bytes)
    (state : GameState KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × GameState KemSK)
    (spent : Spent index state)
    (supported : result ∈ support ((buildOracle setup codec checks session payload).run state)) :
    Spent index result.2 := by
  obtain ⟨allocated, cleared⟩ := build_pending setup codec checks session payload state result supported
  refine ⟨allocated ▸ spent.1, ?_⟩
  rw [cleared]
  by_cases same : index = session
  · subst index; exact Function.update_self ..
  · rw [Function.update_of_ne same]; exact spent.2

/-- A reached build spends its allocated handle independently of publication success. -/
theorem build_consumes (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (index : Nat) (payload : Option Pqxdh.Bytes)
    (state : GameState KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × GameState KemSK)
    (allocated : index < state.sessions)
    (supported : result ∈ support ((buildOracle setup codec checks index payload).run state)) :
    Spent index result.2 := by
  obtain ⟨sessions, cleared⟩ := build_pending setup codec checks index payload state result supported
  exact ⟨sessions ▸ allocated, by rw [cleared]; exact Function.update_self ..⟩

/-- Every other actual capability preserves both the registry length and the missing token. -/
theorem quiet_spent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (query : ServerAuthSpec.Domain) (notAccept : ¬ IsAcceptQuery query)
    (notBuild : ∀ session payload, query ≠ .inr (.build session payload))
    (index : Nat) (state : GameState KemSK) (result : ServerAuthSpec.Range query × GameState KemSK)
    (spent : Spent index state)
    (supported : result ∈ support ((authHandler setup codec checks publicValue beaconSeed query).run state)) :
    Spent index result.2 := by
  obtain ⟨sessions, pending⟩ := handler_pending_quiet setup codec checks publicValue beaconSeed query
    notAccept notBuild state result supported
  exact ⟨sessions ▸ spent.1, pending ▸ spent.2⟩

/-- Every original API step preserves disposal of an already allocated token. -/
theorem handler_spent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (query : ServerAuthSpec.Domain) (index : Nat) (state : GameState KemSK)
    (result : ServerAuthSpec.Range query × GameState KemSK) (spent : Spent index state)
    (supported : result ∈ support ((authHandler setup codec checks publicValue beaconSeed query).run state)) :
    Spent index result.2 := by
  cases query with
  | inl coin =>
      exact quiet_spent setup codec checks publicValue beaconSeed _
        (by simp [IsAcceptQuery]) (by simp) index state result spent supported
  | inr query =>
      cases query with
      | accept raw => exact accept_spent setup codec checks publicValue raw index state result spent supported
      | build session payload => exact build_spent setup codec checks index session payload state result spent supported
      | _ =>
          exact quiet_spent setup codec checks publicValue beaconSeed _
            (by simp [IsAcceptQuery]) (by simp) index state result spent supported

/-- Arbitrary later accepts, builds, reveals and raw deliveries cannot resurrect a consumed pending handle. -/
theorem program_spent {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (program : OracleComp ServerAuthSpec α) (index : Nat) (state : GameState KemSK)
    (result : α × GameState KemSK) (spent : Spent index state)
    (supported : result ∈ support ((simulateQ (authHandler setup codec checks publicValue beaconSeed) program).run state)) :
    Spent index result.2 := by
  exact run_rel _ (fun before after => Spent index before → Spent index after)
    (fun _ => id) (fun _ _ _ first second => second ∘ first)
    (fun query before after reached valid => handler_spent setup codec checks publicValue beaconSeed
      query index before after valid reached) program state result supported spent

/-- Attempting to rebuild an absent token rejects before all source tail callbacks and leaves the complete state unchanged. -/
theorem missing_build (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (index : Nat) (payload : Option Pqxdh.Bytes) (state : GameState KemSK)
    (missing : state.pending index = none) :
    (buildOracle setup codec checks index payload).run state = pure (none, state) := by
  simp [buildOracle, missing]

/-- A consumed allocated token cannot be built a second time after any adaptive continuation, including new registrations and failed responses. -/
theorem no_rebuild {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (index : Nat) (payload replayPayload : Option Pqxdh.Bytes) (state : GameState KemSK)
    (first : Option PqxdhServerRegistrationPublication.Response × GameState KemSK)
    (allocated : index < state.sessions)
    (firstRun : first ∈ support ((buildOracle setup codec checks index payload).run state))
    (program : OracleComp ServerAuthSpec α) (last : α × GameState KemSK)
    (continued : last ∈ support ((simulateQ (authHandler setup codec checks publicValue beaconSeed) program).run first.2)) :
    (buildOracle setup codec checks index replayPayload).run last.2 = pure (none, last.2) := by
  exact missing_build setup codec checks index replayPayload last.2
    (program_spent setup codec checks publicValue beaconSeed program index first.2 last
      (build_consumes setup codec checks index payload state first allocated firstRun) continued).2

/-- The literal native builder consumes the same moved token and retains the complete primitive-family state. -/
theorem native_build_consumes (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (scalar : ScalarBytes)
    (index : Nat) (payload : Option Pqxdh.Bytes) (state : PqxdhServerAuthNative.NativeState KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × PqxdhServerAuthNative.NativeState KemSK)
    (allocated : index < state.2.sessions)
    (supported : result ∈ support ((PqxdhServerAuthNative.nativeBuild setup codec checks index payload).run state)) :
    Spent index result.2.2 := by
  apply build_consumes setup codec checks index payload state.2 (result.1, result.2.2) allocated
  apply PqxdhServerAuthNative.evaluate_support setup seed scalar _ state result
  rw [PqxdhServerAuthNative.build_native]
  exact supported

end BeaconcryptCore.Computational.PqxdhRegistrationPending

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationPending.accept_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationPending.accept_spent

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationPending.build_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationPending.build_spent

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationPending.build_consumes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationPending.build_consumes

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationPending.quiet_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationPending.quiet_spent

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationPending.handler_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationPending.handler_spent

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationPending.program_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationPending.program_spent

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationPending.missing_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationPending.missing_build

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationPending.no_rebuild' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationPending.no_rebuild

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationPending.native_build_consumes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationPending.native_build_consumes
