-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptPreservation

/-! The complete actual one-Server/many-Beacon adaptive schedule derives its immutable constructor and issued-attempt history from source execution. All current-field reveals, failed writes and raw accept/finish replies are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptSchedule
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointAttemptLedger PqxdhRegistrationJointAttemptInvariant
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- Every actual source command preserves its literal constructor receipts and exact signing-attempt history, with no restriction on accepted candidates, compromise, failure or schedule order. -/
theorem query_invariant (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (identityIndex : Nat)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (state : State KemSK)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × State KemSK)
    (valid : Invariant setup state)
    (supported : result ∈ support ((handler setup codec checks seed identityIndex query).run state)) :
    Invariant setup result.2 := by
  rcases query with (coin | request) | read
  case inl.inr =>
    cases request
    case create pin keyId =>
      simp only [handler, create, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨material, _, rfl⟩ := supported
      exact created_invariant setup pin keyId state material valid
    case bundle address => exact bundle_invariant setup codec address state result valid supported
    all_goals
      simp only [handler, PqxdhRegistrationJointAttemptLedger.lift, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨reached, member, rfl⟩ := supported
      first
      | exact PqxdhRegistrationJointAttemptPreservation.accept setup codec checks seed identityIndex _ state reached valid member
      | exact PqxdhRegistrationJointAttemptPreservation.finish setup codec _ _ state reached valid member
      | exact PqxdhRegistrationJointAttemptPreservation.shared setup _ state reached valid member
  case inl.inl =>
    simp only [handler, PqxdhRegistrationJointAttemptLedger.lift, PqxdhRegistrationJointServerSchedule.source,
      PqxdhRegistrationJointRevealSchedule.source, PqxdhRegistrationJointSchedule.handler,
      StateT.run, StateT.lift, bind_pure_comp, Functor.map_map, support_map, Set.mem_image] at supported
    obtain ⟨_, _, rfl⟩ := supported
    exact valid
  case inr =>
    simp only [handler, PqxdhRegistrationJointAttemptLedger.lift, PqxdhRegistrationJointServerSchedule.source,
      PqxdhRegistrationJointRevealSchedule.source, StateT.run, map_pure, mem_support_pure_iff] at supported
    subst result
    exact PqxdhRegistrationJointAttemptPreservation.read setup read state valid

/-- Every finite adaptive source schedule retains the exact constructor/attempt invariant, including arbitrary interleaved creations, raw deliveries, retries and current-field disclosures. -/
theorem program_invariant (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (identityIndex : Nat)
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (state : State KemSK)
    (result : Result × State KemSK) (valid : Invariant setup state)
    (supported : result ∈ support ((simulateQ (handler setup codec checks seed identityIndex) work).run state)) :
    Invariant setup result.2 :=
  (run_rel (handler setup codec checks seed identityIndex) (fun before after => Invariant setup before → Invariant setup after)
    (fun _ previous => previous) (fun _ _ _ first second previous => second (first previous))
    (fun query before after member previous => query_invariant setup codec checks seed identityIndex query before after previous member)
    work state result supported) valid

end BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptSchedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptSchedule.query_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptSchedule.query_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptSchedule.program_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptSchedule.program_invariant
