-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconInitExecutor
import BeaconcryptCore.Computational.RegistrationWorldSigning

/-! Both outgoing Beacon hashes and its ML signing attempt use the same World cache and signing history as records and incoming authentication. The Ed backend retains its complete independent state and records every actual optional reply before its native continuation. World interpretation changes only instrumentation under the exact projection below; no desired simulation or history-preservation premise is supplied. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationBeaconInitShared

open RegistrationBeaconInitExecutor (Spec EdSpec)
open RegistrationSigningShared (SignReply)

structure EdReceipt where
  request : registration.Ed25519SigningRequest
  reply : SignReply

abbrev State (Auxiliary : Type) := Auxiliary × (List EdReceipt × RegistrationSigningShared.State)
abbrev WorldState (n : Nat) (Auxiliary : Type) := RegistrationWorldSigning.State n × (Auxiliary × List EdReceipt)

def project {n : Nat} {Auxiliary : Type} (state : WorldState n Auxiliary) : State Auxiliary :=
  (state.2.1, (state.2.2, RegistrationWorldSigning.project state.1))

def implementation {Auxiliary : Type} (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (ed : QueryImpl EdSpec (StateT Auxiliary ProbComp)) : QueryImpl Spec (StateT (State Auxiliary) ProbComp)
  | .inl request => fun state =>
      (fun result => (result.1, (state.1, (state.2.1, result.2)))) <$>
        (RegistrationSigningShared.implementation sign request).run state.2.2
  | .inr request => fun state =>
      (fun result => (result.1, (result.2, (state.2.1 ++ [⟨request, result.1⟩], state.2.2)))) <$>
        (ed request).run state.1

noncomputable def worldImplementation {n : Nat} {Auxiliary : Type}
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (ed : QueryImpl EdSpec (StateT Auxiliary ProbComp)) : QueryImpl Spec (StateT (WorldState n Auxiliary) ProbComp)
  | .inl request => fun state =>
      (fun result => (result.1, (result.2, state.2))) <$>
        (RegistrationWorldSigning.outgoing sign request).run state.1
  | .inr request => fun state =>
      (fun result => (result.1.1,
        ((result.2, state.1.2), (result.1.2, state.2.2 ++ [⟨request, result.1.1⟩])))) <$>
          (PqxdhRecordLiftWorld.sampled ((ed request).run state.2.1)).run state.1.1

theorem query_project {n : Nat} {Auxiliary : Type}
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (ed : QueryImpl EdSpec (StateT Auxiliary ProbComp)) (query : Spec.Domain) (state : WorldState n Auxiliary) :
    Prod.map id project <$> (worldImplementation sign ed query).run state =
      (implementation sign ed query).run (project state) := by
  cases query with
  | inl request =>
      have same := congrArg (fun work => (fun result => (result.1, (state.2.1, (state.2.2, result.2)))) <$> work)
        (RegistrationWorldSigning.outgoing_project sign request state.1)
      simpa only [worldImplementation, implementation, project, StateT.run, Functor.map_map, Prod.map, id_eq] using same
  | inr request =>
      have same := congrArg (fun work => (fun result => (result.1,
        (result.2, (state.2.2 ++ [EdReceipt.mk request result.1], RegistrationWorldSigning.project state.1)))) <$> work)
          (PqxdhRecordLiftWorld.countCoin_forget ((ed request).run state.2.1) state.1.1.primitive.1.uniform)
      simpa only [worldImplementation, implementation, project, RegistrationWorldSigning.project,
        PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, Functor.map_map, Prod.map, id_eq] using same

theorem program_project {n : Nat} {Auxiliary Output : Type}
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (ed : QueryImpl EdSpec (StateT Auxiliary ProbComp)) (work : OracleComp Spec Output) (state : WorldState n Auxiliary) :
    Prod.map id project <$> (simulateQ (worldImplementation sign ed) work).run state =
      (simulateQ (implementation sign ed) work).run (project state) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project (query_project sign ed) work state

end BeaconcryptCore.Computational.RegistrationBeaconInitShared

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitShared.query_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitShared.query_project
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitShared.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitShared.program_project
