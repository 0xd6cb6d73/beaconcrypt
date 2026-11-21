-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerSdkSource

/-! Actual Server builds consume or cancel one stored capability without changing the session roster length. Every AD-hash, publication and failure continuation retains that length; a failed build cannot recycle an earlier accept handle. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeBuildSessionFrame
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationServerFrontendCompiler (State)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

theorem world (work : StateT (RegistrationServerRootCompiler.Local n) ProbComp Value)
    (before after : State n) (reply : Value)
    (supported : (reply, after) ∈ support ((RegistrationServerSdkSource.world work).run before)) :
    after.sessions = before.sessions := by
  simp only [RegistrationServerSdkSource.world, StateT.run, support_map] at supported
  obtain ⟨inner, _, same⟩ := supported
  exact (congrArg (fun pair => pair.2.sessions) same).symm

theorem commit (published : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes))
    (before after : State n) (reply : RustM (Option (U64 × Pqxdh.Bytes)))
    (supported : (reply, after) ∈ support ((RegistrationServerSdkSource.commit published).run before)) :
    after.sessions = before.sessions := by
  cases published with
  | fail error | div =>
      simp only [RegistrationServerSdkSource.commit, StateT.run, mem_support_pure_iff] at supported
      cases supported
      rfl
  | ok outcome =>
      cases outcome <;>
        simp only [RegistrationServerSdkSource.commit, StateT.run, mem_support_pure_iff] at supported <;>
        cases supported <;> rfl

theorem fromInitial (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf)
    (before after : State n) (reply : RustM (Option (U64 × Pqxdh.Bytes))) :
    (reply, after) ∈ support ((RegistrationServerSdkSource.fromInitial setup codec sign encode control initial).run before) →
    after.sessions = before.sessions := by
  simp only [RegistrationServerSdkSource.fromInitial, StateT.run_bind, mem_support_bind_iff]
  rintro ⟨⟨published, middle⟩, called, continued⟩
  exact (commit published middle after reply continued).trans (world _ before middle published called)

theorem afterOccupancy (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool)
    (before after : State n) (reply : RustM (Option (U64 × Pqxdh.Bytes))) :
    (reply, after) ∈ support
      ((RegistrationServerSdkSource.afterOccupancy setup codec checks sign encode control lookup occupied).run before) →
    after.sessions = before.sessions := by
  unfold RegistrationServerSdkSource.afterOccupancy
  cases lookup.resume occupied with
  | fail error | div =>
      simp only [StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq]
      rintro ⟨rfl, rfl⟩
      rfl
  | ok answer => cases answer with
    | Err previous =>
        simp only [StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq]
        rintro ⟨rfl, rfl⟩
        rfl
    | Ok pending =>
        simp only [StateT.run_bind, mem_support_bind_iff]
        rintro ⟨⟨hashed, middle⟩, called, continued⟩
        have same := world (RegistrationWorldServerCompletion.adHash pending) before middle hashed called
        cases hashed with
        | fail error | div =>
            simp only [StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at continued
            obtain ⟨rfl, rfl⟩ := continued
            exact same
        | ok result => cases result with
          | Err previous =>
              simp only [StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at continued
              obtain ⟨rfl, rfl⟩ := continued
              exact same
          | Ok initial =>
              by_cases reserved : checks.reservePeer = true
              · simp only [reserved, ite_true] at continued
                exact (fromInitial setup codec sign encode control initial middle after reply continued).trans same
              · simp only [reserved, Bool.false_eq_true, ite_false, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at continued
                obtain ⟨rfl, rfl⟩ := continued
                exact same

theorem complete (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice U8)
    (before after : State n) (reply : RustM (Option (U64 × Pqxdh.Bytes))) :
    (reply, after) ∈ support ((RegistrationServerSdkSource.complete setup codec checks sign encode token application).run before) →
    after.sessions = before.sessions := by
  unfold RegistrationServerSdkSource.complete
  simp only [StateT.run]
  cases peer.begin_completion_lookup before.control before.pin token application with
  | fail error | div =>
      simp only [mem_support_pure_iff, Prod.mk.injEq]
      rintro ⟨rfl, rfl⟩
      rfl
  | ok answer => cases answer with
    | Err previous =>
        simp only [mem_support_pure_iff, Prod.mk.injEq]
        rintro ⟨rfl, rfl⟩
        rfl
    | Ok lookup => cases requested : lookup.request with
      | fail error | div =>
          simp only [requested, mem_support_pure_iff, Prod.mk.injEq]
          rintro ⟨rfl, rfl⟩
          rfl
      | ok keyId =>
          simp only [requested]
          by_cases admitted : RegistrationServerSdkSource.preflight application keyId = true
          · simp only [admitted, ite_true, mem_support_bind_iff]
            rintro ⟨⟨occupied, middle⟩, called, continued⟩
            exact (afterOccupancy setup codec checks sign encode before.control lookup occupied middle after reply continued).trans
              (world _ before middle occupied called)
          · simp only [admitted, Bool.false_eq_true, ite_false, mem_support_pure_iff, Prod.mk.injEq]
            rintro ⟨rfl, rfl⟩
            rfl

theorem take (handle : Nat) (before : State n) :
    (RegistrationServerSdkSource.take handle before).2.sessions.length = before.sessions.length := by
  unfold RegistrationServerSdkSource.take
  cases before.sessions[handle]? with
  | none => rfl
  | some entry => cases entry with
    | none => rfl
    | some token => exact List.length_set

theorem build (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (handle : Nat) (application : Option (Slice U8))
    (before after : State n) (reply : RustM (Option (U64 × Pqxdh.Bytes))) :
    (reply, after) ∈ support ((RegistrationServerSdkSource.build setup codec checks sign encode handle application).run before) →
    after.sessions.length = before.sessions.length := by
  have size := take handle before
  unfold RegistrationServerSdkSource.build
  simp only [StateT.run]
  cases selected : RegistrationServerSdkSource.take handle before with
  | mk entry middle =>
    simp only [selected] at size
    cases entry with
    | none =>
        simp only [mem_support_pure_iff, Prod.mk.injEq]
        rintro ⟨rfl, rfl⟩
        exact size
    | some token => cases application with
      | none =>
          simp only [mem_support_pure_iff, Prod.mk.injEq]
          rintro ⟨rfl, rfl⟩
          exact size
      | some application =>
          intro _
          exact (congrArg List.length (complete setup codec checks sign encode token application middle after reply (by assumption))).trans size

end BeaconcryptCore.Computational.RegistrationNativeBuildSessionFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildSessionFrame.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildSessionFrame.world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildSessionFrame.commit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildSessionFrame.commit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildSessionFrame.fromInitial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildSessionFrame.fromInitial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildSessionFrame.afterOccupancy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildSessionFrame.afterOccupancy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildSessionFrame.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildSessionFrame.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildSessionFrame.take' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildSessionFrame.take

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildSessionFrame.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildSessionFrame.build
