-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerMaterialFrontend

/-! Native Server completion changes allocator control and the record World, but never creates or replaces a retained registration capability. The only build roster change is the original one-use take, before every later failure or successful publication. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerMaterialSessions
open RegistrationServerMaterialFrontend (State Result)
open RegistrationServerReferenceRoot (Ready)
variable {n : Nat}

/-- Every native publication/installation outcome keeps the moved capability roster unchanged. -/
theorem finish_sessions (published : RustM (RegistrationNativePairedServerService.Result Pqxdh.Bytes))
    (before : State) (result : Result × State)
    (supported : result ∈ support ((RegistrationServerMaterialFrontend.finish (n := n) published).run before)) :
    result.2.sessions = before.sessions := by
  cases published with
  | fail error =>
      simp only [RegistrationServerMaterialFrontend.finish, StateT.run, mem_support_pure_iff] at supported
      subst result
      rfl
  | div =>
      simp only [RegistrationServerMaterialFrontend.finish, StateT.run, mem_support_pure_iff] at supported
      subst result
      rfl
  | ok publication =>
      cases publication <;>
        simp only [RegistrationServerMaterialFrontend.finish, StateT.run, mem_support_pure_iff] at supported
      all_goals subst result; rfl

/-- Complete-message preflight, occupancy, reservation and all primitive outcomes retain the original moved-capability roster. -/
theorem complete_sessions (wire : RegistrationNativeWire.Wire) (reservePeer : Bool)
    (ready : Ready) (application : Slice U8) (before : State) (result : Result × State)
    (supported : result ∈ support ((RegistrationServerMaterialFrontend.complete (n := n) wire reservePeer ready application).run before)) :
    result.2.sessions = before.sessions := by
  unfold RegistrationServerMaterialFrontend.complete at supported
  simp only [StateT.run] at supported
  cases beginEq : peer.begin_completion_lookup before.control before.pin (RegistrationServerMaterialFrontend.token ready) application with
  | fail error =>
      simp only [beginEq, mem_support_pure_iff] at supported
      subst result
      rfl
  | div =>
      simp only [beginEq, mem_support_pure_iff] at supported
      subst result
      rfl
  | ok lookupResult => cases lookupResult with
    | Err previous =>
        simp only [beginEq, mem_support_pure_iff] at supported
        subst result
        rfl
    | Ok lookup => cases requestEq : lookup.request with
      | fail error =>
          simp only [beginEq, requestEq, mem_support_pure_iff] at supported
          subst result
          rfl
      | div =>
          simp only [beginEq, requestEq, mem_support_pure_iff] at supported
          subst result
          rfl
      | ok keyId =>
          simp only [beginEq, requestEq] at supported
          split at supported
          · rw [mem_support_bind_iff] at supported
            obtain ⟨occupied, _possible, supported⟩ := supported
            cases resumeEq : lookup.resume occupied with
            | fail error =>
                simp only [resumeEq, mem_support_pure_iff] at supported
                subst result
                rfl
            | div =>
                simp only [resumeEq, mem_support_pure_iff] at supported
                subst result
                rfl
            | ok completionResult => cases completionResult with
              | Err previous =>
                  simp only [resumeEq, mem_support_pure_iff] at supported
                  subst result
                  rfl
              | Ok selected =>
                  simp only [resumeEq] at supported
                  rw [mem_support_bind_iff] at supported
                  obtain ⟨hashed, _hashPossible, supported⟩ := supported
                  cases hashed with
                  | fail error | div =>
                      rw [mem_support_pure_iff] at supported
                      subst result
                      rfl
                  | ok completion => cases completion with
                    | Err previous =>
                        rw [mem_support_pure_iff] at supported
                        subst result
                        rfl
                    | Ok initial =>
                        dsimp only at supported
                        split at supported
                        · rw [mem_support_bind_iff] at supported
                          obtain ⟨published, _possible, supported⟩ := supported
                          exact finish_sessions published before result supported
                        · rw [mem_support_pure_iff] at supported
                          subst result
                          rfl
          · rw [mem_support_pure_iff] at supported
            subst result
            rfl

/-- Every build outcome has precisely the capability roster after the initial take, including cancellation and every later native failure. -/
theorem build_sessions (wire : RegistrationNativeWire.Wire) (reservePeer : Bool) (handle : Nat)
    (application : Option (Slice U8)) (before : State) (result : Result × State)
    (supported : result ∈ support ((RegistrationServerMaterialFrontend.build (n := n) wire reservePeer handle application).run before)) :
    result.2.sessions = (RegistrationServerMaterialFrontend.take handle before).2.sessions := by
  unfold RegistrationServerMaterialFrontend.build at supported
  simp only [StateT.run] at supported
  cases chosen : RegistrationServerMaterialFrontend.take handle before with
  | mk ready current =>
      cases ready with
      | none =>
          simp only [chosen, mem_support_pure_iff] at supported
          subst result
          rfl
      | some ready => cases application with
        | none =>
            simp only [chosen, mem_support_pure_iff] at supported
            subst result
            rfl
        | some application =>
            simp only [chosen] at supported
            exact complete_sessions wire reservePeer ready application current result supported

end BeaconcryptCore.Computational.RegistrationServerMaterialSessions
/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialSessions.finish_sessions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialSessions.finish_sessions
/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialSessions.complete_sessions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialSessions.complete_sessions
/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialSessions.build_sessions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialSessions.build_sessions
