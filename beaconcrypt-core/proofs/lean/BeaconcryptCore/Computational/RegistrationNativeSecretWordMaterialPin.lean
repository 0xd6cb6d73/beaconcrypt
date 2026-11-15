-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServerMaterial

/-! Native Server completion preserves the original authentication pin through one-use consumption, all completion gates, raw publication and peer installation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordMaterialPin
open RegistrationNativeSecretWordServerMaterial (State Result)
open RegistrationNativeSecretWordMessage (ServerReady)
abbrev Ready := ServerReady
variable {n : Nat}

/-- Every native publication and installation outcome keeps the Server pin. -/
theorem finish_pin (published : RustM (RegistrationNativePairedServerService.Result Pqxdh.Bytes))
    (before : State) (result : Result × State)
    (supported : result ∈ support ((RegistrationNativeSecretWordServerMaterial.finish (n := n) published).run before)) :
    result.2.pin = before.pin := by
  cases published with
  | fail error =>
      simp only [RegistrationNativeSecretWordServerMaterial.finish, StateT.run, mem_support_pure_iff] at supported
      subst result
      rfl
  | div =>
      simp only [RegistrationNativeSecretWordServerMaterial.finish, StateT.run, mem_support_pure_iff] at supported
      subst result
      rfl
  | ok publication =>
      cases publication <;>
        simp only [RegistrationNativeSecretWordServerMaterial.finish, StateT.run, mem_support_pure_iff] at supported
      all_goals subst result; rfl

/-- Complete-message preflight, occupancy, reservation and all primitive outcomes retain the Server pin. -/
theorem complete_pin (wire : RegistrationNativeWire.Wire) (reservePeer : Bool)
    (ready : Ready) (application : Slice U8) (before : State) (result : Result × State)
    (supported : result ∈ support ((RegistrationNativeSecretWordServerMaterial.complete (n := n) wire reservePeer ready application).run before)) :
    result.2.pin = before.pin := by
  unfold RegistrationNativeSecretWordServerMaterial.complete at supported
  simp only [StateT.run] at supported
  cases beginEq : peer.begin_completion_lookup before.control before.pin (RegistrationNativeSecretWordServerMaterial.token ready) application with
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
                  simp only [resumeEq, mem_support_bind_iff] at supported
                  obtain ⟨hashed, _, supported⟩ := supported
                  cases hashed with
                  | fail error | div =>
                      simp only [mem_support_pure_iff] at supported
                      subst result
                      rfl
                  | ok answer => cases answer with
                    | Err previous =>
                        simp only [mem_support_pure_iff] at supported
                        subst result
                        rfl
                    | Ok initial =>
                        dsimp only at supported
                        split at supported
                        · rw [mem_support_bind_iff] at supported
                          obtain ⟨published, _possible, supported⟩ := supported
                          exact finish_pin published before result supported
                        · rw [mem_support_pure_iff] at supported
                          subst result
                          rfl
          · rw [mem_support_pure_iff] at supported
            subst result
            rfl

/-- Every build outcome has the original authentication pin after the one-use take. -/
theorem build_pin (wire : RegistrationNativeWire.Wire) (reservePeer : Bool) (handle : Nat)
    (application : Option (Slice U8)) (before : State) (result : Result × State)
    (supported : result ∈ support ((RegistrationNativeSecretWordServerMaterial.build (n := n) wire reservePeer handle application).run before)) :
    result.2.pin = (RegistrationNativeSecretWordServerMaterial.take handle before).2.pin := by
  unfold RegistrationNativeSecretWordServerMaterial.build at supported
  simp only [StateT.run] at supported
  cases chosen : RegistrationNativeSecretWordServerMaterial.take handle before with
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
            exact complete_pin wire reservePeer ready application current result supported

/-- Taking a one-use session never changes the original Server pin. -/
theorem take_pin (handle : Nat) (before : State) :
    (RegistrationNativeSecretWordServerMaterial.take handle before).2.pin = before.pin := by
  unfold RegistrationNativeSecretWordServerMaterial.take
  cases found : before.sessions[handle]? with
  | none => rfl
  | some entry => cases entry <;> rfl

end BeaconcryptCore.Computational.RegistrationNativeSecretWordMaterialPin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordMaterialPin.finish_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordMaterialPin.finish_pin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordMaterialPin.complete_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordMaterialPin.complete_pin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordMaterialPin.build_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordMaterialPin.build_pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordMaterialPin.take_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordMaterialPin.take_pin
