-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerMaterialFrontend

/-! Each actual admitted native Server completion asks for material once. Occupancy, complete-message size, current pin, allocator refusal, absent/reused handles and cancelled builds cannot increase this bill. All raw-record, hash, signing and publication continuations are local common requests. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerMaterialCaps
open RegistrationServerMaterialFrontend
open RegistrationNativePairedServerService (Common PublicSpec publicCommon publicAdmitted)
variable {n : Nat} {Value Encoded : Type}

def IsDemand : (PublicSpec n).Domain → Prop
  | .inl _ => True
  | .inr _ => False

instance : DecidablePred (IsDemand (n := n)) := fun query => by
  cases query with
  | inl _ => exact isTrue trivial
  | inr _ => exact isFalse id

private theorem common_free (work : OracleComp (Common n) Value) :
    (simulateQ publicCommon work).IsQueryBoundP IsDemand 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [publicCommon, IsDemand, isQueryBoundP_query_iff]

/-- A successful admission makes exactly one material-service request before any later native failure or publication. -/
theorem admitted_bound (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : RegistrationNativeRelatedFamily.Message) :
    (publicAdmitted (n := n) encode control initial message).IsQueryBoundP IsDemand 1 := by
  unfold publicAdmitted
  rw [isQueryBoundP_query_bind_iff]
  constructor
  · right; decide
  · intro reply
    cases reply with
    | none => trivial
    | some choice => exact common_free _

private theorem finish_free (result : RustM (RegistrationNativePairedServerService.Result Pqxdh.Bytes))
    (before : State) : ((finish (n := n) result).run before).IsQueryBoundP IsDemand 0 := by
  simp only [finish, StateT.run]
  cases result with
  | fail error => trivial
  | div => trivial
  | ok reply => cases reply <;> trivial


/-- Complete native lookup/preflight/occupancy/reservation precede at most one material demand. -/
theorem complete_bound (wire : RegistrationNativeWire.Wire) (reservePeer : Bool)
    (ready : RegistrationServerReferenceRoot.Ready) (application : Slice U8) (before : State) :
    ((complete (n := n) wire reservePeer ready application).run before).IsQueryBoundP IsDemand 1 := by
  simp only [complete, StateT.run]
  cases actual : peer.begin_completion_lookup before.control before.pin (token ready) application with
  | fail error => trivial
  | div => trivial
  | ok reply =>
    cases reply with
    | Err previous => trivial
    | Ok lookup =>
      simp only []
      cases requested : lookup.request with
      | fail error => trivial
      | div => trivial
      | ok keyId =>
        simp only []
        split
        · refine isQueryBoundP_bind (n := 0) (m := 1) ?_ (fun occupied _ => ?_)
          · simp [effect, isQueryBoundP_query_iff, IsDemand]
          · cases resumed : lookup.resume occupied with
            | fail error => trivial
            | div => trivial
            | ok reply =>
              cases reply with
              | Err previous => trivial
              | Ok selected =>
                simp only []
                split
                · exact isQueryBoundP_bind (n := 1) (m := 0)
                    (admitted_bound wire.encodeResponse before.control
                      (RegistrationBoundKeySchedule.publicInitial selected) ready.reference)
                    (fun published _ => finish_free published before)
                · trivial
        · trivial

/-- Taking a handle and cancellation are local; every concrete build has at most one material demand. -/
theorem build_bound (wire : RegistrationNativeWire.Wire) (reservePeer : Bool) (handle : Nat)
    (application : Option (Slice U8)) (before : State) :
    ((build (n := n) wire reservePeer handle application).run before).IsQueryBoundP IsDemand 1 := by
  simp only [build, StateT.run]
  cases taken : take handle before with
  | mk ready current =>
    cases ready with
    | none => trivial
    | some ready =>
      cases application with
      | none => trivial
      | some application => exact complete_bound wire reservePeer ready application current

end BeaconcryptCore.Computational.RegistrationServerMaterialCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialCaps.admitted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialCaps.admitted_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialCaps.complete_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialCaps.complete_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialCaps.build_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialCaps.build_bound
