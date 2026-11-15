-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServerMaterial

/-! Each actual admitted native Server completion asks for material once. Occupancy, complete-message size, current pin, allocator refusal, absent/reused handles and cancelled builds cannot increase this bill. All raw-record, hash, signing and publication continuations are local common requests. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsMaterial
open RegistrationNativeSecretWordServerMaterial
open RegistrationNativePairedServerService (Common)
open RegistrationNativeSecretWordServerMaterial (Spec commonLift admitted)
variable {n : Nat} {Value Encoded : Type}

def IsDemand : (Spec n).Domain → Prop
  | .inl _ => True
  | .inr _ => False

instance : DecidablePred (IsDemand (n := n)) := fun query => by
  cases query with
  | inl _ => exact isTrue trivial
  | inr _ => exact isFalse id

private theorem common_free (work : OracleComp (Common n) Value) :
    (simulateQ commonLift work).IsQueryBoundP IsDemand 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [commonLift, IsDemand, isQueryBoundP_query_iff]

/-- A successful admission makes exactly one material-service request before any later native failure or publication. -/
theorem admitted_bound (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : RegistrationNativeSecretWordMessage.Message) :
    (admitted (n := n) encode control initial message).IsQueryBoundP IsDemand 1 := by
  unfold admitted
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


/-- A real shared hash query is not a private material demand. This does not assign it zero hash or coin cost. -/
private theorem adHash_free (pending : registration.ServerAdHash) :
    (adHash (n := n) pending).IsQueryBoundP IsDemand 0 := by
  unfold adHash
  cases pending.request with
  | fail error | div => trivial
  | ok request =>
      exact isQueryBoundP_bind (n := 0) (m := 0)
        (by simp [effect, isQueryBoundP_query_iff, IsDemand]) (fun _ _ => by trivial)

/-- Complete native lookup/preflight/occupancy/reservation precede at most one material demand. -/
theorem complete_bound (wire : RegistrationNativeWire.Wire) (reservePeer : Bool)
    (ready : RegistrationNativeSecretWordMessage.ServerReady) (application : Slice U8) (before : State) :
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
                refine isQueryBoundP_bind (n := 0) (m := 1) (adHash_free selected) (fun hashed _ => ?_)
                cases hashed with
                | fail error | div => trivial
                | ok result => cases result with
                  | Err previous => trivial
                  | Ok initial =>
                    dsimp only
                    split
                    · exact isQueryBoundP_bind (n := 1) (m := 0)
                        (admitted_bound wire.encodeResponse before.control
                          (RegistrationBoundKeySchedule.publicInitial initial) ready.reference)
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

end BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsMaterial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsMaterial.admitted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsMaterial.admitted_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsMaterial.complete_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsMaterial.complete_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsMaterial.build_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsMaterial.build_bound
