-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveCaps
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveSessions

/-! Actual Server admitted, complete and one-use build programs demand only the retained descriptor whose concrete flag receipt is supplied by preparation. Cancellation, failed lookup, preflight, occupancy, allocator, publication and installation paths are all retained. A build needs only the internal live-session invariant, which the actual accept loop derives separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveMaterialCaps
open RegistrationNativeSecretWordServerMaterial
open RegistrationNativeSecretWordMessage (Message ServerReady)
open RegistrationNativeSecretWordLiveCaps (BadPublic)
open RegistrationNativeSecretWordLiveSessions (Live)
variable {n : Nat} {Encoded Value : Type}

private theorem common_free (flags : Message → Bool) (work : OracleComp (RegistrationNativePairedServerService.Common n) Value) :
    (simulateQ commonLift work).IsQueryBoundP (BadPublic flags) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [commonLift, BadPublic, isQueryBoundP_query_iff]

/-- The actual admitted branch demands exactly its already flagged reference and then only local common work. -/
theorem admitted_free (flags : Message → Bool) (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial) (reference : Message)
    (prepared : flags reference = true) :
    (admitted (n := n) encode control initial reference).IsQueryBoundP (BadPublic flags) 0 := by
  unfold admitted
  rw [isQueryBoundP_query_bind_iff]
  constructor
  · left
    simp only [BadPublic, prepared, Bool.true_eq_false, not_false_eq_true]
  · intro reply
    cases reply with
    | none => trivial
    | some choice =>
        simpa only [BadPublic, prepared, Bool.true_eq_false, ite_false] using
          common_free flags (RegistrationNativePairedServerService.publicBranch encode control initial choice)

private theorem finish_free (flags : Message → Bool) (result : RustM (RegistrationNativePairedServerService.Result Pqxdh.Bytes))
    (before : State) : ((finish (n := n) result).run before).IsQueryBoundP (BadPublic flags) 0 := by
  simp only [finish, StateT.run]
  cases result with
  | fail error => trivial
  | div => trivial
  | ok result => cases result <;> trivial

private theorem adHash_free (flags : Message → Bool) (pending : registration.ServerAdHash) :
    (adHash (n := n) pending).IsQueryBoundP (BadPublic flags) 0 := by
  cases requested : pending.request with
  | fail error | div => simp [adHash, requested]
  | ok request =>
      simp only [adHash, requested]
      refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => isQueryBoundP_pure _ _ _)
      simp [effect, isQueryBoundP_query_iff, BadPublic]

/-- Every concrete complete path asks only for its live transient Ready reference after the actual lookup and admission gates. -/
theorem complete_free (flags : Message → Bool) (wire : RegistrationNativeWire.Wire) (reservePeer : Bool)
    (ready : ServerReady) (application : Slice U8) (before : State) (prepared : flags ready.reference = true) :
    ((complete (n := n) wire reservePeer ready application).run before).IsQueryBoundP (BadPublic flags) 0 := by
  simp only [complete, StateT.run]
  cases actual : peer.begin_completion_lookup before.control before.pin (token ready) application with
  | fail error => trivial
  | div => trivial
  | ok reply => cases reply with
    | Err previous => trivial
    | Ok lookup =>
        simp only []
        cases requested : lookup.request with
        | fail error => trivial
        | div => trivial
        | ok keyId =>
            simp only []
            split
            · refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun occupied _ => ?_)
              · simp [effect, isQueryBoundP_query_iff, BadPublic]
              · cases resumed : lookup.resume occupied with
                | fail error => trivial
                | div => trivial
                | ok reply => cases reply with
                  | Err previous => trivial
                  | Ok selected =>
                      refine isQueryBoundP_bind (n := 0) (m := 0) (adHash_free flags selected) ?_
                      intro hashed _
                      cases hashed with
                      | fail error | div => trivial
                      | ok reply => cases reply with
                        | Err previous => trivial
                        | Ok initial =>
                            dsimp only
                            split
                            · exact isQueryBoundP_bind (n := 0) (m := 0)
                                (admitted_free flags wire.encodeResponse before.control
                                  (RegistrationBoundKeySchedule.publicInitial initial) ready.reference prepared)
                                (fun published _ => finish_free flags published before)
                            · trivial
            · trivial

/-- Taking any actual one-use session, including cancellation and every later failure, demands only a descriptor already live in that session table. -/
theorem build_free (flags : Message → Bool) (wire : RegistrationNativeWire.Wire) (reservePeer : Bool)
    (handle : Nat) (application : Option (Slice U8)) (before : State) (live : Live before flags) :
    ((build (n := n) wire reservePeer handle application).run before).IsQueryBoundP (BadPublic flags) 0 := by
  have receipt := RegistrationNativeSecretWordLiveSessions.take_live handle before flags live
  simp only [build, StateT.run]
  rcases taken : take handle before with ⟨ready, current⟩
  rw [taken] at receipt
  cases ready with
  | none => trivial
  | some ready =>
      cases application with
      | none => trivial
      | some application => exact complete_free flags wire reservePeer ready application current (receipt.2 ready rfl)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveMaterialCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveMaterialCaps.admitted_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveMaterialCaps.admitted_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveMaterialCaps.complete_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveMaterialCaps.complete_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveMaterialCaps.build_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveMaterialCaps.build_free
