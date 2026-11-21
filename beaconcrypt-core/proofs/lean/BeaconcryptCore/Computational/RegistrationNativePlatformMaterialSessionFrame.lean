-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendProgram
/-! Every corrected Server completion phase preserves the remaining one-use token list. The build entry first consumes its selected handle; subsequent pin, occupancy, shared reservation, material and publication outcomes can update only the public control field. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMaterialSessionFrame
open RegistrationServerMaterialFrontend (State)
open RegistrationNativePlatformServerMaterialFrontend
variable {Index Encoded : Type} {spec : OracleSpec Index}
variable (deriveAd : AdHash (OracleComp spec))

private theorem finish_sessions (published : RustM (RegistrationHiddenInstall.Result Encoded)) (before : State) :
    (finish published before).2.sessions = before.sessions := by
  cases published with
  | fail _ | div => rfl
  | ok result => cases result <;> rfl

private theorem after_result (reserve : OracleComp spec Bool) (service : Service (OracleComp spec) Encoded)
    (control : pqxdh.ServerState) (message : RegistrationNativeRelatedFamily.Message)
    (action : RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState))
    (before after : State) (reply : Result Encoded)
    (supported : (reply, after) ∈ support ((afterResult reserve service control message action).run before)) :
    after.sessions = before.sessions := by
  cases action with
  | fail error | div =>
      simp only [afterResult, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | ok outcome => cases outcome with
    | Err previous =>
        simp only [afterResult, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        rfl
    | Ok selected =>
        simp only [afterResult, StateT.run_bind, StateT.run_lift, bind_map_left, bind_pure_comp, mem_support_bind_iff] at supported
        obtain ⟨admitted, _reserved, continued⟩ := supported
        cases admitted with
        | false =>
            simp only [Bool.false_eq_true, ite_false, StateT.run_pure, mem_support_pure_iff] at continued
            cases continued
            rfl
        | true =>
            simp only [ite_true, StateT.run_bind, StateT.run_lift, bind_map_left, bind_pure_comp, mem_support_bind_iff] at continued
            obtain ⟨published, _called, returned⟩ := continued
            change (reply, after) ∈ support (pure (finish published before)) at returned
            rw [mem_support_pure_iff] at returned
            exact (congrArg (fun value => value.2.sessions) returned).trans (finish_sessions published before)


private theorem after_occupancy (reserve : OracleComp spec Bool) (service : Service (OracleComp spec) Encoded)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (message : RegistrationNativeRelatedFamily.Message)
    (occupied : Bool) (before after : State) (reply : Result Encoded)
    (supported : (reply, after) ∈ support ((afterOccupancy deriveAd reserve service control lookup message occupied).run before)) :
    after.sessions = before.sessions := by
  cases resumed : lookup.resume occupied with
  | fail error | div =>
      simp only [afterOccupancy, resumed, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | ok outcome => cases outcome with
    | Err previous =>
        simp only [afterOccupancy, resumed, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        rfl
    | Ok pending =>
        simp only [afterOccupancy, resumed, StateT.run_bind, StateT.run_lift,
          bind_map_left, bind_pure_comp, mem_support_bind_iff] at supported
        obtain ⟨hashed, _queried, continued⟩ := supported
        exact after_result reserve service control message _ before after reply continued

private theorem after_pin (reserve : OracleComp spec Bool) (present : U64 → OracleComp spec Bool)
    (service : Service (OracleComp spec) Encoded) (control : pqxdh.ServerState)
    (ready : RegistrationServerReferenceRoot.Ready) (application : Slice U8)
    (current : RustM (core.option.Option session.ServerAuthenticationPin)) (before after : State) (reply : Result Encoded)
    (supported : (reply, after) ∈ support ((afterPin deriveAd reserve present service control ready application current).run before)) :
    after.sessions = before.sessions := by
  cases current with
  | fail error | div =>
      simp only [afterPin, StateT.run, mem_support_pure_iff] at supported
      cases supported
      rfl
  | ok optional => cases optional with
    | none =>
        simp only [afterPin, StateT.run, mem_support_pure_iff] at supported
        cases supported
        rfl
    | some current =>
        unfold afterPin at supported
        dsimp only [StateT.run] at supported
        cases lookup : peer.begin_completion_lookup control current (RegistrationServerMaterialFrontend.token ready) application with
        | fail error | div =>
            simp only [lookup, mem_support_pure_iff] at supported
            cases supported
            rfl
        | ok outcome => cases outcome with
          | Err previous =>
              simp only [lookup, mem_support_pure_iff] at supported
              cases supported
              rfl
          | Ok selected =>
              simp only [lookup] at supported
              cases request : selected.request with
              | fail error | div =>
                  simp only [request, mem_support_pure_iff] at supported
                  cases supported
                  rfl
              | ok keyId =>
                  by_cases fits : RegistrationServerSdkSource.preflight application keyId = true
                  · simp only [request, ite_eq_left fits, mem_support_bind_iff] at supported
                    obtain ⟨occupied, _queried, continued⟩ := supported
                    exact after_occupancy deriveAd reserve service control selected ready.reference occupied before after reply continued
                  · simp only [request, ite_eq_right fits, mem_support_pure_iff] at supported
                    cases supported
                    rfl

/-- The entire corrected completion preserves all still-owned public session capabilities through every gate, writer and material outcome. -/
theorem complete_sessions
    (pin : session.ServerAuthenticationPin → OracleComp spec (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : OracleComp spec Bool) (present : U64 → OracleComp spec Bool) (service : Service (OracleComp spec) Encoded)
    (ready : RegistrationServerReferenceRoot.Ready) (application : Slice U8)
    (before after : State) (reply : Result Encoded)
    (supported : (reply, after) ∈ support ((complete deriveAd pin reserve present service ready application).run before)) :
    after.sessions = before.sessions := by
  change (reply, after) ∈ support (do
    let current ← pin before.pin
    (afterPin deriveAd reserve present service before.control ready application current).run before) at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨current, _computed, continued⟩ := supported
  exact after_pin deriveAd reserve present service before.control ready application current before after reply continued


private theorem mem_set_none (sessions : List (Option RegistrationServerReferenceRoot.Ready)) (index : Nat)
    (ready : RegistrationServerReferenceRoot.Ready) (member : some ready ∈ sessions.set index none) : some ready ∈ sessions := by
  induction sessions generalizing index with
  | nil => simp only [List.set_nil, List.not_mem_nil] at member
  | cons head tail ih => cases index with
    | zero =>
        simp only [List.set_cons_zero, List.mem_cons] at member
        rcases member with impossible | earlier
        · cases impossible
        · exact List.mem_cons_of_mem _ earlier
    | succ index =>
        simp only [List.set_cons_succ, List.mem_cons] at member
        rcases member with same | earlier
        · exact List.mem_cons.mpr (Or.inl same)
        · exact List.mem_cons_of_mem _ (ih index earlier)

private theorem take_subset (index : Nat) (before : State) (ready : RegistrationServerReferenceRoot.Ready)
    (member : some ready ∈ (RegistrationServerMaterialFrontend.take index before).2.sessions) :
    some ready ∈ before.sessions := by
  unfold RegistrationServerMaterialFrontend.take at member
  cases found : before.sessions[index]? with
  | none => simpa only [found] using member
  | some entry => cases entry with
    | none => simpa only [found] using member
    | some selected => exact mem_set_none before.sessions index ready (by simpa only [found] using member)

/-- Every corrected build outcome retains only earlier session capabilities; the chosen handle is consumed before all later effects. -/
theorem build_subset
    (pin : session.ServerAuthenticationPin → OracleComp spec (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : OracleComp spec Bool) (present : U64 → OracleComp spec Bool) (service : Service (OracleComp spec) Encoded)
    (index : Nat) (application : Option (Slice U8)) (before after : State) (reply : Result Encoded)
    (supported : (reply, after) ∈ support ((build deriveAd pin reserve present service index application).run before))
    (ready : RegistrationServerReferenceRoot.Ready) (member : some ready ∈ after.sessions) :
    some ready ∈ before.sessions := by
  unfold build at supported
  dsimp only [StateT.run] at supported
  cases taken : RegistrationServerMaterialFrontend.take index before with
  | mk optional current =>
      have subset : ∀ retained, some retained ∈ current.sessions → some retained ∈ before.sessions := by
        intro retained stored
        exact take_subset index before retained (by simpa only [taken] using stored)
      cases optional with
      | none =>
          simp only [taken, mem_support_pure_iff] at supported
          cases supported
          exact subset ready member
      | some selected => cases application with
        | none =>
            simp only [taken, mem_support_pure_iff] at supported
            cases supported
            exact subset ready member
        | some application =>
            simp only [taken] at supported
            have preserved := complete_sessions deriveAd pin reserve present service selected application current after reply supported
            rw [preserved] at member
            exact subset ready member


/-- The exact five-leaf source build program has the same token-subset property before any interpreter is chosen. -/
theorem program_subset (index : Nat) (application : Option (Slice U8)) (before after : State)
    (reply : Result (alloc.vec.Vec U8))
    (supported : (reply, after) ∈ support ((RegistrationNativePlatformServerFrontendProgram.program index application).run before))
    (ready : RegistrationServerReferenceRoot.Ready) (member : some ready ∈ after.sessions) : some ready ∈ before.sessions :=
  build_subset RegistrationNativePlatformServerFrontendProgram.adHash RegistrationNativePlatformServerFrontendProgram.pin RegistrationNativePlatformServerFrontendProgram.reserve
    RegistrationNativePlatformServerFrontendProgram.present RegistrationNativePlatformServerFrontendProgram.service
    index application before after reply supported ready member

end BeaconcryptCore.Computational.RegistrationNativePlatformMaterialSessionFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterialSessionFrame.complete_sessions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterialSessionFrame.complete_sessions

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterialSessionFrame.build_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterialSessionFrame.build_subset

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterialSessionFrame.program_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterialSessionFrame.program_subset
