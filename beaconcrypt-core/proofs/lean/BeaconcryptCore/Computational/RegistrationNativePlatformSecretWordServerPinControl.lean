-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuild
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveSessions
/-! Corrected stateful completion retains its configured Server authentication pin through every repeated pin, occupancy, reservation and publication outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinControl
open RegistrationNativeSecretWordMessage (ServerState ServerReady Message)
open RegistrationNativePlatformSecretWordBuildControl
open RegistrationNativePlatformServerMaterialFrontend (Result)
variable {J World Encoded : Type} {spec : OracleSpec J}
private abbrev M (World : Type) (spec : OracleSpec J) := StateT World (OracleComp spec)
private theorem afterResult_pin (reserve : M World spec Bool) (service : Service (M World spec) Encoded)
    (control : pqxdh.ServerState) (reference : Message)
    (answer : RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState))
    (before : ServerState) (previous : World) (result : (Result Encoded × ServerState) × World)
    (supported : result ∈ support (((afterResult reserve service control reference answer).run before).run previous)) :
    result.1.2.pin = before.pin := by
  cases answer with
  | fail error | div =>
      simp only [afterResult, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | ok answer => cases answer with
    | Err state =>
      simp only [afterResult, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
    | Ok initial =>
      simp only [afterResult, StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨allowed, _called, supported⟩ := supported
      cases allowedEq : allowed.1 with
      | false =>
        simp only [allowedEq, Bool.false_eq_true, ite_false, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        rfl
      | true =>
        simp only [allowedEq, ite_true, StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left] at supported
        rw [mem_support_bind_iff] at supported
        obtain ⟨published, _called, supported⟩ := supported
        change result ∈ support (pure (finish published.1 before, published.2)) at supported
        rw [mem_support_pure_iff] at supported
        cases supported
        cases outcome : published.1 with
        | fail error | div => rfl
        | ok value => cases value <;> rfl


private theorem afterOccupancy_pin (deriveAd : RegistrationNativePlatformServerMaterialFrontend.AdHash (M World spec))
    (reserve : M World spec Bool) (service : Service (M World spec) Encoded)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (reference : Message) (occupied : Bool)
    (before : ServerState) (previous : World) (result : (Result Encoded × ServerState) × World)
    (supported : result ∈ support (((afterOccupancy deriveAd reserve service control lookup reference occupied).run before).run previous)) :
    result.1.2.pin = before.pin := by
  unfold afterOccupancy at supported
  cases resumed : lookup.resume occupied with
  | fail error | div =>
      simp only [resumed, StateT.run, StateT.monad_pure_def, StateT.pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | ok answer => cases answer with
    | Err previous =>
        simp only [resumed, StateT.run, StateT.monad_pure_def, StateT.pure, mem_support_pure_iff] at supported
        cases supported
        rfl
    | Ok pending =>
        simp only [resumed, StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left,
          mem_support_bind_iff] at supported
        obtain ⟨hashed, _called, supported⟩ := supported
        exact afterResult_pin reserve service control reference _ before hashed.2 result supported

private theorem afterPin_pin (deriveAd : RegistrationNativePlatformServerMaterialFrontend.AdHash (M World spec)) (reserve : M World spec Bool) (present : U64 → M World spec Bool)
    (service : Service (M World spec) Encoded) (control : pqxdh.ServerState)
    (ready : ServerReady) (application : Slice U8)
    (current : RustM (core.option.Option session.ServerAuthenticationPin))
    (before : ServerState) (previous : World) (result : (Result Encoded × ServerState) × World)
    (supported : result ∈ support (((afterPin deriveAd reserve present service control ready application current).run before).run previous)) :
    result.1.2.pin = before.pin := by
  cases current with
  | fail error | div =>
      simp only [afterPin, StateT.run, StateT.monad_pure_def, StateT.pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | ok current => cases current with
    | none =>
      simp only [afterPin, StateT.run, StateT.monad_pure_def, StateT.pure, mem_support_pure_iff] at supported
      cases supported
      rfl
    | some pin =>
      unfold afterPin at supported
      dsimp only [StateT.run] at supported
      cases beginning : peer.begin_completion_lookup control pin (RegistrationNativeSecretWordServerMaterial.token ready) application with
      | fail error | div =>
        simp only [beginning, StateT.monad_pure_def, StateT.pure, mem_support_pure_iff] at supported
        cases supported
        rfl
      | ok answer =>
        simp only [beginning] at supported
        cases answer with
        | Err state =>
          simp only [StateT.monad_pure_def, StateT.pure, mem_support_pure_iff] at supported
          cases supported
          rfl
        | Ok lookup =>
          cases requested : lookup.request with
          | fail error | div =>
            simp only [requested, StateT.monad_pure_def, StateT.pure, mem_support_pure_iff] at supported
            cases supported
            rfl
          | ok keyId =>
            simp only [requested] at supported
            split at supported
            · change result ∈ support ((do
                let occupied ← present keyId
                (afterOccupancy deriveAd reserve service control lookup ready.reference occupied).run before).run previous) at supported
              rw [StateT.run_bind, mem_support_bind_iff] at supported
              obtain ⟨occupied, _called, supported⟩ := supported
              exact afterOccupancy_pin deriveAd reserve service control lookup ready.reference occupied.1 before occupied.2 result supported
            · simp only [StateT.monad_pure_def, StateT.pure, mem_support_pure_iff] at supported
              cases supported
              rfl

/-- Every corrected moved-token controller result retains exactly the configured pin after the literal initial take. -/
theorem build_pin
    (deriveAd : RegistrationNativePlatformServerMaterialFrontend.AdHash (M World spec))
    (pin : session.ServerAuthenticationPin → M World spec (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : M World spec Bool) (present : U64 → M World spec Bool) (service : Service (M World spec) Encoded)
    (handle : Nat) (application : Option (Slice U8)) (before : ServerState) (previous : World)
    (result : (Result Encoded × ServerState) × World)
    (supported : result ∈ support (((build deriveAd pin reserve present service handle application).run before).run previous)) :
    result.1.2.pin = (RegistrationNativeSecretWordServerMaterial.take handle before).2.pin := by
  unfold build at supported
  rcases taken : RegistrationNativeSecretWordServerMaterial.take handle before with ⟨selected, current⟩
  simp only [StateT.run, taken] at supported
  cases selected with
  | none =>
    simp only [StateT.monad_pure_def, StateT.pure, mem_support_pure_iff] at supported
    cases supported
    rfl
  | some ready => cases application with
    | none =>
      simp only [StateT.monad_pure_def, StateT.pure, mem_support_pure_iff] at supported
      cases supported
      rfl
    | some application =>
      change result ∈ support ((do
        let currentPin ← pin current.pin
        (afterPin deriveAd reserve present service current.control ready application currentPin).run current).run previous) at supported
      rw [StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨pinned, _called, supported⟩ := supported
      exact afterPin_pin deriveAd reserve present service current.control ready application pinned.1 current pinned.2 result supported


end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinControl

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinControl.build_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinControl.build_pin
