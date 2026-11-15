-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety
/-! Query predicates are preserved by the actual stateful Server SDK continuation, including token consumption, pin recomputation, lookup, occupancy, reservation, publication and installation. The predicate is generic so generation exclusion and live-key validity share this checked controller proof. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkQuerySafety
open RegistrationNativePlatformQuerySafety
open RegistrationNativePlatformMldsaProgram (M)
open RegistrationNativeMldsaProgram (Spec)
open RegistrationNativePlatformCompletionSdk
variable {source : RegistrationNativeMldsa.Source} {Platform State Value : Type} {n : Nat} {Encoded : Type}
variable (predicate : (Spec source).Domain → Prop)

theorem get_safe : Safe predicate (get : StateT State (M source Platform) State) :=
  fun _ _ => allQueriesSatisfy_pure _ _

theorem world (work : StateT (RegistrationServerRootCompiler.Local n) (M source Platform) Value)
    (allowed : Safe predicate work) :
    Safe predicate (RegistrationNativePlatformServerSdk.world work) :=
  frame_safe predicate (fun current : RegistrationServerFrontendCompiler.State n => current.world) (fun current after => { current with world := after }) work allowed

theorem commit (published : RustM (RegistrationWorldServerCompletion.Result Encoded)) :
    Safe predicate (RegistrationNativePlatformServerSdk.commit (n := n) (m := M source Platform) published) := by
  intro before previous
  cases published with
  | fail error | div => exact allQueriesSatisfy_pure _ _
  | ok result => cases result <;> exact allQueriesSatisfy_pure _ _

theorem fromInitial (finish : Completion n (M source Platform) Encoded)
    (allowed : ∀ control initial, Safe predicate (finish control initial))
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf) :
    Safe predicate (RegistrationNativePlatformCompletionSdk.fromInitial finish control initial) := by
  unfold RegistrationNativePlatformCompletionSdk.fromInitial
  exact bind_safe predicate _ _ (world predicate _ (allowed control initial)) (commit predicate)

theorem afterOccupancy (deriveAd : AdHash n (M source Platform))
    (hashed : ∀ pending, Safe predicate (deriveAd pending)) (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (reserved : Safe predicate reserve) (finish : Completion n (M source Platform) Encoded)
    (allowed : ∀ control initial, Safe predicate (finish control initial))
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    Safe predicate (RegistrationNativePlatformCompletionSdk.afterOccupancy deriveAd reserve finish control lookup occupied) := by
  unfold RegistrationNativePlatformCompletionSdk.afterOccupancy
  cases lookup.resume occupied with
  | fail error | div => exact pure_safe predicate _
  | ok result => cases result with
    | Err previous => exact pure_safe predicate _
    | Ok pending =>
        apply bind_safe predicate _ _ (hashed pending)
        intro reply
        cases reply with
        | fail error | div => exact pure_safe predicate _
        | ok result => cases result with
          | Err previous => exact pure_safe predicate _
          | Ok initial =>
              apply bind_safe predicate _ _ reserved
              intro admitted
              cases admitted with
              | false => exact pure_safe predicate _
              | true => exact fromInitial predicate finish allowed control initial

theorem afterPin (deriveAd : AdHash n (M source Platform))
    (hashed : ∀ pending, Safe predicate (deriveAd pending)) (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (reserved : Safe predicate reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (presence : ∀ keyId, Safe predicate (present keyId)) (finish : Completion n (M source Platform) Encoded)
    (allowed : ∀ control initial, Safe predicate (finish control initial))
    (control : pqxdh.ServerState) (token : peer.ConsumedRegistration) (application : Slice U8)
    (pin : RustM (core.option.Option session.ServerAuthenticationPin)) :
    Safe predicate (RegistrationNativePlatformCompletionSdk.afterPin deriveAd reserve present finish control token application pin) := by
  unfold RegistrationNativePlatformCompletionSdk.afterPin
  cases pin with
  | fail error | div => exact pure_safe predicate _
  | ok optional => cases optional with
    | none => exact pure_safe predicate _
    | some pin =>
        simp only
        cases peer.begin_completion_lookup control pin token application with
        | fail error | div => exact pure_safe predicate _
        | ok result => cases result with
          | Err previous => exact pure_safe predicate _
          | Ok lookup =>
              simp only
              cases lookup.request with
              | fail error | div => exact pure_safe predicate _
              | ok keyId =>
                  simp only
                  split
                  · exact bind_safe predicate _ _ (presence keyId)
                      (fun occupied => afterOccupancy predicate deriveAd hashed reserve reserved finish allowed control lookup occupied)
                  · exact pure_safe predicate _

theorem complete
    (deriveAd : AdHash n (M source Platform))
    (hashed : ∀ pending, Safe predicate (deriveAd pending))
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (pinned : Safe predicate pin) (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (reserved : Safe predicate reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (presence : ∀ keyId, Safe predicate (present keyId)) (finish : Completion n (M source Platform) Encoded)
    (allowed : ∀ control initial, Safe predicate (finish control initial))
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    Safe predicate (RegistrationNativePlatformCompletionSdk.complete deriveAd pin reserve present finish token application) := by
  unfold RegistrationNativePlatformCompletionSdk.complete
  apply bind_safe predicate _ _ (get_safe predicate)
  intro before
  exact bind_safe predicate _ _ pinned
    (fun selected => afterPin predicate deriveAd hashed reserve reserved present presence finish allowed before.control token application selected)

theorem build
    (deriveAd : AdHash n (M source Platform))
    (hashed : ∀ pending, Safe predicate (deriveAd pending))
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (pinned : Safe predicate pin) (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (reserved : Safe predicate reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (presence : ∀ keyId, Safe predicate (present keyId)) (finish : Completion n (M source Platform) Encoded)
    (allowed : ∀ control initial, Safe predicate (finish control initial))
    (handle : Nat) (application : Option (Slice U8)) :
    Safe predicate (RegistrationNativePlatformCompletionSdk.build deriveAd pin reserve present finish handle application) := by
  intro before previous
  simp only [RegistrationNativePlatformCompletionSdk.build, StateT.run]
  cases taken : RegistrationServerSdkSource.take handle before with
  | mk selected current =>
      cases selected with
      | none => exact allQueriesSatisfy_pure _ _
      | some token => cases application with
        | none => exact allQueriesSatisfy_pure _ _
        | some application => exact complete predicate deriveAd hashed pin pinned reserve reserved present presence finish allowed token application current previous

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkQuerySafety

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkQuerySafety.get_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkQuerySafety.get_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkQuerySafety.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkQuerySafety.world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkQuerySafety.commit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkQuerySafety.commit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkQuerySafety.fromInitial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkQuerySafety.fromInitial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkQuerySafety.afterOccupancy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkQuerySafety.afterOccupancy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkQuerySafety.afterPin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkQuerySafety.afterPin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkQuerySafety.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkQuerySafety.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkQuerySafety.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkQuerySafety.build
