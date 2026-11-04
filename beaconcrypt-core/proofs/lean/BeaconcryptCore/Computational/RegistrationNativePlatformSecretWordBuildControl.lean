-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpen
import BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendProgram
import Cslib.Foundations.Control.Monad.IsMonadHom
/-! Symbolic one-use Server build follows the corrected four-leaf source controller. It retains moved handles, cancellation, repeated pin hashing, occupancy, effectful reservation and every source failure. The representation theorem uses only equality of the individual admitted service call; the concrete checked service dictionary is instantiated separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildControl
open RegistrationNativeSecretWordMessage (Message ServerReady ServerState)
open RegistrationNativePlatformServerMaterialFrontend (Result)
variable {m : Type → Type} [Monad m] [LawfulMonad m] {Encoded : Type}

abbrev Service (m : Type → Type) (Encoded : Type) := pqxdh.ServerState →
  RegistrationBoundKeySchedule.PublicInitial → Message → m (RustM (RegistrationHiddenInstall.Result Encoded))

def finish (result : RustM (RegistrationHiddenInstall.Result Encoded)) (before : ServerState) : Result Encoded × ServerState :=
  match result with
  | .fail error => (.fail error, before)
  | .div => (.div, before)
  | .ok (.Err previous) => (.ok none, { before with control := previous })
  | .ok (.Ok published) => (.ok (some (published.key_id, published.encoded)), { before with control := published.control })

def afterResult (reserve : m Bool) (service : Service m Encoded) (control : pqxdh.ServerState)
    (reference : Message)
    (result : RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState)) :
    StateT ServerState m (Result Encoded) :=
  match result with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok selected) => do
      let admitted ← StateT.lift reserve
      if admitted then do
        let published ← StateT.lift (service control selected reference)
        fun before => pure (finish published before)
      else pure (.ok none)

def afterOccupancy (reserve : m Bool) (service : Service m Encoded) (control : pqxdh.ServerState)
    (lookup : peer.CompletionLookup) (reference : Message) (occupied : Bool) :
    StateT ServerState m (Result Encoded) :=
  afterResult reserve service control reference
    (RegistrationPublicationKernelErasure.mapOk RegistrationBoundKeySchedule.publicInitial <$> lookup.resume occupied)

def afterPin (reserve : m Bool) (present : U64 → m Bool) (service : Service m Encoded)
    (control : pqxdh.ServerState) (ready : ServerReady) (application : Slice U8)
    (current : RustM (core.option.Option session.ServerAuthenticationPin)) : StateT ServerState m (Result Encoded) := fun before =>
  match current with
  | .fail error => pure (.fail error, before)
  | .div => pure (.div, before)
  | .ok .None => pure (.ok none, before)
  | .ok (.Some pin) => match peer.begin_completion_lookup control pin (RegistrationNativeSecretWordServerMaterial.token ready) application with
    | .fail error => pure (.fail error, before)
    | .div => pure (.div, before)
    | .ok (.Err _) => pure (.ok none, before)
    | .ok (.Ok lookup) => match lookup.request with
      | .fail error => pure (.fail error, before)
      | .div => pure (.div, before)
      | .ok keyId => if RegistrationServerSdkSource.preflight application keyId then do
          let occupied ← present keyId
          (afterOccupancy reserve service control lookup ready.reference occupied).run before
        else pure (.ok none, before)

def complete (pin : session.ServerAuthenticationPin → m (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : m Bool) (present : U64 → m Bool) (service : Service m Encoded)
    (ready : ServerReady) (application : Slice U8) : StateT ServerState m (Result Encoded) := fun before => do
  let current ← pin before.pin
  (afterPin reserve present service before.control ready application current).run before

def build (pin : session.ServerAuthenticationPin → m (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : m Bool) (present : U64 → m Bool) (service : Service m Encoded)
    (handle : Nat) (application : Option (Slice U8)) : StateT ServerState m (Result Encoded) := fun before =>
  match RegistrationNativeSecretWordServerMaterial.take handle before with
  | (none, current) => pure (.ok none, current)
  | (some ready, current) => match application with
    | none => pure (.ok none, current)
    | some application => (complete pin reserve present service ready application).run current

variable (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (pin : session.ServerAuthenticationPin → m (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : m Bool) (present : U64 → m Bool)
    (nativeService : RegistrationNativePlatformServerMaterialFrontend.Service m Encoded) (wordService : Service m Encoded)
    (service_source : ∀ control initial (message : Message),
      nativeService control initial (RegistrationNativeSecretWordMessage.eval candidate message) = wordService control initial message)

/-- Returned control and output bytes are independent of the root-reference representation. -/
theorem finish_source (result : RustM (RegistrationHiddenInstall.Result Encoded)) (before : ServerState) :
    Prod.map id (ServerState.eval candidate) (finish result before) =
      RegistrationNativePlatformServerMaterialFrontend.finish result (before.eval candidate) := by
  cases result with
  | fail error | div => rfl
  | ok result => cases result <;> rfl

include service_source in
private theorem afterResult_source (control : pqxdh.ServerState) (reference : Message)
    (result : RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState))
    (before : ServerState) :
    (RegistrationNativePlatformServerMaterialFrontend.afterResult reserve nativeService control (RegistrationNativeSecretWordMessage.eval candidate reference) result).run (before.eval candidate) =
      Prod.map id (ServerState.eval candidate) <$> (afterResult reserve wordService control reference result).run before := by
  cases result with
  | fail error | div => simp only [RegistrationNativePlatformServerMaterialFrontend.afterResult, afterResult, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | ok result => cases result with
    | Err previous => simp only [RegistrationNativePlatformServerMaterialFrontend.afterResult, afterResult, StateT.run_pure, map_pure, Prod.map_def, id_eq]
    | Ok selected =>
      simp only [RegistrationNativePlatformServerMaterialFrontend.afterResult, afterResult, StateT.run_bind,
        StateT.run_lift, bind_pure_comp, bind_map_left, map_bind]
      apply bind_congr
      intro admitted
      cases admitted with
      | false => simp only [Bool.false_eq_true, ite_false, StateT.run_pure, map_pure, Prod.map_def, id_eq]
      | true =>
        simp only [ite_true, StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left, map_bind]
        rw [service_source]
        apply bind_congr
        intro result
        simpa only [StateT.run, map_pure] using congrArg (fun value => (pure value : m _)) (finish_source candidate result before).symm

include service_source in
private theorem afterPin_source (control : pqxdh.ServerState) (ready : ServerReady) (application : Slice U8)
    (current : RustM (core.option.Option session.ServerAuthenticationPin)) (before : ServerState) :
    (RegistrationNativePlatformServerMaterialFrontend.afterPin reserve present nativeService control
      (ready.eval candidate) application current).run (before.eval candidate) =
      Prod.map id (ServerState.eval candidate) <$> (afterPin reserve present wordService control ready application current).run before := by
  cases current with
  | fail error | div => simp only [RegistrationNativePlatformServerMaterialFrontend.afterPin, afterPin, StateT.run, map_pure, Prod.map_def, id_eq]
  | ok current => cases current with
    | none => simp only [RegistrationNativePlatformServerMaterialFrontend.afterPin, afterPin, StateT.run, map_pure, Prod.map_def, id_eq]
    | some current =>
      unfold RegistrationNativePlatformServerMaterialFrontend.afterPin afterPin
      simp only [RegistrationNativeSecretWordServerMaterial.token_eval]
      dsimp only [StateT.run]
      cases peer.begin_completion_lookup control current (RegistrationNativeSecretWordServerMaterial.token ready) application with
      | fail error | div => simp only [map_pure, Prod.map_def, id_eq]
      | ok lookup => cases lookup with
        | Err previous => simp only [map_pure, Prod.map_def, id_eq]
        | Ok lookup =>
          cases requested : lookup.request with
          | fail error | div => simp only [requested, map_pure, Prod.map_def, id_eq]
          | ok keyId =>
            simp only [requested]
            by_cases fits : RegistrationServerSdkSource.preflight application keyId = true
            · simp only [fits, ite_true, map_bind]
              apply bind_congr
              intro occupied
              exact afterResult_source candidate reserve nativeService wordService service_source control ready.reference _ before
            · simp only [fits, Bool.false_eq_true, ite_false, map_pure, Prod.map_def, id_eq]

include service_source in
/-- The corrected moved-token build commutes with reference evaluation under its individual admitted service relation; cancellation and every failure retain the exact source state. -/
theorem build_source (handle : Nat) (application : Option (Slice U8)) (before : ServerState) :
    (RegistrationNativePlatformServerMaterialFrontend.build pin reserve present nativeService handle application).run (before.eval candidate) =
      Prod.map id (ServerState.eval candidate) <$> (build pin reserve present wordService handle application).run before := by
  have moved := RegistrationNativeSecretWordServerMaterial.take_eval candidate handle before
  simp only [RegistrationNativePlatformServerMaterialFrontend.build, build, StateT.run]
  rcases actual : RegistrationNativeSecretWordServerMaterial.take handle before with ⟨selected, current⟩
  rw [actual] at moved
  rw [← moved]
  cases selected with
  | none => simp only [Prod.map, Option.map_none, map_pure, id_eq]
  | some ready => cases application with
    | none => simp only [Prod.map, Option.map_some, map_pure, id_eq]
    | some application =>
      simp only [Prod.map, Option.map_some, RegistrationNativePlatformServerMaterialFrontend.complete, complete,
        map_bind, ServerState.eval]
      apply bind_congr
      intro pinReply
      exact afterPin_source candidate reserve present nativeService wordService service_source current.control ready application pinReply current

section Mapping
variable {k : Type → Type} [Monad k] [LawfulMonad k]
    {F : ∀ {A : Type}, m A → k A} (hom : Cslib.IsMonadHom m k F)
include hom

private theorem map_afterResult (control : pqxdh.ServerState) (reference : Message)
    (action : RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState))
    (before : ServerState) :
    F ((afterResult reserve wordService control reference action).run before) =
      (afterResult (F reserve) (fun control initial message => F (wordService control initial message))
        control reference action).run before := by
  cases action with
  | fail error | div => exact hom.map_pure _
  | ok answer => cases answer with
    | Err previous => exact hom.map_pure _
    | Ok selected =>
      simp only [afterResult, StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left]
      rw [hom.map_bind]
      apply bind_congr
      intro admitted
      cases admitted with
      | false => exact hom.map_pure _
      | true =>
        simp only [ite_true, StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left]
        rw [hom.map_bind]
        apply bind_congr
        intro result
        exact hom.map_pure _

private theorem map_afterPin (control : pqxdh.ServerState) (ready : ServerReady) (application : Slice U8)
    (current : RustM (core.option.Option session.ServerAuthenticationPin)) (before : ServerState) :
    F ((afterPin reserve present wordService control ready application current).run before) =
      (afterPin (F reserve) (fun keyId => F (present keyId))
        (fun control initial message => F (wordService control initial message)) control ready application current).run before := by
  cases current with
  | fail error | div => exact hom.map_pure _
  | ok current => cases current with
    | none => exact hom.map_pure _
    | some current =>
      unfold afterPin
      dsimp only [StateT.run]
      cases peer.begin_completion_lookup control current (RegistrationNativeSecretWordServerMaterial.token ready) application with
      | fail error | div => exact hom.map_pure _
      | ok lookup => cases lookup with
        | Err previous => exact hom.map_pure _
        | Ok lookup =>
          cases requested : lookup.request with
          | fail error | div => simp only [requested]; exact hom.map_pure _
          | ok keyId =>
            simp only [requested]
            by_cases fits : RegistrationServerSdkSource.preflight application keyId = true
            · simp only [fits, ite_true]
              rw [hom.map_bind]
              apply bind_congr
              intro occupied
              exact map_afterResult reserve wordService hom control ready.reference _ before
            · simp only [fits, Bool.false_eq_true, ite_false]
              exact hom.map_pure _

/-- The corrected symbolic controller commutes with any monad homomorphism, preserving the returned one-use state and every leaf's complete effects. -/
theorem map_build (handle : Nat) (application : Option (Slice U8)) (before : ServerState) :
    F ((build pin reserve present wordService handle application).run before) =
      (build (fun current => F (pin current)) (F reserve) (fun keyId => F (present keyId))
        (fun control initial message => F (wordService control initial message)) handle application).run before := by
  simp only [build, StateT.run]
  rcases RegistrationNativeSecretWordServerMaterial.take handle before with ⟨selected, current⟩
  cases selected with
  | none => exact hom.map_pure _
  | some ready => cases application with
    | none => exact hom.map_pure _
    | some application =>
      simp only [complete, StateT.run]
      rw [hom.map_bind]
      apply bind_congr
      intro pinReply
      exact map_afterPin reserve present wordService hom current.control ready application pinReply current
end Mapping

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildControl

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildControl.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildControl.finish_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildControl.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildControl.build_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildControl.map_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildControl.map_build
