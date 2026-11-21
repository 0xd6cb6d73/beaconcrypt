-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication
import Cslib.Foundations.Control.Monad.IsMonadHom

/-! The complete actual Core Init publication controller commutes with any lawful monadic interpretation. This algebra retains every source gate, Ed-loop rank, optional reply and effectful writer continuation and is used to thread native and external platform states together. It is not a protocol-security or source-wrapper premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMap
open RegistrationNativePlatformBeaconPublication
open RegistrationBeaconInitExecutor (Spec Result edRank ed_rank)
variable {left right : Type → Type} [Monad left] [Monad right]
variable {F : ∀ {Value : Type}, left Value → right Value}
variable (hom : Cslib.IsMonadHom left right F)
include hom
variable {Encoded : Type}

private theorem continueWith_hom {Input : Type} (action : RustM Input)
    (next : Input → left (RustM (Result Encoded))) :
    F (continueWith action next) = continueWith action (fun value => F (next value)) := by
  cases action <;> first | rfl | exact hom.map_pure _

theorem ready (encode : registration.InitView → left (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconInitReady) :
    F (RegistrationNativePlatformBeaconPublication.ready encode pending) =
      RegistrationNativePlatformBeaconPublication.ready (fun view => F (encode view)) pending := by
  unfold RegistrationNativePlatformBeaconPublication.ready
  rw [continueWith_hom hom]
  apply congrArg (continueWith pending.message)
  funext view
  rw [hom.map_bind]
  apply bind_congr
  intro encoded
  exact hom.map_pure _
theorem hash (impl : QueryImpl Spec left)
    (encode : registration.InitView → left (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconInitHash) :
    F (fromHash impl encode pending) =
      fromHash (fun query => F (impl query)) (fun view => F (encode view)) pending := by
  unfold fromHash
  rw [continueWith_hom hom]
  apply congrArg (continueWith pending.request)
  funext request
  rw [hom.map_bind]
  apply bind_congr
  intro digest
  rw [continueWith_hom hom]
  apply congrArg (continueWith (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))))
  funext effect
  cases effect <;> first | exact ready hom encode _ | exact hom.map_pure _
theorem ed (impl : QueryImpl Spec left)
    (encode : registration.InitView → left (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconEd25519Signing) :
    F (fromEd impl encode pending) =
      fromEd (fun query => F (impl query)) (fun view => F (encode view)) pending := by
  rw [fromEd.eq_def, fromEd.eq_def]
  rw [continueWith_hom hom]
  apply congrArg (continueWith pending.request)
  funext request
  rw [hom.map_bind]
  apply bind_congr
  intro reply
  cases resumed : pending.resume reply with
  | fail error => exact hom.map_pure _
  | div => exact hom.map_pure _
  | ok effect =>
    cases effect with
    | Ed25519SigningRequested next => exact ed impl encode next
    | HashRequested next => exact hash hom impl encode next
    | _ => exact hom.map_pure _
termination_by edRank pending
decreasing_by exact ed_rank pending reply next resumed

theorem begin (impl : QueryImpl Spec left)
    (encode : registration.InitView → left (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :
    F (RegistrationNativePlatformBeaconPublication.begin impl encode control inputs coins pin) =
      RegistrationNativePlatformBeaconPublication.begin (fun query => F (impl query))
        (fun view => F (encode view)) control inputs coins pin := by
  unfold RegistrationNativePlatformBeaconPublication.begin
  rw [continueWith_hom hom]
  apply congrArg (continueWith (registration.begin_beacon_init control inputs coins pin))
  funext effect
  cases effect <;> first | exact ed hom impl encode _ | exact hom.map_pure _
end BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMap.ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMap.ready


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMap.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMap.hash


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMap.ed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMap.ed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMap.begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMap.begin
