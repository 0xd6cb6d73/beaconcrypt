-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMap
import BeaconcryptCore.Computational.RegistrationStateView
/-! The actual effectful Init publication control preserves an idempotent state view when its individual crypto and writer leaves do. This follows the checked monadic interpretation of that same Core controller, retaining every optional/failure result and the ranked Ed loop. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationStateView
open RegistrationStateView (Stable)
variable {S Encoded : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

private abbrev Carrier (view : S → S) (m : Type → Type) [Monad m] (A : Type) :=
  { work : StateT S m A // Stable view work }
private abbrev carrierMonad (view : S → S) (idem : ∀ before, view (view before) = view before) : Monad (Carrier view m) where
  pure value := ⟨pure value, RegistrationStateView.pure_stable view idem value⟩
  bind work next := ⟨work.val >>= fun value => (next value).val,
    RegistrationStateView.bind_stable view _ _ work.property (fun value => (next value).property)⟩

/-- Individual actual operation laws compose through the literal effectful publication controller, including all later writer and source-resume branches. -/
theorem begin (view : S → S) (idem : ∀ before, view (view before) = view before)
    (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (StateT S m))
    (encode : registration.InitView → StateT S m (RustM (core.option.Option Encoded)))
    (leaves : ∀ query, Stable view (impl query)) (writer : ∀ packet, Stable view (encode packet))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :
    Stable view (RegistrationNativePlatformBeaconPublication.begin impl encode control inputs coins pin) := by
  let _ := carrierMonad (m := m) view idem
  let _ : LawfulMonad (Carrier view m) := LawfulMonad.mk' _
    (fun work => by apply Subtype.ext; exact bind_pure work.val)
    (fun value next => by apply Subtype.ext; exact pure_bind value (fun value => (next value).val))
    (fun work next rest => by apply Subtype.ext; exact bind_assoc work.val (fun value => (next value).val) (fun value => (rest value).val))
  let forget : ∀ {A : Type}, Carrier view m A → StateT S m A := fun {_} work => work.val
  have hom : Cslib.IsMonadHom (Carrier view m) (StateT S m) forget :=
    .mk' (fun _ => rfl) (fun _ _ => rfl)
  let operations : QueryImpl RegistrationBeaconInitExecutor.Spec (Carrier view m) := fun query => ⟨impl query, leaves query⟩
  let encoding : registration.InitView → Carrier view m (RustM (core.option.Option Encoded)) := fun packet => ⟨encode packet, writer packet⟩
  have kept := (RegistrationNativePlatformBeaconPublication.begin operations encoding control inputs coins pin).property
  change Stable view (forget (RegistrationNativePlatformBeaconPublication.begin operations encoding control inputs coins pin)) at kept
  rw [RegistrationNativePlatformBeaconMap.begin hom] at kept
  exact kept
end BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationStateView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationStateView.begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationStateView.begin
