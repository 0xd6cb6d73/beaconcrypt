-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxLocal
import BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialState
/-! Pure Server pin selection and actual source capability leaves share the explicit CTX interpreter. Pin selection performs no primitive query; capability operations retain full counters, current Local/receipt state and public platform state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxPin
open RegistrationWorldAgreement (State)
open RegistrationNativePlatformCtxBackend (Spec)
open RegistrationNativePlatformCtxRunner (Full interpret privateWork)
open RegistrationNativePlatformCtxLocal (realize attach)
open RegistrationNativePlatformCtxCacheFrame (replace)
variable {n : Nat} {Auxiliary Platform : Type}

def pin (current : session.ServerAuthenticationPin) :
    StateT (State n Auxiliary) (OracleComp Spec) RegistrationNativeServerPinRecompute.PinReply :=
  pure (.ok (.Some current))

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let value ← work; pure (value, before)) := rfl

private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let reply ← work before; next reply.1 reply.2) := rfl

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) :
    (pure value : StateT S m X) before = pure (value, before) := rfl

theorem pin_source (current : session.ServerAuthenticationPin)
    (before : Full (State n RegistrationServerRoleBackend.State) Platform) :
    Prod.map id realize <$> (interpret (privateWork (pin current))).run before =
      (RegistrationAgreementNestedState.flatten
        (RegistrationNativePlatformServerMaterialState.pin RegistrationNativePlatformMldsaProgram.coins current)).run (realize before) := by
  rw [RegistrationNativePlatformCtxRunner.private_run]
  simp only [pin, RegistrationNativePlatformServerMaterialState.pin,
    RegistrationAgreementNestedState.flatten, StateT.run, state_pure_apply,
    simulateQ_pure, map_pure, RegistrationNativePlatformMldsaProgram.lift_coins,
    state_map_apply, state_lift_apply, bind_pure_comp,
    Functor.map_map, realize, attach, replace, Prod.map_def, id_eq]
  rw [show RegistrationNativeServerPinRecompute.native (n := n) current.binding current.public_key = pure (.ok (.Some current)) from by cases current; rfl]
  rfl

theorem capability_source (query : (PqxdhRecordLiftInterface.CapabilitySpec n).Domain)
    (before : Full (State n Auxiliary) Platform) :
    Prod.map id realize <$> (interpret (privateWork (RegistrationNativePlatformCtxLocal.effects (.inr query)))).run before =
      (RegistrationAgreementNestedState.flatten
        (RegistrationNativePlatformServerCompletion.capability RegistrationNativePlatformMldsaProgram.coins query)).run (realize before) := by
  simpa only [RegistrationNativePlatformServerCompletion.capability,
    RegistrationNativePlatformServerCompletion.liftNative, RegistrationWorldServerCompletion.capability,
    RegistrationAgreementNestedState.flatten, StateT.run, RegistrationNativePlatformMldsaProgram.lift_coins,
    state_lift_apply, state_map_apply, bind_pure_comp, Functor.map_map, realize, attach, Prod.map_def, id_eq] using
    RegistrationNativePlatformCtxLocal.effects_source (.inr query) before
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxPin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxPin.pin_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxPin.pin_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxPin.capability_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxPin.capability_source
