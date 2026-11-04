-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxLocal
import BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialState
/-! The literal repeated Server pin hash and source capability leaves share the explicit CTX interpreter. Full counters, current Local/receipt state and public platform state are retained. -/
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

noncomputable def pin (current : session.ServerAuthenticationPin) :
    StateT (State n Auxiliary) (OracleComp Spec) RegistrationNativeServerPinRecompute.PinReply := do
  let digest ← RegistrationNativePlatformCtxLocal.effects (.inr (.hash (PqxdhRefinement.absBytes current.public_key)))
  pure (.ok (.Some ⟨current.binding, current.public_key, RegistrationAuthenticationShared.digestArray digest⟩))

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
  have source := RegistrationNativePlatformCtxLocal.effects_source
    (.inr (.hash (PqxdhRefinement.absBytes current.public_key))) before
  rw [RegistrationNativePlatformCtxRunner.private_run] at source ⊢
  have nativeRun := RegistrationNativeServerPinRecompute.native_run current.binding current.public_key (realize before).1.world.1
  simp only [StateT.run, realize, attach, replace] at nativeRun
  have mapped := congrArg (fun action => (fun (result : CtxRomAuth.CtxDigest ×
      (State n RegistrationServerRoleBackend.State × Platform)) =>
    ((.ok (.Some (⟨current.binding, current.public_key, RegistrationAuthenticationShared.digestArray result.1⟩ : session.ServerAuthenticationPin)) : RegistrationNativeServerPinRecompute.PinReply), result.2)) <$> action) source
  simpa only [pin, RegistrationNativePlatformServerMaterialState.pin,
    nativeRun, RegistrationAgreementNestedState.flatten,
    StateT.run, state_bind_apply, state_pure_apply, bind_pure_comp, simulateQ_map,
    RegistrationNativePlatformMldsaProgram.lift_coins, state_map_apply, state_lift_apply,
    Functor.map_map, realize, attach, replace, Prod.map_def, id_eq] using mapped
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
