-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingFold

/-! The actual outgoing hash callback exposes exactly its literal input before any physical lookup. The remaining Main update depends only on the returned digest/draw bill, retains all source fields and P, and increments the real effect/coin counters. This gives a current-query coupling interface without a whole handler or counter-erasure premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashOutgoing
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
variable {n : Nat} {I KemSK Platform : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def updated (draws : Nat) (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :=
  let charged := PqxdhRecordLiftWorld.chargeEffect (.inr (.hash [])) before.1.context.server.world.world.1
  let world := { charged with primitive :=
    ({ charged.primitive.1 with uniform := charged.primitive.1.uniform + draws }, charged.primitive.2) }
  ({ before.1 with context := { before.1.context with server := { before.1.context.server with
    world := { before.1.context.server.world with world := (world, before.1.context.server.world.world.2) } } } }, before.2)

private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (do let value ← work; pure (value, before)) = _
  rw [bind_pure_comp]
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

/-- Full true-counter source normalization of the actual current hash leaf. -/
theorem outgoing (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (request : registration.HashRequest) (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (RegistrationNativePlatformIdentityProgram.native
        (RegistrationNativeIdentityFrontend.hash (n := n) (KemSK := KemSK) (Auxiliary := RegistrationServerRoleBackend.State) (source := source) request))).run before = (do
      let reply ← (Spec.query (.inr (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request)) : OracleComp Spec (CtxRomAuth.CtxDigest × Nat))
      pure (reply.1, updated reply.2 before)) := by
  rw [RegistrationNativePlatformIdentityCtxOutgoingFold.run]
  simp only [RegistrationNativePlatformIdentityProgram.native, RegistrationNativeIdentityFrontend.hash,
    RegistrationNativeIdentityFrontend.effect, StateT.run, lift_apply, map_apply, simulateQ_map, Functor.map_map,
    RegistrationNativePlatformIdentityProgram.nativeLift, simulateQ_spec_query,
    RegistrationNativePlatformIdentityCtxCompiler.free, RegistrationNativePlatformIdentityCtxCompiler.implementation,
    RegistrationNativePlatformIdentityCtxAmbient.program, RegistrationNativePlatformIdentityCtxAmbient.world,
    RegistrationNativePlatformCtxEffects.program, RegistrationNativePlatformCtxBackend.hash,
    RegistrationNativePlatformIdentityCtxCompiler.backend, simulateQ_bind, simulateQ_pure, map_bind, map_pure]
  apply bind_congr
  intro reply
  simp only [RegistrationNativePlatformIdentityCtxOutgoingFold.close, RegistrationNativePlatformIdentityCtxEnvPatch.patch,
    Prod.map, id_eq, updated, PqxdhRecordLiftWorld.chargeEffect, RegistrationWorldAgreementCompiler.erase,
    RegistrationWorldAgreementCompiler.join]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashOutgoing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashOutgoing.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashOutgoing.outgoing
