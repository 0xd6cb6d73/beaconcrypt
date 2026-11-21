-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSyntax
/-! Every ongoing public record route is the actual stateful source-writer runtime operation. Failed publication retains the exact advanced private World and P; the named output view removes instrumentation only. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordNative
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicSourceState (project restore nativeView)
open RegistrationNativePlatformPublicSourceExecution (State execute)
open RegistrationNativePlatformOrdinaryExperiment (canonicalWire)
open RegistrationServerReferenceRestore (Roots)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let value ← work; pure (value, before)) := rfl

private theorem lift_run (work : StateT (RegistrationNativeExperiment.State n KemSK source) ProbComp A)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform) :
    ((RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins work).run before).run previous =
      (fun result => (result, previous)) <$> work.run before := by
  simp only [RegistrationNativePlatformExperiment.liftNative, StateT.run,
    RegistrationNativePlatformMldsaProgram.lift_coins, lift_apply, bind_pure_comp]

private theorem mapped_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem after_run (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : StateT (RegistrationNativeExperiment.State n KemSK source) ProbComp (Option RawCtxSourceSend.Encrypted))
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform) :
    ((RegistrationNativePlatformOrdinaryExperimentRouting.after reserve
      (RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins work)).run before).run previous = (do
      let result ← work.run before
      let allowed ← (RegistrationNativePlatformOrdinaryGate.gate reserve (fun value => value.ciphertext.length) result.1).run previous
      pure ((allowed.1, result.2), allowed.2)) := by
  unfold RegistrationNativePlatformOrdinaryExperimentRouting.after
  rw [StateT.run_bind, StateT.run_bind, lift_run]
  simp only [bind_map_left, lift_apply, bind_pure_comp, StateT.run, mapped_apply, Prod.map_def, id_eq]

/-- All four actual source record routes share the same native private execution and public platform state, with literal failed-writer and absent-owner behavior. -/
theorem record (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (roots : Roots)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State n KemSK Platform source) :
    (fun result => ((result.1, project roots scalar result.2.1.1 result.2.2), result.2.1.2)) <$>
      (execute setup (canonicalWire wire) route sign seed scalar
        (RegistrationNativePlatformPublicFrontend.record reserve query)).run before =
      (fun result => ((result.1.1, nativeView result.1.2), result.2)) <$>
        ((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route query source).run
          (restore roots scalar before.1.1 before.2)).run before.1.2 := by
  cases query with
  | inl query => cases query with
    | inl send =>
      rcases send with ⟨plaintext, keyId⟩
      rw [RegistrationNativePlatformPublicRecordSyntax.server_send,
        RegistrationNativePlatformOrdinaryExperimentRouting.server_send, after_run]
      have actual := RegistrationNativePlatformPublicRecordSource.server_gated setup (canonicalWire wire) route sign seed scalar roots reserve keyId plaintext before
      simp only [map_bind, map_pure]
      convert actual using 1 <;> rfl
    | inr raw =>
      rw [RegistrationNativePlatformPublicRecordSyntax.server_raw,
        RegistrationNativePlatformOrdinaryExperimentRouting.server_raw, lift_run, Functor.map_map]
      exact RegistrationNativePlatformPublicRecordSource.old_record setup (canonicalWire wire) route sign seed scalar roots (.inl (.inr raw)) before
  | inr query =>
    rcases query with ⟨index, request⟩
    cases request with
    | inl plaintext =>
      rw [RegistrationNativePlatformPublicRecordSyntax.beacon_send,
        RegistrationNativePlatformOrdinaryExperimentRouting.beacon_send, after_run]
      have actual := RegistrationNativePlatformPublicRecordSource.beacon_gated setup (canonicalWire wire) route sign seed scalar roots reserve index plaintext before
      simp only [map_bind, map_pure]
      convert actual using 1 <;> rfl
    | inr raw =>
      rw [RegistrationNativePlatformPublicRecordSyntax.beacon_raw,
        RegistrationNativePlatformOrdinaryExperimentRouting.beacon_raw, lift_run, Functor.map_map]
      exact RegistrationNativePlatformPublicRecordSource.old_record setup (canonicalWire wire) route sign seed scalar roots (.inr (index, .inr raw)) before
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordNative

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordNative.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordNative.record
