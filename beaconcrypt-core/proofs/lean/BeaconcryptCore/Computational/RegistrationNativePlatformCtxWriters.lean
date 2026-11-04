-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxLocal
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerService
/-! Source first-record and response writer bodies retain the same public platform state and full native request markers. All installation effects use the exact common Local/CTX lens. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxWriters
open BeaconcryptCore.Refinement
open RegistrationWorldAgreement (State)
open RegistrationNativePlatformCtxRunner (M Full interpret privateWork publicWork)
open RegistrationNativePlatformCtxLocal (realize attach)
variable {n : Nat} {Auxiliary Platform E : Type}

noncomputable def write (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (request : record_effects.RecordWriteRequest) :
    M (State n Auxiliary) Platform (RustM (core.option.Option (Slice U8))) := fun before previous =>
  (fun result => ((result.1, {before with recordRequests := before.recordRequests ++ [RegistrationWorldAgreement.recordCall (.write request)]}), result.2)) <$>
    simulateQ RegistrationNativePlatformCtxBackend.coin
      ((RegistrationNativePlatformSourceCompletion.writeWith helper request).run previous)

noncomputable def encode (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (view : registration.SignedResponseView) :
    M (State n Auxiliary) Platform (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  publicWork (RegistrationNativePlatformSourceCompletion.encodeWith writer view)

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let value ← work; pure (value, before)) := rfl

theorem write_source (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (request : record_effects.RecordWriteRequest)
    (before : Full (State n RegistrationServerRoleBackend.State) Platform) :
    Prod.map id realize <$> (interpret (write helper request)).run before =
      (RegistrationAgreementNestedState.flatten (RegistrationNativePlatformSourceBuild.write helper request)).run (realize before) := by
  unfold write RegistrationNativePlatformCtxRunner.interpret RegistrationAgreementNestedState.flatten RegistrationNativePlatformSourceBuild.write
  simp only [StateT.run, simulateQ_map, RegistrationNativePlatformCtxBackend.coins,
    state_map_apply, state_lift_apply, bind_pure_comp, Functor.map_map, realize, attach,
    RegistrationNativePlatformCtxCacheFrame.replace, Prod.map_def, id_eq]

theorem encode_source (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (view : registration.SignedResponseView)
    (before : Full (State n RegistrationServerRoleBackend.State) Platform) :
    Prod.map id realize <$> (interpret (encode writer view)).run before =
      (RegistrationAgreementNestedState.flatten (RegistrationNativePlatformSourceBuild.encode writer view)).run (realize before) := by
  rw [show encode writer view = publicWork (RegistrationNativePlatformSourceCompletion.encodeWith writer view) from rfl,
    RegistrationNativePlatformCtxRunner.public_run]
  simp only [RegistrationAgreementNestedState.flatten, RegistrationNativePlatformSourceBuild.encode,
    StateT.run, state_lift_apply, state_map_apply, bind_pure_comp, Functor.map_map, realize, Prod.map_def, id_eq]

theorem effects_source (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain)
    (before : Full (State n Auxiliary) Platform) :
    Prod.map id realize <$> (interpret (privateWork (RegistrationNativePlatformCtxLocal.effects query))).run before =
      (RegistrationAgreementNestedState.flatten
        (RegistrationNativePlatformPairedServerService.nativeEffects RegistrationNativePlatformMldsaProgram.coins query)).run (realize before) := by
  simpa only [RegistrationNativePlatformPairedServerService.nativeEffects,
    RegistrationNativePlatformServerCompletion.liftNative, RegistrationServerPublicationWorldCompiler.effect,
    RegistrationAgreementNestedState.flatten, StateT.run, RegistrationNativePlatformMldsaProgram.lift_coins,
    state_lift_apply, state_map_apply, bind_pure_comp, Functor.map_map, realize, attach, Prod.map_def, id_eq] using
    RegistrationNativePlatformCtxLocal.effects_source query before
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxWriters

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxWriters.write_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxWriters.write_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxWriters.encode_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxWriters.encode_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxWriters.effects_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxWriters.effects_source
