-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconComplete
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinishCut
import BeaconcryptCore.Computational.RegistrationNativeInstallFreePreparation
import BeaconcryptCore.Computational.RegistrationNativeTypedBeaconAllController

/-! The original native terminal finish has one successful installation in its own role exactly when its actual public Option reply succeeds. Preparation and all terminal aborts preserve the per-role descriptor prefix, including ordinary-owner translation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconFinish
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeInstallOrdinals (messages)
open RegistrationNativeInstallBeaconComplete (present)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeG2Trace (State handler)
variable {n : Nat} {ι KemSK Auxiliary Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

noncomputable def compile (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value) :=
  RegistrationNativeInstallBeaconComplete.compile (RegistrationNativeTypedBeaconAllController.translated setup scalar work)

private theorem compile_pure (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes) (value : Value) :
    compile (n := n) setup scalar (pure value) = pure value := by
  cases scalar <;> simp only [compile, RegistrationNativeTypedBeaconAllController.translated,
    RegistrationNativeInstallBeaconComplete.compile, simulateQ_pure]

private theorem compile_bind (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value)
    (next : Value → OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Next) :
    compile setup scalar (work >>= next) = (compile setup scalar work >>= fun value => compile setup scalar (next value)) := by
  cases scalar <;> simp only [compile, RegistrationNativeTypedBeaconAllController.translated,
    RegistrationNativeInstallBeaconComplete.compile, simulateQ_bind]

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before


private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work) before = (fun value => (value, before)) <$> work := by
  change (work >>= fun value => pure (value, before)) = _
  rw [bind_pure_comp]

private theorem abort (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (owner current : SelectedOwner source) (env : EnvState Auxiliary) (value : RustM (Option Pqxdh.Bytes))
    (before : State) (result : ((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary) × State)
    (supported : result ∈ support ((simulateQ handler (compile (n := n) setup scalar
      (((RegistrationNativePlatformBeaconMaterialFrontend.abort RegistrationBeaconReferenceCompiler.effect owner *> pure value).run current).run env))).run before)) :
    result.1.1.1 = value ∧ result.2 = before := by
  cases scalar <;>
    simp only [compile, RegistrationNativeTypedBeaconAllController.translated, RegistrationNativePlatformBeaconMaterialFrontend.abort,
      seqRight_eq_bind, bind_pure_comp, StateT.run, map_apply, lift_apply,
      RegistrationNativeInstallBeaconComplete.compile, simulateQ_map, Functor.map_map,
      RegistrationBeaconReferenceCompiler.effect, RegistrationNativePublicOwners.ordinary,
      RegistrationNativePublicFrontend.liftLocal, simulateQ_spec_query, handler,
      RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish, map_apply, Functor.map_map, Prod.map_def, id_eq, support_map] at supported
  all_goals
    obtain ⟨reached, called, equal⟩ := supported
    cases equal
    constructor
    · rfl
    · rfl

attribute [local irreducible] RegistrationBeaconReferenceCompiler.finishPreparation RegistrationBeaconReferenceFinish.complete

/-- Every actual native finish has precisely the successful public handle's own-role installation suffix. -/
theorem finish (role : Role) (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner source) (env : EnvState RegistrationServerRoleBackend.State) (packet : Option registration.ResponsePacket) (before : State)
    (result : ((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState RegistrationServerRoleBackend.State) × State)
    (supported : result ∈ support ((simulateQ handler (compile (n := n) setup scalar
      (((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner).run env))).run before)) :
    ∃ delta, messages role result.2.events = messages role before.events ++ delta ∧
      delta.length = if role = .beacon ∧ present result.1.1.1 = true then 1 else 0 := by
  rw [RegistrationNativePlatformBeaconFinishCut.factor] at supported
  cases phase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ =>
      simp only [phase, StateT.run_pure, compile_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact ⟨[], by simp only [List.append_nil], by simp [present]⟩
  | initSent pending oneTime =>
      simp only [phase] at supported
      cases moved : pending.aborted_state with
      | fail error | div =>
          simp only [moved, StateT.run_pure, compile_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
          subst result
          exact ⟨[], by simp only [List.append_nil], by simp [present]⟩
      | ok aborted =>
          rw [moved] at supported
          simp only [StateT.run_bind, compile_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
          obtain ⟨prepared, possible, continued⟩ := supported
          have noInstall := RegistrationNativeInstallFreePreparation.preparation_free (n := n) role setup source packet owner env
          have bound : (compile setup scalar (((RegistrationBeaconReferenceCompiler.finishPreparation (n := n) setup source packet).run owner).run env)).IsQueryBoundP
              (RegistrationNativeInstallPredicate.GlobalInstall (KemSK := KemSK) role) 0 := by
            cases scalar with
            | none => exact RegistrationNativeInstallRouting.local_bound role false _ 0 noInstall
            | some scalar =>
                exact RegistrationNativeInstallRouting.local_bound role false _ 0
                  (RegistrationNativeInstallRouting.ordinary_bound role setup scalar _ 0 noInstall)
          have prefixEq := RegistrationNativeInstallTrace.free role _ bound before prepared possible
          cases outcome : prepared.1.1.1 with
          | fail error | div =>
              simp only [outcome, RegistrationNativePlatformBeaconContinuation.afterPrepared] at continued
              have ended := abort setup scalar owner prepared.1.1.2 prepared.1.2 _ prepared.2 result continued
              refine ⟨[], ?_, ?_⟩
              · rw [ended.2, prefixEq, List.append_nil]
              · rw [ended.1]; simp [present]
          | ok preparedValue => cases preparedValue with
            | none =>
                simp only [outcome, RegistrationNativePlatformBeaconContinuation.afterPrepared] at continued
                have ended := abort setup scalar owner prepared.1.1.2 prepared.1.2 (.ok none) prepared.2 result continued
                refine ⟨[], ?_, ?_⟩
                · rw [ended.2, prefixEq, List.append_nil]
                · rw [ended.1]; simp [present]
            | some ready =>
                have completed : result ∈ support ((simulateQ handler (RegistrationNativePlatformInstallBeaconComplete.compile (n := n) (KemSK := KemSK)
                  (((RegistrationNativePlatformBeaconMaterialFrontend.complete (n := n) setup.source wire.frameWrite RegistrationBeaconReferenceCompiler.effect RegistrationNativePlatformBeaconMaterialInterpreter.demand owner ready).run prepared.1.1.2).run prepared.1.2))).run prepared.2) := by
                  cases scalar <;> simpa only [outcome, RegistrationNativePlatformBeaconContinuation.afterPrepared, compile, RegistrationNativeTypedBeaconAllController.translated,
                    RegistrationNativeInstallBeaconComplete.compile, RegistrationNativePlatformInstallBeaconComplete.compile, RegistrationNativePlatformBeaconFinishCut.ordinary_complete] using continued
                have bill := RegistrationNativePlatformInstallBeaconComplete.complete_all role setup.source wire.frameWrite owner prepared.1.1.2 ready prepared.1.2 prepared.2 result completed
                refine ⟨if role = .beacon ∧ present result.1.1.1 = true then [ready.reference] else [], ?_, ?_⟩
                · rw [bill, prefixEq]
                · split <;> rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconFinish.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconFinish.finish
