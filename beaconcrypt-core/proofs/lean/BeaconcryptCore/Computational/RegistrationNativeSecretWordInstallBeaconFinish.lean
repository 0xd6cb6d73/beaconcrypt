-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBeaconComplete
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerInstallPrefix
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerSource

/-! The original native terminal finish has one successful installation in its own role exactly when its actual public Option reply succeeds. Preparation and all terminal aborts preserve the per-role descriptor prefix, including ordinary-owner translation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBeaconFinish
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeSecretWordInstallOrdinals (messages)
open RegistrationNativeInstallBeaconComplete (present)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordFrontendTrace (State handler)
variable {n : Nat} {ι KemSK Auxiliary Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

noncomputable def compile (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) Value) :=
  simulateQ (RegistrationNativeSecretWordAtomOwnerSource.routing setup scalar) work

private theorem compile_pure (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes) (value : Value) :
    compile (n := n) setup scalar (pure value) = pure value := by
  simp only [compile, simulateQ_pure]

private theorem compile_bind (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) Value)
    (next : Value → OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) Next) :
    compile setup scalar (work >>= next) = (compile setup scalar work >>= fun value => compile setup scalar (next value)) := by
  simp only [compile, simulateQ_bind]

private theorem routing_paired (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativeSecretWordBeaconMaterial.Spec n) Value) :
    compile setup scalar (simulateQ RegistrationNativeSecretWordInterface.paired work) =
      RegistrationNativeSecretWordInstallBeaconComplete.compile (KemSK := KemSK) work := by
  unfold compile RegistrationNativeSecretWordInstallBeaconComplete.compile
  cases scalar with
  | none => rfl
  | some scalar =>
      simp only [RegistrationNativeSecretWordAtomOwnerSource.routing, QueryImpl.simulateQ_compose]
      congr 1
      rw [← QueryImpl.simulateQ_compose]
      rfl

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
      (((RegistrationNativeSecretWordBeaconCompiler.abort owner *> pure value).run current).run env))).run before)) :
    result.1.1.1 = value ∧ result.2 = before := by
  cases scalar <;>
    simp only [compile, RegistrationNativeSecretWordAtomOwnerSource.routing, RegistrationNativeSecretWordBeaconCompiler.abort,
      seqRight_eq_bind, bind_pure_comp, StateT.run, map_apply, lift_apply,
      simulateQ_map, Functor.map_map,
      RegistrationNativeSecretWordInterface.effect, QueryImpl.compose, RegistrationNativeSecretWordOwners.ordinary,
      RegistrationNativeSecretWordInterface.liftLocal, simulateQ_spec_query, handler,
      RegistrationNativeSecretWordFrontendTrace.begin, RegistrationNativeSecretWordFrontendTrace.finish, map_apply, Functor.map_map, Prod.map_def, id_eq, support_map] at supported
  all_goals
    obtain ⟨reached, called, equal⟩ := supported
    cases equal
    constructor
    · rfl
    · rfl

attribute [local irreducible] RegistrationNativeSecretWordBeaconCompiler.finishPreparation RegistrationNativeSecretWordBeaconCompiler.complete

/-- Every actual native finish has precisely the successful public handle's own-role installation suffix. -/
theorem finish (role : Role) (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner source) (env : EnvState Auxiliary) (packet : Option registration.ResponsePacket) (before : State)
    (result : ((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary) × State)
    (supported : result ∈ support ((simulateQ handler (compile (n := n) setup scalar
      (((RegistrationNativeSecretWordBeaconCompiler.finish setup source packet).run owner).run env))).run before)) :
    ∃ delta, messages role result.2.events = messages role before.events ++ delta ∧
      delta.length = if role = .beacon ∧ present result.1.1.1 = true then 1 else 0 := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.finish, StateT.run_bind, StateT.run_get, pure_bind] at supported
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
          have noInstall := RegistrationNativeSecretWordAtomOwnerInstallPrefix.preparation_free (n := n) role setup source packet owner env
          have bound : (compile setup scalar (((RegistrationNativeSecretWordBeaconCompiler.finishPreparation (n := n) setup source packet).run owner).run env)).IsQueryBoundP
              (RegistrationNativeSecretWordAtomInstallPredicate.GlobalInstall (KemSK := KemSK) role) 0 :=
            RegistrationNativeSecretWordAtomOwnerSource.routing_bound setup role scalar _ 0 noInstall
          have prefixEq := RegistrationNativeSecretWordInstallTrace.free role _ bound before prepared possible
          cases outcome : prepared.1.1.1 with
          | fail error | div =>
              simp only [outcome] at continued
              have ended := abort setup scalar owner prepared.1.1.2 prepared.1.2 _ prepared.2 result continued
              refine ⟨[], ?_, ?_⟩
              · rw [ended.2, prefixEq, List.append_nil]
              · rw [ended.1]; simp [present]
          | ok preparedValue => cases preparedValue with
            | none =>
                simp only [outcome] at continued
                have ended := abort setup scalar owner prepared.1.1.2 prepared.1.2 (.ok none) prepared.2 result continued
                refine ⟨[], ?_, ?_⟩
                · rw [ended.2, prefixEq, List.append_nil]
                · rw [ended.1]; simp [present]
            | some ready =>
                have completed : result ∈ support ((simulateQ handler (RegistrationNativeSecretWordInstallBeaconComplete.compile (n := n) (KemSK := KemSK)
                  (((RegistrationNativeSecretWordBeaconMaterial.complete (n := n) setup.source owner ready).run prepared.1.1.2).run prepared.1.2))).run prepared.2) := by
                  simpa only [outcome, RegistrationNativeSecretWordBeaconCompiler.complete, StateT.run, routing_paired] using continued
                have bill := RegistrationNativeSecretWordInstallBeaconComplete.complete_all role setup.source owner prepared.1.1.2 ready prepared.1.2 prepared.2 result completed
                refine ⟨if role = .beacon ∧ present result.1.1.1 = true then [ready.reference] else [], ?_, ?_⟩
                · rw [bill, prefixEq]
                · split <;> rfl

end BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBeaconFinish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBeaconFinish.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBeaconFinish.finish
