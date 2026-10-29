-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleBeaconCaps

/-! The actual symbolic Beacon controller has one indexed decapsulation only after its terminal move gate. The finite open collector equation preserves query syntax and its bound while evaluating only returned data; later material and opening callbacks are local Common requests and cannot add a getter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleBeaconCaps
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordInterface (LocalSpec effect prepare paired)
open RegistrationNativeSecretWordBeaconCompiler (collect agreement finishPreparation complete)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}

def IsDecap : (LocalSpec n KemSK).Domain → Prop
  | .inr (.inr (.inr (.inl (.decapsulate _ _)))) => True
  | _ => False
instance : DecidablePred (IsDecap (n := n) (KemSK := KemSK)) := fun query => by
  unfold IsDecap
  split <;> infer_instance

private theorem realize_bound (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordLifecycleBeaconCaps.IsDecap (KemSK := KemSK)) cap) :
    (simulateQ (RegistrationNativeSecretWordServerSource.realize candidate) work).IsQueryBoundP (IsDecap (KemSK := KemSK)) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work cap bounded
  intro query
  rcases query with message | (message | common) | (other | (pool | key))
  all_goals try cases pool
  all_goals simp [RegistrationNativeSecretWordServerSource.realize, prepare,
    RegistrationNativeSecretWordInterface.demand, RegistrationNativeSecretWordInterface.common,
    RegistrationNativeSecretWordInterface.localKem, IsDecap,
    RegistrationNativeSecretWordLifecycleBeaconCaps.IsDecap, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

private theorem environment_free (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    (simulateQ (effect (KemSK := KemSK)) work).IsQueryBoundP (IsDecap (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [effect, IsDecap, isQueryBoundP_query_iff]

/-- The exact open collector source equation transports the actual syntactic single-getter cap, preserving every optional branch. -/
theorem collect_bound (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((collect (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP (IsDecap (KemSK := KemSK)) 1 := by
  have bounded := realize_bound RegistrationNativeSecretWordMessage.zero _ 1
    (RegistrationNativeSecretWordLifecycleBeaconCaps.collect_bound (n := n) setup owner oneTime authenticated before)
  rw [RegistrationNativeSecretWordBeaconSource.collector_source] at bounded
  exact (isQueryBoundP_map_iff _ _ _).mp bounded

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

private theorem prepare_free (work : OracleComp RegistrationNativeSecretWordMessage.PrepareSpec Value) :
    (simulateQ (prepare (n := n) (KemSK := KemSK)) work).IsQueryBoundP (IsDecap (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [prepare, IsDecap, isQueryBoundP_query_iff]

private theorem agreement_bound (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((agreement (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP (IsDecap (KemSK := KemSK)) 1 := by
  simp only [agreement, StateT.run_bind]
  apply isQueryBoundP_bind (m := 0) (collect_bound setup owner oneTime authenticated before)
  intro result _
  cases result.1 with
  | none => trivial
  | some pending =>
      simpa only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff] using
        prepare_free (n := n) (KemSK := KemSK) (RegistrationNativeSecretWordBeaconRoot.client authenticated pending)

/-- Authentication and the terminal move precede at most one actual symbolic decapsulation. -/
theorem preparation_bound (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (before : EnvState Auxiliary) :
    (((finishPreparation (n := n) setup source packet).run owner).run before).IsQueryBoundP (IsDecap (KemSK := KemSK)) 1 := by
  simp only [finishPreparation, StateT.run_bind, StateT.run_get, pure_bind]
  cases owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ => trivial
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error | div => simp only [moved, StateT.run_pure]; trivial
      | ok aborted =>
          simp only [moved, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_lift, bind_assoc]
          apply isQueryBoundP_bind (n := 0) (m := 1) (environment_free _)
          intro accepted _
          cases accepted with
          | fail error | div => trivial
          | ok reply => cases reply with
            | Err error => trivial
            | Ok authenticated =>
                simpa only [StateT.run_lift, StateT.run_map, bind_pure_comp, map_apply, isQueryBoundP_map_iff] using
                  agreement_bound setup owner oneTime authenticated before

private theorem abort_free {source : RegistrationNativeMldsa.Source}
    (owner current : SelectedOwner source) (before : EnvState Auxiliary) :
    (((RegistrationNativeSecretWordBeaconCompiler.abort (n := n) (KemSK := KemSK) owner).run current).run before).IsQueryBoundP
      (IsDecap (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.abort, bind_pure_comp]
  simp [effect, IsDecap, isQueryBoundP_query_iff]

/-- Every actual material, opening and installation branch is decapsulation-free. -/
theorem complete_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (ready : RegistrationNativeSecretWordMessage.BeaconReady) (before : EnvState Auxiliary) :
    (((complete (n := n) (KemSK := KemSK) source owner ready).run current).run before).IsQueryBoundP (IsDecap (KemSK := KemSK)) 0 := by
  change (simulateQ paired _).IsQueryBoundP _ 0
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  cases query <;> simp [paired, IsDecap, isQueryBoundP_query_iff]

/-- The actual whole selected-owner finish spends at most its single indexed getter only when its terminal move succeeds. -/
theorem finish_bound (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (before : EnvState Auxiliary) :
    (((RegistrationNativeSecretWordBeaconCompiler.finish (n := n) (KemSK := KemSK) setup source packet).run owner).run before).IsQueryBoundP
      (IsDecap (KemSK := KemSK)) (if RegistrationNativeSecretWordLifecycleOwnerCredit.canFinish owner.phase then 1 else 0) := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.finish, StateT.run_bind, StateT.run_get, pure_bind]
  cases phase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ =>
      simp only [RegistrationNativeSecretWordLifecycleOwnerCredit.canFinish]
      trivial
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error | div =>
          simp only [moved, StateT.run_pure, RegistrationNativeSecretWordLifecycleOwnerCredit.canFinish, Bool.false_eq_true, ite_false]
          trivial
      | ok aborted =>
          simp only [RegistrationNativeSecretWordLifecycleOwnerCredit.canFinish, moved, ite_true]
          apply isQueryBoundP_bind (n := 1) (m := 0) (preparation_bound setup source packet owner before)
          intro result _
          rcases result with ⟨⟨prepared, current⟩, env⟩
          cases prepared with
          | fail error | div =>
              simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                (abort_free (KemSK := KemSK) owner current env)
          | ok prepared => cases prepared with
            | none =>
                simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                  (abort_free (KemSK := KemSK) owner current env)
            | some ready => exact complete_free setup.source owner current ready env

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleBeaconCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleBeaconCaps.collect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleBeaconCaps.collect_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleBeaconCaps.preparation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleBeaconCaps.preparation_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleBeaconCaps.complete_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleBeaconCaps.complete_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleBeaconCaps.finish_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleBeaconCaps.finish_bound
