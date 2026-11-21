-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceFinish

/-! Actual Beacon response processing makes at most one root preparation on every failure branch. Its native completion and record installation make no additional preparation queries. The count is structural and independent of primitive or KEM sampling loops. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconPrepareCaps
open RegistrationBeaconReferenceCompiler
open PqxdhServerAuthExperiment (Setup)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}

def IsPrepare : (Spec n KemSK).Domain → Prop
  | .inl _ => True
  | _ => False
instance : DecidablePred (IsPrepare (n := n) (KemSK := KemSK)) := fun query => by
  cases query with
  | inl _ => exact isTrue trivial
  | inr _ => exact isFalse id

private theorem effect_free (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    (simulateQ (effect (KemSK := KemSK)) work).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [effect, IsPrepare, isQueryBoundP_query_iff]

private theorem sample_free (work : ProbComp Value) :
    (sample (n := n) (KemSK := KemSK) work).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 0 := by
  unfold sample
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro coin
  simp [effect, IsPrepare, isQueryBoundP_query_iff]

private theorem primitive_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    (primitive (n := n) setup owner oneTime query).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 0 := by
  unfold primitive
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  cases query with
  | inl query => simpa only [other, ite_false] using (sample_free (KemSK := KemSK) _)
  | inr query => simp [indexed, IsPrepare, isQueryBoundP_query_iff]

private theorem backend_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Spec.Domain) (before : EnvState Auxiliary) :
    ((backend (n := n) setup owner oneTime query).run before).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 0 := by
  simp only [backend, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_lift,
    bind_pure_comp, isQueryBoundP_map_iff]
  cases query <;> first | exact primitive_free setup owner oneTime _ | trivial

private theorem backend_program_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (before : EnvState Auxiliary) :
    ((simulateQ (backend (n := n) setup owner oneTime) work).run before).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_run_of_step
  · intro query impossible
    contradiction
  · intro query _ current
    exact backend_free setup owner oneTime query current

private theorem prefix_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (query : (PqxdhPhase2GapDhSource.PrefixSpec Unit Unit Unit Unit registration.AuthenticatedResponse).Domain)
    (before : EnvState Auxiliary) :
    ((PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain
      (RegistrationBeaconRootInterpreter.auxImpl (backend (n := n) setup owner oneTime) authenticated) visit query).run before).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 0 := by
  cases query <;> simp only [PqxdhPhase2GapDhSource.prefixImpl, RegistrationBeaconRootInterpreter.auxImpl]
  all_goals first | exact backend_program_free setup owner oneTime _ before | trivial

/-- Every actual selected-owner prefix path has zero root preparation cost. -/
theorem collect_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((collect (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 0 := by
  unfold collect
  apply (isQueryBoundP_false _ 0).simulateQ_run_of_step
  · intro query impossible
    contradiction
  · intro query _ current
    exact prefix_free setup owner oneTime authenticated query current

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

private theorem prepare_bound (work : OracleComp RegistrationServerReferenceRoot.PrepareSpec Value)
    (bounded : work.IsTotalQueryBound 1) :
    (simulateQ (prepare (n := n) (KemSK := KemSK)) work).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 1 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => True) _ work 1 ((isQueryBoundP_true_iff work 1).mpr bounded)
  intro query
  simp [prepare, IsPrepare, isQueryBoundP_query_iff]

private theorem agreement_bound (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((agreement (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 1 := by
  simp only [agreement, StateT.run_bind]
  apply isQueryBoundP_bind (m := 1) (collect_free setup owner oneTime authenticated before)
  intro result _
  cases result.1 with
  | none => trivial
  | some pending =>
      simpa only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff] using
        prepare_bound (n := n) (KemSK := KemSK) (RegistrationBeaconReferenceRoot.client authenticated pending)
          (RegistrationBeaconReferenceRoot.client_bound authenticated pending)

/-- Response authentication and preparation make at most one root preparation. -/
theorem preparation_bound (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner mlSource) (before : EnvState Auxiliary) :
    (((finishPreparation (n := n) setup mlSource packet).run owner).run before).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 1 := by
  simp only [finishPreparation, StateT.run_bind, StateT.run_get, pure_bind]
  cases owner.phase with
  | fresh => trivial
  | freshWithCoins oneTime => trivial
  | established completed => trivial
  | aborted aborted => trivial
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error => simp only [moved, StateT.run_pure]; trivial
      | div => simp only [moved, StateT.run_pure]; trivial
      | ok aborted =>
          simp only [moved, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_lift, bind_assoc]
          apply isQueryBoundP_bind (m := 1) (effect_free _)
          intro accepted _
          cases accepted with
          | fail error => trivial
          | div => trivial
          | ok reply => cases reply with
            | Err error => trivial
            | Ok authenticated =>
                simpa only [StateT.run_lift, StateT.run_map, bind_pure_comp, map_apply, isQueryBoundP_map_iff] using
                  agreement_bound setup owner oneTime authenticated before

private theorem common_free (work : OracleComp (RegistrationNativePairedServerService.Common n) Value) :
    OracleComp.IsQueryBoundP (simulateQ (fun query => ((Spec n KemSK).query (.inr (.inl (.inr query))) : OracleComp (Spec n KemSK) _)) work) (IsPrepare (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [IsPrepare, isQueryBoundP_query_iff]

private theorem admitted_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (message : RegistrationNativeRelatedFamily.Message) :
    (simulateQ (RegistrationBeaconReferenceFinish.service (KemSK := KemSK))
      (RegistrationNativePairedBeaconService.admitted (n := n) source owner sender descriptor message)).IsQueryBoundP
        (IsPrepare (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  cases query <;> simp [RegistrationBeaconReferenceFinish.service, IsPrepare, isQueryBoundP_query_iff]

private theorem abort_free {source : RegistrationNativeMldsa.Source}
    (owner current : SelectedOwner source) (before : EnvState Auxiliary) :
    (((RegistrationBeaconReferenceFinish.abort (n := n) (KemSK := KemSK) owner).run current).run before).IsQueryBoundP
      (IsPrepare (KemSK := KemSK)) 0 := by
  simp only [RegistrationBeaconReferenceFinish.abort,
    bind_pure_comp]
  simp [effect, IsPrepare, isQueryBoundP_query_iff]

/-- Completing a prepared native owner makes no root preparation, even when opening or installation fails. -/
theorem complete_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (ready : RegistrationBeaconReferenceRoot.Ready) (before : EnvState Auxiliary) :
    (((RegistrationBeaconReferenceFinish.complete (n := n) (KemSK := KemSK) source owner ready).run current).run before).IsQueryBoundP
      (IsPrepare (KemSK := KemSK)) 0 := by
  simp only [RegistrationBeaconReferenceFinish.complete, StateT.run_bind, StateT.run_lift,
    bind_map_left, bind_pure_comp]
  apply isQueryBoundP_bind (n := 0) (m := 0) (admitted_free source owner.worldOwner owner.pin.binding.identity_key_id ready.descriptor ready.reference)
  intro completed _
  cases completed with
  | fail error =>
      simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, map_apply,
        isQueryBoundP_map_iff] using abort_free (KemSK := KemSK) owner current before
  | div =>
      simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, map_apply,
        isQueryBoundP_map_iff] using abort_free (KemSK := KemSK) owner current before
  | ok completed => cases completed with
    | Err aborted =>
        simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, map_apply,
          isQueryBoundP_map_iff] using abort_free (KemSK := KemSK) owner current before
    | Ok completed => trivial

/-- The full selected-owner finish retains its single root preparation allowance on every actual lifecycle branch. -/
theorem finish_bound (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (before : EnvState Auxiliary) :
    (((RegistrationBeaconReferenceFinish.finish (n := n) (KemSK := KemSK) setup source packet).run owner).run before).IsQueryBoundP
      (IsPrepare (KemSK := KemSK)) 1 := by
  simp only [RegistrationBeaconReferenceFinish.finish, StateT.run_bind, StateT.run_get, pure_bind]
  cases owner.phase with
  | fresh => trivial
  | freshWithCoins oneTime => trivial
  | established completed => trivial
  | aborted aborted => trivial
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error => simp only [moved, StateT.run_pure]; trivial
      | div => simp only [moved, StateT.run_pure]; trivial
      | ok aborted =>
          simp only []
          apply isQueryBoundP_bind (n := 1) (m := 0) (preparation_bound setup source packet owner before)
          intro result _
          rcases result with ⟨⟨prepared, current⟩, env⟩
          cases prepared with
          | fail error =>
              simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                abort_free (KemSK := KemSK) owner current env
          | div =>
              simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                abort_free (KemSK := KemSK) owner current env
          | ok prepared => cases prepared with
            | none =>
                simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                  abort_free (KemSK := KemSK) owner current env
            | some ready => exact complete_free setup.source owner current ready env

end BeaconcryptCore.Computational.RegistrationBeaconPrepareCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconPrepareCaps.collect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconPrepareCaps.collect_free

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconPrepareCaps.preparation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconPrepareCaps.preparation_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconPrepareCaps.complete_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconPrepareCaps.complete_free

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconPrepareCaps.finish_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconPrepareCaps.finish_bound
