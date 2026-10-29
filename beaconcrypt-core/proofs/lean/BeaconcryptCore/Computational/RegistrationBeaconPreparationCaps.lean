-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks
import BeaconcryptCore.Computational.RegistrationBeaconReferenceFinish

/-! Preparation and deferred material are different resources. An actual selected-owner response prefix has no prepare query; successful completion of the prefix makes one. The terminal finish operation therefore has at most one prepare, including every rejected or failed branch. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconPreparationCaps
open RegistrationBeaconReferenceCompiler
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}

def IsPrepare : (Spec n KemSK).Domain → Prop
  | .inl _ => True
  | .inr _ => False
instance : DecidablePred (IsPrepare (n := n) (KemSK := KemSK)) := fun query => by
  cases query with
  | inl _ => exact isTrue trivial
  | inr _ => exact isFalse id

private theorem trusted_free (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value) :
    (simulateQ trustedLift work).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  cases query <;> simp [trustedLift, effect, indexed, IsPrepare, isQueryBoundP_query_iff]

private theorem environment_free (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    (simulateQ (effect (KemSK := KemSK)) work).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [effect, IsPrepare, isQueryBoundP_query_iff]

/-- The complete concrete native public prefix issues no prepare callback. -/
theorem collect_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((collect (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 0 := by
  rw [← RegistrationBeaconReferenceCallbacks.collect_lift]
  exact trusted_free _

private theorem prepare_bound (work : OracleComp RegistrationServerReferenceRoot.PrepareSpec Value)
    (bounded : work.IsTotalQueryBound 1) :
    (simulateQ (prepare (n := n) (KemSK := KemSK)) work).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 1 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => True) _ work 1 ((isQueryBoundP_true_iff work 1).mpr bounded)
  intro query
  simp [prepare, IsPrepare, isQueryBoundP_query_iff]

/-- The actual prepared-message gate makes at most one root-preparation query. -/
theorem agreement_bound (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((agreement (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 1 := by
  simp only [agreement, StateT.run_bind]
  refine (isQueryBoundP_bind (n := 0) (m := 1) (collect_free setup owner oneTime authenticated before) ?_)
  intro result _reached
  cases result.1 with
  | none => trivial
  | some pending =>
      simpa only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff] using
        prepare_bound (n := n) (KemSK := KemSK) (RegistrationBeaconReferenceRoot.client authenticated pending)
          (RegistrationBeaconReferenceRoot.client_bound authenticated pending)

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

/-- Mandatory authentication, all early exits and terminal malformed-response consumption retain the single preparation allowance. -/
theorem preparation_bound (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (before : EnvState Auxiliary) :
    (((finishPreparation (n := n) setup source packet).run owner).run before).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 1 := by
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
          apply isQueryBoundP_bind (n := 0) (m := 1) (environment_free _)
          intro accepted _
          cases accepted with
          | fail error => trivial
          | div => trivial
          | ok reply => cases reply with
            | Err error => trivial
            | Ok authenticated =>
                simpa only [StateT.run_lift, StateT.run_map, bind_pure_comp, map_apply, isQueryBoundP_map_iff] using
                  agreement_bound setup owner oneTime authenticated before

private theorem service_free (work : OracleComp (RegistrationNativePairedServerService.PublicSpec n) Value) :
    (simulateQ (RegistrationBeaconReferenceFinish.service (KemSK := KemSK)) work).IsQueryBoundP
      (IsPrepare (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [RegistrationBeaconReferenceFinish.service, IsPrepare, isQueryBoundP_query_iff]

private theorem abort_free {source : RegistrationNativeMldsa.Source}
    (owner current : SelectedOwner source) (before : EnvState Auxiliary) :
    (((RegistrationBeaconReferenceFinish.abort (n := n) (KemSK := KemSK) owner).run current).run before).IsQueryBoundP
      (IsPrepare (KemSK := KemSK)) 0 := by
  simp [RegistrationBeaconReferenceFinish.abort, effect, StateT.run_lift, bind_pure_comp,
    IsPrepare, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

/-- Actual post-root opening and installation never perform another root preparation. -/
theorem complete_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (ready : RegistrationBeaconReferenceRoot.Ready) (before : EnvState Auxiliary) :
    (((RegistrationBeaconReferenceFinish.complete (n := n) (KemSK := KemSK) source owner ready).run current).run before).IsQueryBoundP
      (IsPrepare (KemSK := KemSK)) 0 := by
  simp only [RegistrationBeaconReferenceFinish.complete, StateT.run_bind, StateT.run_lift,
    bind_map_left, bind_pure_comp]
  apply isQueryBoundP_bind (n := 0) (m := 0) (service_free _)
  intro completed _reached
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

/-- The complete terminal native finish has at most one preparation, separately from its at-most-one material demand. -/
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
          apply isQueryBoundP_bind (n := 1) (m := 0) (preparation_bound setup source packet owner before)
          intro result _reached
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

end BeaconcryptCore.Computational.RegistrationBeaconPreparationCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconPreparationCaps.collect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconPreparationCaps.collect_free
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconPreparationCaps.agreement_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconPreparationCaps.agreement_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconPreparationCaps.preparation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconPreparationCaps.preparation_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconPreparationCaps.complete_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconPreparationCaps.complete_free
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconPreparationCaps.finish_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconPreparationCaps.finish_bound
