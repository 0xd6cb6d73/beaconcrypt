-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateLocal
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsMaterial

/-! The actual symbolic Beacon controller has zero private KEM birth before completion and at most one afterward. The completion bill is transported through its exact open-program source equality whose query map forwards every material/Common request once with its unchanged reply type. Terminal consumption, malformed packets and all failed installations remain present. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateBeacon
open RegistrationNativeSecretWordBeaconCompiler
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeSecretWordInterface (LocalSpec effect prepare)
open PqxdhServerAuthExperiment (Setup)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}
abbrev Spec := LocalSpec
abbrev IsCreate := RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate (n := n) (KemSK := KemSK)

private theorem effect_free (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    (simulateQ (effect (KemSK := KemSK)) work).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 :=
  RegistrationNativeSecretWordTargetNoCreateLocal.effect_free work

/-- The entire actual symbolic collector has the literal source's zero deferred material bill. -/
theorem collect_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((collect (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 :=
  RegistrationNativeSecretWordTargetNoCreateLocal.beacon_collect_free setup owner oneTime authenticated before

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

private theorem prepare_free (work : OracleComp RegistrationNativeSecretWordMessage.PrepareSpec Value) :
    (simulateQ (prepare (n := n) (KemSK := KemSK)) work).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [prepare, IsCreate, RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate, isQueryBoundP_query_iff]

private theorem agreement_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((agreement (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 := by
  simp only [agreement, StateT.run_bind]
  apply isQueryBoundP_bind (m := 0) (collect_free setup owner oneTime authenticated before)
  intro result _
  cases result.1 with
  | none => trivial
  | some pending =>
      simpa only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff] using
        prepare_free (n := n) (KemSK := KemSK) (RegistrationNativeSecretWordBeaconRoot.client authenticated pending)

/-- Response authentication and preparation do not consume any later private birth allowance. -/
theorem preparation_free (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner mlSource) (before : EnvState Auxiliary) :
    (((finishPreparation (n := n) setup mlSource packet).run owner).run before).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 := by
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
          apply isQueryBoundP_bind (m := 0) (effect_free _)
          intro accepted _
          cases accepted with
          | fail error => trivial
          | div => trivial
          | ok reply => cases reply with
            | Err error => trivial
            | Ok authenticated =>
                simpa only [StateT.run_lift, StateT.run_map, bind_pure_comp, map_apply, isQueryBoundP_map_iff] using
                  agreement_free setup owner oneTime authenticated before

private theorem abort_free {source : RegistrationNativeMldsa.Source}
    (owner current : SelectedOwner source) (before : EnvState Auxiliary) :
    (((RegistrationNativeSecretWordBeaconCompiler.abort (n := n) (KemSK := KemSK) owner).run current).run before).IsQueryBoundP
      (IsCreate (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.abort,
    bind_pure_comp]
  simp [effect, IsCreate, RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate, isQueryBoundP_query_iff]

/-- Actual completion only asks for material and Common operations, so it creates no private key. -/
theorem complete_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (ready : RegistrationNativeSecretWordMessage.BeaconReady) (before : EnvState Auxiliary) :
    (((complete (n := n) (KemSK := KemSK) source owner ready).run current).run before).IsQueryBoundP
      (IsCreate (KemSK := KemSK)) 0 := by
  change (simulateQ RegistrationNativeSecretWordInterface.paired
    (((RegistrationNativeSecretWordBeaconMaterial.complete source owner ready).run current).run before)).IsQueryBoundP _ 0
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  cases query <;> simp [RegistrationNativeSecretWordInterface.paired, IsCreate,
    RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate, isQueryBoundP_query_iff]

/-- The full selected-owner finish retains its zero private birth allowance on every actual lifecycle branch. -/
theorem finish_free (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (before : EnvState Auxiliary) :
    (((RegistrationNativeSecretWordBeaconCompiler.finish (n := n) (KemSK := KemSK) setup source packet).run owner).run before).IsQueryBoundP
      (IsCreate (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.finish, StateT.run_bind, StateT.run_get, pure_bind]
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
          apply isQueryBoundP_bind (n := 0) (m := 0) (preparation_free setup source packet owner before)
          intro result _
          rcases result with ⟨⟨prepared, current⟩, env⟩
          cases prepared with
          | fail error =>
              simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                (abort_free (KemSK := KemSK) owner current env)
          | div =>
              simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                (abort_free (KemSK := KemSK) owner current env)
          | ok prepared => cases prepared with
            | none =>
                simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                  (abort_free (KemSK := KemSK) owner current env)
            | some ready => exact complete_free setup.source owner current ready env

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateBeacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateBeacon.collect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateBeacon.collect_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateBeacon.preparation_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateBeacon.preparation_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateBeacon.complete_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateBeacon.complete_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateBeacon.finish_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateBeacon.finish_free
