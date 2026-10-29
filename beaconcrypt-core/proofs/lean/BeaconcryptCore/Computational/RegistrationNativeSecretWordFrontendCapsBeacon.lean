-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsLocal
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsMaterial

/-! The actual symbolic Beacon controller has zero material demand before completion and at most one afterward. The completion bill is transported through its exact open-program source equality whose query map forwards every material/Common request once with its unchanged reply type. Terminal consumption, malformed packets and all failed installations remain present. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsBeacon
open RegistrationNativeSecretWordBeaconCompiler
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeSecretWordInterface (LocalSpec effect prepare)
open PqxdhServerAuthExperiment (Setup)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}
abbrev Spec := LocalSpec
abbrev IsDemand := RegistrationNativeSecretWordFrontendCapsLocal.IsDemand (n := n) (KemSK := KemSK)

private theorem effect_free (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    (simulateQ (effect (KemSK := KemSK)) work).IsQueryBoundP (IsDemand (KemSK := KemSK)) 0 :=
  RegistrationNativeSecretWordFrontendCapsLocal.effect_free work

/-- The entire actual symbolic collector has the literal source's zero deferred material bill. -/
theorem collect_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((collect (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP (IsDemand (KemSK := KemSK)) 0 :=
  RegistrationNativeSecretWordFrontendCapsLocal.beacon_collect_free setup owner oneTime authenticated before

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

private theorem prepare_free (work : OracleComp RegistrationNativeSecretWordMessage.PrepareSpec Value) :
    (simulateQ (prepare (n := n) (KemSK := KemSK)) work).IsQueryBoundP (IsDemand (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [prepare, IsDemand, RegistrationNativeSecretWordFrontendCapsLocal.IsDemand, isQueryBoundP_query_iff]

private theorem agreement_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((agreement (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP (IsDemand (KemSK := KemSK)) 0 := by
  simp only [agreement, StateT.run_bind]
  apply isQueryBoundP_bind (m := 0) (collect_free setup owner oneTime authenticated before)
  intro result _
  cases result.1 with
  | none => trivial
  | some pending =>
      simpa only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff] using
        prepare_free (n := n) (KemSK := KemSK) (RegistrationNativeSecretWordBeaconRoot.client authenticated pending)

/-- Response authentication and preparation do not consume any later material allowance. -/
theorem preparation_free (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner mlSource) (before : EnvState Auxiliary) :
    (((finishPreparation (n := n) setup mlSource packet).run owner).run before).IsQueryBoundP (IsDemand (KemSK := KemSK)) 0 := by
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
      (IsDemand (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.abort,
    bind_pure_comp]
  simp [effect, IsDemand, RegistrationNativeSecretWordFrontendCapsLocal.IsDemand, isQueryBoundP_query_iff]

private theorem material_reflect (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (work : OracleComp (RegistrationNativeSecretWordBeaconMaterial.Spec n) Value) (cap : Nat)
    (bounded : (simulateQ (RegistrationBeaconReferenceFinish.service (KemSK := KemSK) ∘ₛ
      RegistrationNativeSecretWordServerMaterial.realize candidate) work).IsQueryBoundP
        (RegistrationBeaconReferenceCaps.IsDemand (KemSK := KemSK)) cap) :
    work.IsQueryBoundP (RegistrationNativeSecretWordFrontendCapsMaterial.IsDemand (n := n)) cap := by
  induction work using OracleComp.inductionOn generalizing cap with
  | pure value => trivial
  | query_bind query next ih =>
      cases query with
      | inl message =>
          simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.compose,
            RegistrationNativeSecretWordServerMaterial.realize, RegistrationBeaconReferenceFinish.service,
            simulateQ_spec_query, isQueryBoundP_query_bind_iff,
            RegistrationBeaconReferenceCaps.IsDemand, RegistrationNativeSecretWordFrontendCapsMaterial.IsDemand] at bounded ⊢
          exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩
      | inr common =>
          simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.compose,
            RegistrationNativeSecretWordServerMaterial.realize, RegistrationBeaconReferenceFinish.service,
            simulateQ_spec_query, isQueryBoundP_query_bind_iff,
            RegistrationBeaconReferenceCaps.IsDemand, RegistrationNativeSecretWordFrontendCapsMaterial.IsDemand] at bounded ⊢
          exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩

private theorem material_complete_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (ready : RegistrationNativeSecretWordMessage.BeaconReady) (before : EnvState Auxiliary) :
    (((RegistrationNativeSecretWordBeaconMaterial.complete source owner ready).run current).run before).IsQueryBoundP
      (RegistrationNativeSecretWordFrontendCapsMaterial.IsDemand (n := n)) 1 := by
  have native := RegistrationBeaconReferenceCaps.complete_bound (n := n) (KemSK := Unit)
    source owner current (ready.eval RegistrationNativeSecretWordMessage.zero) before
  rw [← RegistrationNativeSecretWordBeaconMaterial.complete_source RegistrationNativeSecretWordMessage.zero
    source owner current ready before] at native
  exact material_reflect RegistrationNativeSecretWordMessage.zero _ 1 native

/-- Every actual symbolic completion has one material demand, with all reply branches and native poststates retained. -/
theorem complete_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (ready : RegistrationNativeSecretWordMessage.BeaconReady) (before : EnvState Auxiliary) :
    (((complete (n := n) (KemSK := KemSK) source owner ready).run current).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) 1 := by
  change (simulateQ RegistrationNativeSecretWordInterface.paired
    (((RegistrationNativeSecretWordBeaconMaterial.complete source owner ready).run current).run before)).IsQueryBoundP _ 1
  apply RawCtxSourceOpen.simulate_bound _ (RegistrationNativeSecretWordFrontendCapsMaterial.IsDemand (n := n)) _ _ 1
    (material_complete_bound source owner current ready before)
  intro query
  cases query <;> simp [RegistrationNativeSecretWordInterface.paired, IsDemand,
    RegistrationNativeSecretWordFrontendCapsLocal.IsDemand, RegistrationNativeSecretWordFrontendCapsMaterial.IsDemand,
    isQueryBoundP_query_iff]

/-- The full selected-owner finish retains its single material allowance on every actual lifecycle branch. -/
theorem finish_bound (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (before : EnvState Auxiliary) :
    (((RegistrationNativeSecretWordBeaconCompiler.finish (n := n) (KemSK := KemSK) setup source packet).run owner).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) 1 := by
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
          apply isQueryBoundP_bind (n := 0) (m := 1) (preparation_free setup source packet owner before)
          intro result _
          rcases result with ⟨⟨prepared, current⟩, env⟩
          cases prepared with
          | fail error =>
              simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                (abort_free (KemSK := KemSK) owner current env).mono (Nat.zero_le 1)
          | div =>
              simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                (abort_free (KemSK := KemSK) owner current env).mono (Nat.zero_le 1)
          | ok prepared => cases prepared with
            | none =>
                simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                  (abort_free (KemSK := KemSK) owner current env).mono (Nat.zero_le 1)
            | some ready => exact complete_bound setup.source owner current ready env

end BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsBeacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsBeacon.collect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsBeacon.collect_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsBeacon.preparation_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsBeacon.preparation_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsBeacon.complete_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsBeacon.complete_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsBeacon.finish_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsBeacon.finish_bound
