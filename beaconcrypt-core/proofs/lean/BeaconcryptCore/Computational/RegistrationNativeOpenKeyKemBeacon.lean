-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceFinish
import BeaconcryptCore.Computational.RegistrationNativeProviderBeaconCaps
import BeaconcryptCore.Computational.RegistrationNativeKemCompilerFootprint

/-! Actual native Beacon reference collection and finishing create no KEM key and reveal no private generated secret. Indexed decapsulation and all ordinary local operations remain present. These structural zero bills retain every authentication, root-preparation and first-record failure branch. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemBeacon
open RegistrationBeaconReferenceCompiler
open PqxdhServerAuthExperiment (Setup)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}
variable {kind : RegistrationNativeKemBeaconFootprint.Kind}

def IsPrivate (kind : RegistrationNativeKemBeaconFootprint.Kind) : (Spec n KemSK).Domain → Prop
  | .inr (.inr query) => RegistrationNativeKemCompilerFootprint.predicate RegistrationNativeKemInterface.OtherSpec KemSK kind query
  | _ => False
instance (kind : RegistrationNativeKemBeaconFootprint.Kind) : DecidablePred (IsPrivate (n := n) (KemSK := KemSK) kind) := fun query => by
  rcases query with message | (query | query) <;> simp only [IsPrivate] <;> infer_instance

private theorem effect_free (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    (simulateQ (effect (KemSK := KemSK)) work).IsQueryBoundP (IsPrivate (KemSK := KemSK) kind) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [effect, IsPrivate, isQueryBoundP_query_iff]

private theorem sample_free (work : ProbComp Value) :
    (sample (n := n) (KemSK := KemSK) work).IsQueryBoundP (IsPrivate (KemSK := KemSK) kind) 0 := by
  unfold sample
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro coin
  simp [effect, IsPrivate, isQueryBoundP_query_iff]

private theorem primitive_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    (primitive (n := n) setup owner oneTime query).IsQueryBoundP (IsPrivate (KemSK := KemSK) kind) 0 := by
  cases query with
  | convertPublic key | convertSecret role | generate role | dh request =>
      simpa only [primitive, RegistrationNativeKemInterface.beacon, RegistrationNativeKemInterface.other,
        simulateQ_spec_query, other] using (sample_free (kind := kind) (KemSK := KemSK) _)
  | encapsulate key =>
      simp only [primitive, RegistrationNativeKemInterface.beacon, simulateQ_pure, isQueryBoundP_pure]
  | decapsulate ciphertext =>
      cases ciphertext <;> simp [primitive, RegistrationNativeKemInterface.beacon, simulateQ_map,
        indexed, IsPrivate, RegistrationNativeKemCompilerFootprint.predicate,
        isQueryBoundP_map_iff, isQueryBoundP_query_iff]

private theorem backend_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Spec.Domain) (before : EnvState Auxiliary) :
    ((backend (n := n) setup owner oneTime query).run before).IsQueryBoundP (IsPrivate (KemSK := KemSK) kind) 0 := by
  simp only [backend, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_lift,
    bind_pure_comp, isQueryBoundP_map_iff]
  cases query <;> first | exact primitive_free setup owner oneTime _ | trivial

private theorem backend_program_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (before : EnvState Auxiliary) :
    ((simulateQ (backend (n := n) setup owner oneTime) work).run before).IsQueryBoundP (IsPrivate (KemSK := KemSK) kind) 0 := by
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
      (RegistrationBeaconRootInterpreter.auxImpl (backend (n := n) setup owner oneTime) authenticated) visit query).run before).IsQueryBoundP (IsPrivate (KemSK := KemSK) kind) 0 := by
  cases query <;> simp only [PqxdhPhase2GapDhSource.prefixImpl, RegistrationBeaconRootInterpreter.auxImpl]
  all_goals first | exact backend_program_free setup owner oneTime _ before | trivial

/-- Every actual selected-owner collector has zero private KEM birth/reveal cost. -/
theorem collect_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((collect (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP (IsPrivate (KemSK := KemSK) kind) 0 := by
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

private theorem prepare_free (work : OracleComp RegistrationServerReferenceRoot.PrepareSpec Value) :
    (simulateQ (prepare (n := n) (KemSK := KemSK)) work).IsQueryBoundP (IsPrivate (KemSK := KemSK) kind) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [prepare, IsPrivate, isQueryBoundP_query_iff]

private theorem agreement_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((agreement (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP (IsPrivate (KemSK := KemSK) kind) 0 := by
  simp only [agreement, StateT.run_bind]
  apply isQueryBoundP_bind (m := 0) (collect_free setup owner oneTime authenticated before)
  intro result _
  cases result.1 with
  | none => trivial
  | some pending =>
      simpa only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff] using
        prepare_free (n := n) (KemSK := KemSK) (RegistrationBeaconReferenceRoot.client authenticated pending)

/-- Actual response authentication and root preparation never create or reveal a KEM key. -/
theorem preparation_free (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner mlSource) (before : EnvState Auxiliary) :
    (((finishPreparation (n := n) setup mlSource packet).run owner).run before).IsQueryBoundP (IsPrivate (KemSK := KemSK) kind) 0 := by
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

private theorem private_of_kem (query : (Spec n KemSK).Domain) (counted : IsPrivate kind query) :
    RegistrationNativeProviderBuildCaps.IsLocalKem query := by
  rcases query with message | (query | query)
  · exact counted.elim
  · exact counted.elim
  · trivial

/-- Complete post-root execution has zero private KEM birth/reveal cost on every failure and success branch. -/
theorem complete_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (ready : RegistrationBeaconReferenceRoot.Ready) (before : EnvState Auxiliary) :
    (((RegistrationBeaconReferenceFinish.complete (n := n) (KemSK := KemSK) source owner ready).run current).run before).IsQueryBoundP
      (IsPrivate (KemSK := KemSK) kind) 0 :=
  OracleComp.IsQueryBoundP.of_imp (private_of_kem (kind := kind) (KemSK := KemSK))
    (RegistrationNativeProviderBeaconCaps.complete_zero source owner current ready before)

/-- Entire native reference finishing creates no KEM key and reveals no generated secret. -/
theorem finish_free (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (before : EnvState Auxiliary) :
    (((RegistrationBeaconReferenceFinish.finish (n := n) (KemSK := KemSK) setup source packet).run owner).run before).IsQueryBoundP
      (IsPrivate (KemSK := KemSK) kind) 0 := by
  simp only [RegistrationBeaconReferenceFinish.finish, StateT.run_bind, StateT.run_get, pure_bind]
  cases owner.phase with
  | fresh | freshWithCoins oneTime | established completed | aborted aborted => trivial
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error | div => simp only [moved, StateT.run_pure]; trivial
      | ok aborted =>
          simp only []
          apply isQueryBoundP_bind (n := 0) (m := 0) (preparation_free setup source packet owner before)
          rintro ⟨⟨prepared, current⟩, env⟩ _
          cases prepared with
          | fail error | div =>
              simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, bind_pure_comp,
                StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                OracleComp.IsQueryBoundP.of_imp (private_of_kem (kind := kind) (KemSK := KemSK))
                  (RegistrationNativeProviderBeaconCaps.abort_zero (KemSK := KemSK) owner current env ())
          | ok prepared => cases prepared with
            | none =>
                simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, bind_pure_comp,
                  StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                  OracleComp.IsQueryBoundP.of_imp (private_of_kem (kind := kind) (KemSK := KemSK))
                    (RegistrationNativeProviderBeaconCaps.abort_zero (KemSK := KemSK) owner current env ())
            | some ready => exact complete_free setup.source owner current ready env

end BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemBeacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemBeacon.collect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemBeacon.collect_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemBeacon.preparation_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemBeacon.preparation_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemBeacon.complete_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemBeacon.complete_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemBeacon.finish_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemBeacon.finish_free
