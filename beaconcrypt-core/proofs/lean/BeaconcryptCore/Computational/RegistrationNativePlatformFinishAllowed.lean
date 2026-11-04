-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeTrustedAllowed
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinish
/-! The corrected assigned-ID finish lowers every role primitive before its trusted interface. Its checked query restriction includes all authentication, agreement, record, copy and installation outcomes; no completed controller equation is required. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformFinishAllowed
open RegistrationNativeBeaconFrontend (M Trusted Owner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeKemBeaconFootprint (Kind counted Bounded effect_zero sample_zero simulate_zero)
variable {n : Nat} {ι KemSK Auxiliary Value Result : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
private theorem pure_bound (kind : Kind) (cap : Nat) (value : Value) :
    Bounded (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) kind cap (pure value) := by
  intro owners environment
  simp only [StateT.run_pure, isQueryBoundP_pure]

private theorem bind_bound (kind : Kind) (left right : Nat) (first : M n KemSK source Auxiliary Value)
    (next : Value → M n KemSK source Auxiliary Result)
    (initial : Bounded kind left first) (later : ∀ value, Bounded kind right (next value)) :
    Bounded kind (left + right) (first >>= next) := by
  intro owners environment
  change (((first.run owners).run environment) >>= fun middle =>
    (((next middle.1.1).run middle.1.2).run middle.2)).IsQueryBoundP (counted (n := n) (KemSK := KemSK) kind) (left + right)
  exact isQueryBoundP_bind (initial owners environment) (fun middle _supported => later middle.1.1 middle.1.2 middle.2)

private theorem bind_zero (kind : Kind) (first : M n KemSK source Auxiliary Value)
    (next : Value → M n KemSK source Auxiliary Result)
    (initial : Bounded kind 0 first) (later : ∀ value, Bounded kind 0 (next value)) :
    Bounded kind 0 (first >>= next) := bind_bound kind 0 0 first next initial later

private theorem env_zero (kind : Kind) (change : EnvState Auxiliary → EnvState Auxiliary) :
    Bounded (n := n) (KemSK := KemSK) (source := source) kind 0
      (RegistrationNativeBeaconFrontend.updateEnv change) := by
  intro owners environment
  simp [RegistrationNativeBeaconFrontend.updateEnv, StateT.run_lift, StateT.run_map]

private theorem modify_zero (kind : Kind)
    (change : RegistrationNativeBeaconFrontend.State source → RegistrationNativeBeaconFrontend.State source) :
    Bounded (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) kind 0 (modify change) := by
  intro owners environment
  simp [StateT.run_modify, StateT.run_pure]

private theorem get_zero (kind : Kind) :
    Bounded (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) kind 0 get := by
  intro owners environment
  simp [StateT.run_get, StateT.run_pure]

private theorem hash_zero (kind : Kind) (request : registration.HashRequest) :
    Bounded (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.hash request) := effect_zero kind _

private theorem map_zero (kind : Kind) (project : Value → Result) (work : M n KemSK source Auxiliary Value)
    (bounded : Bounded kind 0 work) : Bounded kind 0 (project <$> work) := by
  rw [map_eq_bind_pure_comp]
  exact bind_zero kind work _ bounded (fun _ => pure_bound kind 0 _)

private theorem authentication_zero (setup : PqxdhServerAuthExperiment.Setup base KemSK) (kind : Kind)
    (query : RegistrationAuthenticationExecutor.Spec.Domain) :
    Bounded (n := n) (source := source) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.authentication setup source query) := by
  cases query with
  | hash request =>
      unfold RegistrationNativeBeaconFrontend.authentication
      exact bind_zero kind _ _ (hash_zero kind _) (fun _ => pure_bound kind 0 _)
  | mldsa request | ed25519 request => exact pure_bound kind 0 _

private theorem decapsulate_zero (kind : Kind) (handle : Nat) (ciphertext : PqxdhKemIndCca.MlKem768Ciphertext) :
    Bounded (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.kem (.inr (.inl (.decapsulate handle ciphertext)))) := by
  intro owners environment
  simp [RegistrationNativeBeaconFrontend.kem, StateT.run_lift, StateT.run_map,
    isQueryBoundP_map_iff, isQueryBoundP_query_iff, counted]

private theorem primitive_zero (setup : PqxdhServerAuthExperiment.Setup base KemSK) (kind : Kind)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    Bounded (n := n) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.primitive setup owner oneTime query) := by
  cases query with
  | convertPublic key | convertSecret key | generate key | dh key =>
      simp only [RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon,
        RegistrationNativeKemInterface.other, simulateQ_spec_query]
      exact sample_zero kind _
  | encapsulate key =>
      simp only [RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon, simulateQ_pure]
      exact pure_bound kind 0 _
  | decapsulate ciphertext =>
      cases ciphertext with
      | none =>
          simp only [RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon, simulateQ_pure]
          exact pure_bound kind 0 _
      | some ciphertext =>
          simp only [RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon,
            simulateQ_map, simulateQ_spec_query]
          exact map_zero kind _ _ (decapsulate_zero kind owner.kemHandle _)

private theorem agreement_zero (setup : PqxdhServerAuthExperiment.Setup base KemSK) (kind : Kind)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Spec.Domain) :
    Bounded (n := n) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.agreement setup owner oneTime query) := by
  unfold RegistrationNativeBeaconFrontend.agreement
  apply bind_zero kind _ _ (env_zero kind _)
  intro recorded
  cases query <;> first
    | exact primitive_zero setup kind owner oneTime _
    | exact pure_bound kind 0 _

private theorem record_zero (setup : PqxdhServerAuthExperiment.Setup base KemSK) (kind : Kind)
    (wire : RegistrationNativeWire.Wire) (query : RegistrationRecordPrimitives.Spec.Domain) :
    Bounded (n := n) (source := source) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.record setup wire query) := by
  unfold RegistrationNativeBeaconFrontend.record
  apply bind_zero kind _ _ (env_zero kind _)
  intro recorded
  cases query <;> first
    | exact bind_zero kind _ _ (hash_zero kind _) (fun _ => pure_bound kind 0 _)
    | exact sample_zero kind _

private theorem abort_zero (kind : Kind) (owner : Owner source) :
    Bounded (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.abort owner) :=
  bind_zero kind _ _ (effect_zero kind _) (fun _ => pure_bound kind 0 _)


private theorem install_zero (kind : Kind) (index : Nat) (owner : Owner source) (completed : registration.CompletedBeacon) :
    Bounded (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativePlatformBeaconFinish.install index owner completed) := by
  rw [RegistrationNativePlatformBeaconFinish.install_exact]
  apply bind_zero kind _ _ (effect_zero kind _)
  intro installed
  split
  · exact bind_zero kind _ _ (modify_zero kind _) (fun _ => pure_bound kind 0 _)
  · exact bind_zero kind _ _ (abort_zero kind owner) (fun _ => pure_bound kind 0 _)

private theorem finish_zero (setup : PqxdhServerAuthExperiment.Setup base KemSK) (kind : Kind)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    Bounded (n := n) (source := source) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet) := by
  unfold RegistrationNativePlatformBeaconFinish.finish RegistrationNativePlatformBeaconFinish.finishWith
  apply bind_zero kind _ _ (get_zero kind)
  intro owners
  repeat first
    | exact pure_bound kind 0 _
    | (apply bind_zero kind _ _ (modify_zero kind _); intro changed)
    | (apply bind_zero kind _ _ (abort_zero kind _); intro aborted)
    | exact install_zero kind _ _ _
    | (unfold RegistrationNativePlatformBeaconFinish.afterAuthenticationWith)
    | (apply bind_zero kind _ _ (simulate_zero RegistrationAuthenticationExecutor.Spec kind _ (fun query => authentication_zero setup kind query) _); intro authenticated)
    | (apply bind_zero kind _ _ (simulate_zero RegistrationAgreementExecutor.Spec kind _ (fun query => agreement_zero setup kind _ _ query) _); intro agreed)
    | (apply bind_zero kind _ _ (simulate_zero RegistrationRecordPrimitives.Spec kind _ (fun query => record_zero setup kind wire query) _); intro opened)
    | split

/-- The whole corrected finish exposes only actual public World work and indexed private decapsulation. -/
theorem finish (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : EnvState Auxiliary) :
    (((RegistrationNativePlatformBeaconFinish.finish (n := n) setup source wire index packet).run owners).run env).AllQueriesSatisfy
      (RegistrationNativePublicSourceTrusted.Allowed (KemSK := KemSK)) := by
  classical
  apply (isQueryBoundP_zero_iff _ (RegistrationNativePublicSourceTrusted.Allowed (KemSK := KemSK))).mp
  apply (isQueryBoundP_congr_pred (fun query => show counted (n := n) (KemSK := KemSK) .other query ↔
    ¬ RegistrationNativePublicSourceTrusted.Allowed query from ?_)).mp (finish_zero setup .other wire index packet owners env)
  rcases query with environment | other | (pool | key)
  · simp [counted, RegistrationNativePublicSourceTrusted.Allowed]
  · simp [counted, RegistrationNativePublicSourceTrusted.Allowed]
  · cases pool <;> simp [counted, RegistrationNativePublicSourceTrusted.Allowed]
  · simp [counted, RegistrationNativePublicSourceTrusted.Allowed]
end BeaconcryptCore.Computational.RegistrationNativePlatformFinishAllowed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFinishAllowed.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFinishAllowed.finish
