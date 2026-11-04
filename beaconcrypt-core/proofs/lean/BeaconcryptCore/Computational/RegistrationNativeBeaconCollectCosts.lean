-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeCreateCosts
import BeaconcryptCore.Computational.RegistrationNativeReferenceCosts

/-! The actual root-free Beacon prefix has twelve source callback slots. Ordinary conversion/DH are local source functions, typed decapsulation retains the indexed primitive service and its optional failure, and both selected prekey visits retain their metadata updates. This conservative bill charges each source slot one indexed KEM allowance and charges no hashes or administrative capability. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconCollectCosts
open PqxdhRecordLiftInterface (EffectKind)
open RegistrationNativePrimitiveCosts (coinCost)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_mono weighted_run weighted_indicator)
open RegistrationNativeWeightedContext (query_bound map_bound)
open RegistrationNativeReferenceCosts (bill)
open RegistrationBeaconReferenceCompiler (SelectedOwner Spec)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}

private theorem other_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (qSign qKem : Nat) (kind : EffectKind) (query : RegistrationNativeKemInterface.OtherSpec.Domain) :
    Weighted (fun query => bill (n := n) qSign qKem query kind)
      (RegistrationBeaconReferenceCompiler.other setup owner oneTime query) 0 := by
  cases query with
  | convertPublic key =>
      simp only [RegistrationBeaconReferenceCompiler.other, RegistrationNativeKemInterface.OtherRequest.primitive,
        RegistrationBeaconRoleBackend.localBackend,
        RegistrationBeaconReferenceCompiler.sample]
      trivial
  | convertSecret role =>
      cases role <;> simp only [RegistrationBeaconReferenceCompiler.other, RegistrationNativeKemInterface.OtherRequest.primitive,
        RegistrationBeaconRoleBackend.localBackend, StateT.run,
        RegistrationBeaconReferenceCompiler.sample]
      all_goals trivial
  | generate role =>
      simp only [RegistrationBeaconReferenceCompiler.other, RegistrationNativeKemInterface.OtherRequest.primitive,
        RegistrationBeaconRoleBackend.localBackend,
        RegistrationBeaconReferenceCompiler.sample]
      trivial
  | dh request =>
      cases role : request.secret_role <;> simp only [RegistrationBeaconReferenceCompiler.other, RegistrationNativeKemInterface.OtherRequest.primitive,
        RegistrationBeaconRoleBackend.localBackend, StateT.run, role,
        RegistrationBeaconReferenceCompiler.sample]
      all_goals trivial

set_option backward.isDefEq.respectTransparency false in
private theorem primitive_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (qSign qKem : Nat) (kind : EffectKind)
    (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    Weighted (fun query => bill (n := n) qSign qKem query kind)
      (RegistrationBeaconReferenceCompiler.primitive setup owner oneTime query) (coinCost qKem kind) := by
  cases query with
  | convertPublic key | convertSecret key | generate key | dh key =>
      all_goals simp only [RegistrationBeaconReferenceCompiler.primitive, RegistrationNativeKemInterface.beacon,
        RegistrationNativeKemInterface.other, simulateQ_spec_query]
      all_goals exact weighted_mono _ _ 0 _ (other_bound setup owner oneTime qSign qKem kind _) (Nat.zero_le _)
  | encapsulate key => trivial
  | decapsulate ciphertext =>
      cases ciphertext with
      | none => trivial
      | some ciphertext =>
          simp only [RegistrationBeaconReferenceCompiler.primitive, RegistrationNativeKemInterface.beacon,
            simulateQ_map, simulateQ_spec_query, RegistrationBeaconReferenceCompiler.indexed]
          exact map_bound _ _ _ _ (query_bound _ _)

/-- Each original agreement callback retains the full chronological native request state and its optional indexed decapsulation. -/
theorem backend_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (qSign qKem : Nat) (kind : EffectKind)
    (query : RegistrationAgreementExecutor.Spec.Domain) (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Weighted (fun query => bill (n := n) qSign qKem query kind)
      ((RegistrationBeaconReferenceCompiler.backend setup owner oneTime query).run before) (coinCost qKem kind) := by
  simp only [RegistrationBeaconReferenceCompiler.backend, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_lift, bind_pure_comp]
  apply map_bound
  cases query <;> first
    | exact primitive_bound setup owner oneTime qSign qKem kind _
    | trivial

set_option backward.isDefEq.respectTransparency false in
private theorem auxiliary_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (qSign qKem : Nat) (kind : EffectKind) (query : RegistrationBeaconRootInterpreter.AuxSpec.Domain)
    (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Weighted (fun query => bill (n := n) qSign qKem query kind)
      ((RegistrationBeaconRootInterpreter.auxImpl (RegistrationBeaconReferenceCompiler.backend setup owner oneTime) authenticated query).run before)
      (coinCost qKem kind) := by
  cases query <;> simp only [RegistrationBeaconRootInterpreter.auxImpl, RegistrationBeaconAgreementRoot.callbacks,
    simulateQ_pure, simulateQ_map, simulateQ_spec_query, StateT.run_pure, StateT.run_map]
  all_goals first
    | trivial
    | exact map_bound _ _ _ _ (backend_bound setup owner oneTime qSign qKem kind _ before)

/-- Every actual root-free collection branch, including failed decapsulation, has the twelve-slot source allowance. -/
theorem collect_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (qSign qKem : Nat) (kind : EffectKind) (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Weighted (fun query => bill (n := n) qSign qKem query kind)
      ((RegistrationBeaconReferenceCompiler.collect setup owner oneTime authenticated).run before) (coinCost qKem kind * 12) := by
  unfold RegistrationBeaconReferenceCompiler.collect
  apply weighted_run (fun _ => coinCost qKem kind) _ _ _ _ before
  · simpa only [ite_true] using weighted_indicator (fun _ => True) (coinCost qKem kind) _ 12
      ((isQueryBoundP_true_iff _ _).mpr (PqxdhPhase2DhMetadata.prepare_bound _ _ _ _ _))
  · intro query current
    cases query <;> simp only [PqxdhPhase2GapDhSource.prefixImpl]
    all_goals first
      | exact auxiliary_bound setup owner oneTime authenticated qSign qKem kind _ current
      | trivial

end BeaconcryptCore.Computational.RegistrationNativeBeaconCollectCosts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCollectCosts.backend_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCollectCosts.backend_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCollectCosts.collect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCollectCosts.collect_bound
