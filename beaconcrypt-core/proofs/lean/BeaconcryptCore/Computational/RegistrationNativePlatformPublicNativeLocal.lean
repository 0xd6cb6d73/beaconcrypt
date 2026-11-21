-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldBills
import BeaconcryptCore.Computational.RegistrationNativeCreateCosts
import BeaconcryptCore.Computational.RegistrationNativeReferenceCosts
/-! Native/global weighted bills cross the actual new local embedding without charging external platform coins. Actual source samplers retain separate primitive allowances and every mutable platform poststate. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeLocal
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_simulate weighted_run weighted_indicator)
open RegistrationNativePlatformPublicFrontend (Spec LocalSpec Base localQuery localHandler trusted)
open PqxdhRecordLiftInterface (EffectKind)
open RegistrationNativePlatformPublicWorldBills (nativeBill)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I}

def bill (qSign qKem : Nat) (kind : EffectKind) : (LocalSpec n KemSK).Domain → Nat
  | .inl query => RegistrationNativeRestrictedCosts.bill (KemSK := KemSK) qSign qKem (.inl query) kind
  | .inr _ => 0

/-- Local/source repacking preserves the complete native weighted bill. -/
theorem embed_bound (qSign qKem : Nat) (kind : EffectKind) (work : OracleComp (LocalSpec n KemSK) A) (cap : Nat)
    (bounded : Weighted (bill qSign qKem kind) work cap) :
    Weighted (nativeBill qSign qKem kind) (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal work) cap := by
  apply weighted_simulate _ _ _ _ _ bounded
  intro query
  cases query <;> simp [Weighted, RegistrationNativePlatformPublicFrontend.embedLocal,
    RegistrationNativePlatformPublicFrontend.publicCoin, nativeBill, bill, isQueryBound_query_iff]

/-- The selected indexed route changes no literal reference capability bill. -/
theorem local_query (qSign qKem : Nat) (kind : EffectKind) (selected : Bool)
    (query : (RegistrationBeaconReferenceCompiler.Spec n KemSK).Domain) :
    Weighted (bill qSign qKem kind) (localQuery selected query) (RegistrationNativeReferenceCosts.bill qSign qKem query kind) := by
  rcases query with message | (publication | kem)
  · simp [Weighted, localQuery, bill, RegistrationNativeReferenceCosts.bill,
      RegistrationNativeRestrictedCosts.bill, isQueryBound_query_iff]
  · rcases publication with message | (publication | effect)
    all_goals simp [Weighted, localQuery, bill, RegistrationNativeReferenceCosts.bill,
      RegistrationNativeRestrictedCosts.bill, isQueryBound_query_iff]
  · rcases kem with ordinary | (privateQuery | ciphertext)
    all_goals cases selected <;> simp [Weighted, localQuery, RegistrationNativeKemRouting.route,
      bill, RegistrationNativeReferenceCosts.bill, RegistrationNativeRestrictedCosts.bill, isQueryBound_query_iff]

/-- The actual local StateT dictionary keeps arbitrary P values alongside the source bill. -/
theorem local_program (qSign qKem : Nat) (kind : EffectKind) (selected : Bool)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A) (cap : Nat)
    (bounded : Weighted (fun query => RegistrationNativeReferenceCosts.bill qSign qKem query kind) work cap) (previous : Platform) :
    Weighted (bill qSign qKem kind) ((simulateQ (localHandler selected) work).run previous) cap := by
  apply weighted_run _ _ _ _ _ _ bounded
  intro query current
  simpa only [localHandler, StateT.run_lift, bind_pure_comp, Weighted, isQueryBound_map_iff] using
    local_query qSign qKem kind selected query

private theorem zero {I A : Type} {spec : OracleSpec I} (work : OracleComp spec A) :
    Weighted (fun _ => 0) work 0 := by
  simpa only [ite_false] using weighted_indicator (fun _ => False) 1 work 0 (isQueryBoundP_false work 0)

/-- Arbitrary external platform sampler effects have zero old/global bill. -/
theorem platform_zero (qSign qKem : Nat) (kind : EffectKind) (work : StateT Platform ProbComp A) (previous : Platform) :
    Weighted (bill (n := n) (KemSK := KemSK) qSign qKem kind)
      ((RegistrationNativePlatformPublicFrontend.platform work).run previous) 0 := by
  apply weighted_simulate (fun _ => 0) _ _ _ _ (zero _)
  intro query
  simp [RegistrationNativePlatformPublicFrontend.localCoin, Weighted, bill, isQueryBound_query_iff]

/-- Every original trusted source program keeps its literal native effect weights in the new common platform stack. -/
theorem trusted_program (qSign qKem : Nat) (kind : EffectKind)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) A) (cap : Nat)
    (bounded : Weighted (RegistrationNativeTrustedCosts.bill qKem kind) work cap) (previous : Platform) :
    Weighted (bill qSign qKem kind) ((simulateQ trusted work).run previous) cap := by
  apply weighted_run _ _ _ _ _ _ bounded
  intro query current
  simp only [trusted, StateT.run_lift, bind_pure_comp, Weighted, isQueryBound_map_iff]
  rcases query with query | (query | (query | key))
  all_goals simp only [RegistrationBeaconReferenceCompiler.trustedLift,
    RegistrationBeaconReferenceCompiler.effect, RegistrationBeaconReferenceCompiler.indexed,
    localQuery, RegistrationNativeKemRouting.route, Bool.false_eq_true, ite_false, simulateQ_spec_query]
  all_goals simp [bill, RegistrationNativeTrustedCosts.bill, RegistrationNativeRestrictedCosts.bill, isQueryBound_query_iff]
/-- The literal owner/environment/full-P lens changes no resource query. -/
theorem beacon_bound {source : RegistrationNativeMldsa.Source} (qSign qKem : Nat) (kind : EffectKind)
    (work : RegistrationNativePlatformPublicOwners.M source RegistrationServerRoleBackend.State (Base n KemSK Platform) A)
    (before : RegistrationNativePlatformPublicFrontend.State source Platform) (cap : Nat)
    (bounded : Weighted (bill qSign qKem kind) (((work.run before.1.beacons).run before.1.environment).run before.2) cap) :
    Weighted (nativeBill qSign qKem kind)
      ((RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.beacon work)).run before) cap := by
  change Weighted _ (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
    ((RegistrationNativePlatformPublicFrontend.beacon work).run before)) cap
  apply embed_bound qSign qKem kind
  simpa only [RegistrationNativePlatformPublicFrontend.beacon, StateT.run, Weighted, isQueryBound_map_iff] using bounded
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeLocal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeLocal.embed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeLocal.embed_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeLocal.local_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeLocal.local_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeLocal.local_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeLocal.local_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeLocal.platform_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeLocal.platform_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeLocal.trusted_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeLocal.trusted_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeLocal.beacon_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeLocal.beacon_bound
