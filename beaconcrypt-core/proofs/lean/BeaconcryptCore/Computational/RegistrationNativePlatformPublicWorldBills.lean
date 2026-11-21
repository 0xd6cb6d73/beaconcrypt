-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalCaps
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyExecution
import BeaconcryptCore.Computational.RegistrationNativeRestrictedCosts
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldBills
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (WorldSpec EnvEffects EffectKind effectKind effectLift)
open PqxdhRecordLiftBudget (WorldEffect)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_add weighted_indicator)
open RegistrationNativePrimitiveCosts (coinCost)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePlatformPublicFrontend (Spec)
variable {n : Nat} {I KemSK ProviderState A : Type} {base : OracleSpec I}
def nativeBill (qSign qKem : Nat) (kind : EffectKind) : (Spec n KemSK).Domain → Nat
  | .inl query => RegistrationNativeRestrictedCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind
  | .inr _ => 0
def bill (qSign qKem : Nat) (kind : EffectKind) : (Spec n KemSK).Domain → Nat
  | .inl query => RegistrationNativeRestrictedCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind
  | .inr _ => coinCost 1 kind
/-- Old/global and external platform coins are billed independently before closing the same actual World tree. -/
theorem combine_bound (qSign qKem : Nat) (kind : EffectKind) (work : OracleComp (Spec n KemSK) A)
    (nativeCap externalCap : Nat) (native : Weighted (nativeBill (n := n) (KemSK := KemSK) qSign qKem kind) work nativeCap)
    (external : work.IsQueryBoundP (RegistrationNativePlatformPublicExternalLocal.IsExternal (KemSK := KemSK)) externalCap) :
    Weighted (bill (n := n) (KemSK := KemSK) qSign qKem kind) work (nativeCap + coinCost externalCap kind) := by
  have counted := weighted_indicator RegistrationNativePlatformPublicExternalLocal.IsExternal (coinCost 1 kind) work externalCap external
  have combined := weighted_add _ _ work nativeCap (coinCost 1 kind * externalCap) native counted
  convert combined using 1
  · funext query
    cases query <;> simp [bill, nativeBill, RegistrationNativePlatformPublicExternalLocal.IsExternal]
  · cases kind <;> simp [coinCost]
private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (fun v => (v, before)) <$> work := bind_pure_comp _ _
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
variable (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
variable (qSign qKem : Nat) (signing : ∀ request, (sign request).IsTotalQueryBound qSign)
variable (kem : ∀ query before, ((provider query).run before).IsTotalQueryBound qKem)
include signing kem in
/-- Each individual actual selective interpreter leaf has its derived shared-World effect bill; material demand has a conservative108-byte ceiling and external allocation draws stay explicit. -/
theorem query_bound (query : (Spec n KemSK).Domain)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) (kind : EffectKind) :
    ((RegistrationNativePlatformSelectiveEntropyBackend.handler setup wire sign seed scalar candidate provider query).run before).IsQueryBoundP
      (WorldEffect kind) (bill (n := n) (KemSK := KemSK) qSign qKem kind query) := by
  cases query with
  | inl query => cases query with
    | inl nativeQuery =>
      change ((RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider (.inl nativeQuery)).run before).IsQueryBoundP _ _
      rw [← RegistrationNativeSelectiveEntropyBackend.local_query setup wire sign seed scalar candidate provider nativeQuery before]
      have bounded := RegistrationNativeRestrictedCosts.restricted_bound setup wire sign seed scalar candidate provider qSign qKem signing kem (.inl nativeQuery) before kind
      apply RawCtxSourceOpen.simulate_bound _ (fun query => effectKind query = kind) _ _ _ bounded
      intro effect
      simp only [effectLift, WorldEffect, isQueryBoundP_query_iff]
      intro hit
      simp [hit]
    | inr record =>
      simp only [RegistrationNativePlatformSelectiveEntropyBackend.handler, RegistrationNativeSelectiveHiddenInterpreter.handler,
        RegistrationNativeSelectiveHiddenInterpreter.onBase, RegistrationNativeHiddenInterpreter.handler, StateT.run,
        lift_apply, isQueryBoundP_map_iff, bill, RegistrationNativeRestrictedCosts.bill]
      simp [WorldEffect, isQueryBoundP_query_iff]
  | inr coin =>
    cases kind <;> simp [RegistrationNativePlatformSelectiveEntropyBackend.handler, StateT.run_lift, bind_pure_comp,
      bill, coinCost, PqxdhRecordLiftInterface.coinLift, WorldEffect, effectKind,
      isQueryBoundP_map_iff, isQueryBoundP_query_iff]
include signing kem in
/-- Every adaptive source query tree retains its full selective private state when the individually derived native and platform bills close to the World. -/
theorem program_bound (work : OracleComp (Spec n KemSK) A) (bound : Nat) (kind : EffectKind)
    (bounded : Weighted (bill (n := n) (KemSK := KemSK) qSign qKem kind) work bound)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) :
    ((simulateQ (RegistrationNativePlatformSelectiveEntropyBackend.handler setup wire sign seed scalar candidate provider) work).run before).IsQueryBoundP
      (WorldEffect kind) bound :=
  PqxdhRecordLiftCtxBills.run_bound _ _ _
    (fun query current => query_bound setup wire sign seed scalar candidate provider qSign qKem signing kem query current kind)
    work bound bounded before
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldBills

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldBills.combine_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldBills.combine_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldBills.query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldBills.query_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldBills.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldBills.program_bound
