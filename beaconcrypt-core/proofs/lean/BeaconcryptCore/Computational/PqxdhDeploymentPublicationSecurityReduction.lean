-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityEvents

/-! Ordinary joint-use weak-EUF reductions and explicit query accounting for the selected unpublished-bundle clients. Each client keeps its real source interface; terminal candidate reports are translated by the existing first-unissued-field monitor. A finite family of selected bundle ordinals needs no extra random draw. -/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityReduction
open PqxdhJointIdentity PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhDynamicIdentityPool PqxdhDynamicIdentityRouting PqxdhDynamicIdentityReports
open PqxdhJointPhase1Reports (ProtocolSpec SourceClass routedClient)
variable {Result : Type}

/-- The target seed remains inside the original ordinary joint-use challenger. The client itself has only public generated handles and the real source operations. -/
noncomputable def reduction (joint : Primitives) (count : Nat) (client : OracleComp ProtocolSpec Result)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery) (target : Fin (count + 1)) :=
  globalReduction joint target ordinaryFallback
    (routedAdversary count ordinaryFallback
      (reportExtractor joint (count + 1) fallback (routedClient joint (count + 1) client)))

/-- The ordinary generated-identity sum recognizes every actual fresh field report of the client, without a field or report-position selection factor. -/
theorem report_bound (joint : Primitives) (count : Nat) (client : OracleComp ProtocolSpec Result)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (creates : client.IsQueryBoundP (SourceClass IsCreate) (count + 1)) :
    Pr{let result ← PqxdhJointPhase1Reports.run joint (count + 1) client}[result.2.1.occurred = true] ≤
      ∑ target : Fin (count + 1), advantage joint (reduction joint count client fallback ordinaryFallback target) :=
  PqxdhJointPhase1Reports.fieldOrigin_advantage_le_sum joint count client fallback ordinaryFallback creates

/-- Exact per-reduction resource caps, including the reserved other identity seeds and the challenger's own seed. -/
def Bills (joint : Primitives) (count : Nat) (client : OracleComp ProtocolSpec Result)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery) (qSign qDh qUniform : Nat)
    (target : Fin (count + 1)) : Prop :=
  (∀ jointPublic : PublicIdentity,
    (reduction joint count client fallback ordinaryFallback target jointPublic).IsQueryBoundP (IsClass .sign) qSign ∧
    (reduction joint count client fallback ordinaryFallback target jointPublic).IsQueryBoundP (IsClass .staticDh) qDh ∧
    (reduction joint count client fallback ordinaryFallback target jointPublic).IsQueryBoundP (IsClass .uniform)
      (32 * count + qUniform)) ∧
  (PqxdhJointIdentity.game joint (reduction joint count client fallback ordinaryFallback target)).IsTotalQueryBound
    (32 * (count + 1) + qUniform)

/-- Source caps transport to the ordinary reductions unchanged; a selected ordinal is an index in the family and spends no uniform query. -/
theorem bills (joint : Primitives) (count : Nat) (client : OracleComp ProtocolSpec Result)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery) (qSign qDh qUniform : Nat)
    (signBound : client.IsQueryBoundP (SourceClass (dynamicClass (IsClass .sign))) qSign)
    (dhBound : client.IsQueryBoundP (SourceClass (dynamicClass (IsClass .staticDh))) qDh)
    (uniformBound : client.IsQueryBoundP (SourceClass (dynamicClass (IsClass .uniform))) qUniform)
    (target : Fin (count + 1)) : Bills joint count client fallback ordinaryFallback qSign qDh qUniform target := by
  refine ⟨fun jointPublic => ⟨?_, ?_, ?_⟩, ?_⟩
  · simpa only [Nat.zero_add, ite_false, reduceCtorEq, reduction] using
      PqxdhJointPhase1Reports.fieldReduction_query_bound joint count target fallback ordinaryFallback client
        .sign qSign signBound jointPublic
  · simpa only [Nat.zero_add, ite_false, reduceCtorEq, reduction] using
      PqxdhJointPhase1Reports.fieldReduction_query_bound joint count target fallback ordinaryFallback client
        .staticDh qDh dhBound jointPublic
  · exact PqxdhJointPhase1Reports.fieldReduction_query_bound joint count target fallback ordinaryFallback client
      .uniform qUniform uniformBound jointPublic
  · exact PqxdhJointPhase1Reports.fieldReductionGame_uniform_bound joint count target fallback ordinaryFallback client
      qUniform uniformBound

/-- The selected-attempt family uses an explicit finite sum; the probability transfer retains the original coefficient of each ordinary identity reduction. -/
theorem family_bound {n : Nat} (joint : Primitives) (count : Nat)
    (clients : Fin n → OracleComp ProtocolSpec Result) (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (creates : ∀ selected, (clients selected).IsQueryBoundP (SourceClass IsCreate) (count + 1)) :
    (∑ selected : Fin n,
      Pr{let result ← PqxdhJointPhase1Reports.run joint (count + 1) (clients selected)}[result.2.1.occurred = true]) ≤
      ∑ selected : Fin n, ∑ target : Fin (count + 1),
        advantage joint (reduction joint count (clients selected) fallback ordinaryFallback target) := by
  exact Finset.sum_le_sum fun selected _ => report_bound joint count (clients selected) fallback ordinaryFallback
    (creates selected)

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityReduction

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityReduction.report_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityReduction.report_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityReduction.bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityReduction.bills

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityReduction.family_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityReduction.family_bound
