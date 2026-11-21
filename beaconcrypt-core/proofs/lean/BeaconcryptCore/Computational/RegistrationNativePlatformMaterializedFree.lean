-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocal
import BeaconcryptCore.Computational.RegistrationNativePairedSafe
/-! Literal query bills derive when actual ordinary callbacks are unchanged by known/opaque materialization. No source identity or alias-exclusion conclusion is a premise: the helper uses only zero material-demand and installation syntax. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFree
open RegistrationNativePublicFrontend (Spec)
open RegistrationNativePairedSafe (GlobalInstall)
open RegistrationNativePublicCaps (IsDemand)
open RegistrationNativeG3AuditedWorld (Seeds)
variable {n : Nat} {KemSK A : Type}

private theorem query_free (full : Bool) (seeds : Seeds n) (query : (Spec n KemSK).Domain)
    (ordinary : ¬ IsDemand (n := n) (KemSK := KemSK) query)
    (noInstall : ∀ role, ¬ GlobalInstall (n := n) (KemSK := KemSK) role query) :
    RegistrationNativeG3MaterializedLocal.translate full seeds query = (Spec n KemSK).query query := by
  rcases query with (prepare | (demand | (publication | environment)) | kem) | record
  · rfl
  · exact (ordinary trivial).elim
  · rfl
  · cases environment with
    | inl coin => rfl
    | inr capability => cases capability with
      | installServer keyId binding kernel => exact (noInstall .server rfl).elim
      | installBeacon owner shell kernel => exact (noInstall .beacon rfl).elim
      | _ => rfl
  · rfl
  · rfl

/-- The complete actual free source tree is unchanged when it has no material demand or installation request; arbitrary ordinary replies and external-coin embeddings remain literal. -/
theorem program_free (full : Bool) (seeds : Seeds n) (work : OracleComp (Spec n KemSK) A)
    (ordinary : work.IsQueryBoundP (IsDemand (n := n) (KemSK := KemSK)) 0)
    (noInstall : ∀ role, work.IsQueryBoundP (GlobalInstall (n := n) (KemSK := KemSK) role) 0) :
    simulateQ (RegistrationNativeG3MaterializedLocal.translate full seeds) work = work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    have plain := (isQueryBoundP_query_bind_iff _ _ _ _).mp ordinary
    have zero := fun role => (isQueryBoundP_query_bind_iff _ _ _ _).mp (noInstall role)
    have ordinaryHead : ¬ IsDemand (n := n) (KemSK := KemSK) query := plain.1.resolve_right (by omega)
    have noInstallHead : ∀ role, ¬ GlobalInstall (n := n) (KemSK := KemSK) role query := fun role => (zero role).1.resolve_right (by omega)
    simp only [simulateQ_bind, simulateQ_spec_query, query_free full seeds query ordinaryHead noInstallHead]
    congr 1
    funext reply
    apply ih reply
    · simpa only [Nat.zero_sub, ite_self] using plain.2 reply
    · intro role
      simpa only [Nat.zero_sub, ite_self] using (zero role).2 reply
end BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFree

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFree.program_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFree.program_free
