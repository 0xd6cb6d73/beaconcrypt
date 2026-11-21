-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSeedDelayCore

/-! Accounting normalization is itself independent of the hidden cache. Consequently the exact normalized native resolve step inherits lazy-query commutation, with its actual role kernel and cache answer retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSeedDelayNormalize
open PqxdhRecordLiftWorld (State)
open RegistrationNativeSeedDelayCore (lens mask normalize)
open LazyOracleDiscard (Commutes)
variable {n : Nat} {Value : Type}

def maskStep : StateT (State n) ProbComp Unit := fun before => pure ((), mask before)

/-- Normalization performs the stated accounting projection before and after the actual step. -/
theorem normalize_eq (work : StateT (State n) ProbComp Value) :
    normalize work = (do
      let _ ← maskStep
      let value ← work
      let _ ← maskStep
      pure value) := by
  funext before
  change Prod.map id mask <$> work.run (mask before) =
    (do let result ← work.run (mask before); pure (result.1, mask result.2))
  rw [bind_pure_comp]
  rfl

/-- Accounting normalization commutes with actual cache completion. -/
theorem mask_commutes : Commutes (lens (n := n)) maskStep := by
  apply LazyOracleDiscard.commutes_frame
  intro before cache
  simp only [maskStep, StateT.run, map_pure, RegistrationNativeSeedDelayCore.mask_set]

/-- A commuting actual step continues to commute under the explicit accounting view. -/
theorem normalize_commutes (work : StateT (State n) ProbComp Value) (commutes : Commutes lens work) :
    Commutes lens (normalize work) := by
  rw [normalize_eq]
  apply LazyOracleDiscard.commutes_bind lens mask_commutes
  intro _
  apply LazyOracleDiscard.commutes_bind lens commutes
  intro value
  apply LazyOracleDiscard.commutes_bind lens mask_commutes
  intro _
  exact LazyOracleDiscard.commutes_pure lens value

/-- All normalized actual resolves commute, including known kernels and a hidden query at the same slot as the completion. -/
theorem resolve_commutes (role : PqxdhRecordLiftInterface.Role) (ref : PqxdhRecordLiftInterface.KernelRef n) :
    Commutes lens (normalize (PqxdhRecordLiftWorld.resolve role ref)) := by
  cases ref with
  | known kernel => exact normalize_commutes (pure kernel) (LazyOracleDiscard.commutes_pure lens kernel)
  | hidden slot =>
      have same : normalize (PqxdhRecordLiftWorld.resolve role (.hidden slot)) =
          normalize (PqxdhRecordLiftWorld.kernel role <$> lens.query slot) := by
        funext before
        exact RegistrationNativeSeedDelayCore.resolve_query role slot before
      rw [same]
      exact normalize_commutes _
        (LazyOracleDiscard.commutes_map lens (PqxdhRecordLiftWorld.kernel role) (LazyOracleDiscard.commutes_query lens slot))

end BeaconcryptCore.Computational.RegistrationNativeSeedDelayNormalize

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayNormalize.normalize_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayNormalize.normalize_eq
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayNormalize.mask_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayNormalize.mask_commutes
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayNormalize.normalize_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayNormalize.normalize_commutes
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayNormalize.resolve_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayNormalize.resolve_commutes
