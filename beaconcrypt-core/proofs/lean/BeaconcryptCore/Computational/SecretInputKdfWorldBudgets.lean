import BeaconcryptCore.Computational.PqxdhSecretInputKdf

/-!
Uniform-query budgets for the existing concrete secret-input root and Extract/HMAC
worlds. The joint sampler and every observer continuation retain their original
ProbComp programs. Counts are upper bounds in uniform oracle calls; arbitrary
finite-range calls count as one, while these fixed byte vectors draw once per byte.
Source HKDF/HMAC evaluation and all other local work are not declared free.
No primitive security premise, source-distribution substitution or hidden ambient
base interface is introduced. The ordinary random HMAC branch samples an output
block and no key; the real branch samples its actual 64-byte key.
-/

open OracleComp OracleSpec
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.SecretInputKdfWorldBudgets
open PqxdhSecretInputKdf PqxdhJointKdfGame

/-- The ordinary real PRF game charges its actual 64-byte key before the full sampler and observer. -/
theorem hmac_real {Context : Type} (hmac : HmacSha512)
    (sample : SecretInputSampler Context) (observer : RootObserver Context) (qSample qObserver : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context root, (observer context root).IsTotalQueryBound qObserver) :
    (hmacPrfRealGame hmac (expandReduction sample observer)).IsTotalQueryBound
      (qSample + 64 + qObserver) := by
  unfold hmacPrfRealGame
  simp only [expandReduction_real]
  have bound := isTotalQueryBound_bind (uniformFixedBytes_isTotalQueryBound 64)
    (fun key => isTotalQueryBound_bind sampleBound (fun pair => observerBound pair.1 (expandRoot hmac key)))
  have budget : 64 + (qSample + qObserver) = qSample + 64 + qObserver := by omega
  rwa [budget] at bound

/-- Actual source root evaluation adds local deterministic work but no uniform request. -/
theorem source_root {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : SecretInputSampler Context) (observer : RootObserver Context) (qSample qObserver : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context root, (observer context root).IsTotalQueryBound qObserver) :
    (sourceRootGame source sample observer).IsTotalQueryBound (qSample + qObserver) := by
  unfold sourceRootGame
  apply isTotalQueryBound_bind sampleBound
  rintro ⟨context, input⟩
  exact observerBound _ _

/-- The real Extract reduction evaluates the actual deterministic Extract/Expand functions before the same observer. -/
theorem extract_real {Context : Type} (hmac : HmacSha512)
    (sample : SecretInputSampler Context) (observer : RootObserver Context) (qSample qObserver : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context root, (observer context root).IsTotalQueryBound qObserver) :
    (extractRealGame hmac sample (extractReduction hmac observer)).IsTotalQueryBound
      (qSample + qObserver) := by
  unfold extractRealGame extractReduction
  apply isTotalQueryBound_bind sampleBound
  rintro ⟨context, input⟩
  exact observerBound _ _

/-- The independent root costs 32 byte-valued uniform draws in addition to the unchanged joint sampler and observer. -/
theorem independent_root {Context : Type}
    (sample : SecretInputSampler Context) (observer : RootObserver Context) (qSample qObserver : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context root, (observer context root).IsTotalQueryBound qObserver) :
    (independentRootGame sample observer).IsTotalQueryBound (qSample + 32 + qObserver) := by
  rw [Nat.add_assoc]
  unfold independentRootGame
  apply isTotalQueryBound_bind sampleBound
  rintro ⟨context, input⟩
  exact isTotalQueryBound_bind (uniformFixedBytes_isTotalQueryBound 32) (observerBound context)

/-- The uniform Extract game samples all 64 PRK bytes; the whole actual local Expand/observer continuation remains. -/
theorem extract_uniform {Context : Type} (hmac : HmacSha512)
    (sample : SecretInputSampler Context) (observer : RootObserver Context) (qSample qObserver : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context root, (observer context root).IsTotalQueryBound qObserver) :
    (extractUniformGame sample (extractReduction hmac observer)).IsTotalQueryBound
      (qSample + 64 + qObserver) := by
  rw [Nat.add_assoc]
  unfold extractUniformGame extractReduction
  apply isTotalQueryBound_bind sampleBound
  rintro ⟨context, input⟩
  exact isTotalQueryBound_bind (uniformFixedBytes_isTotalQueryBound 64)
    (fun key => observerBound context (expandRoot hmac key))

/-- The ordinary random PRF game samples one fresh 64-byte output and no secret key; original sampler and observer coins remain. -/
theorem hmac_random {Context : Type}
    (sample : SecretInputSampler Context) (observer : RootObserver Context) (qSample qObserver : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context root, (observer context root).IsTotalQueryBound qObserver) :
    (hmacPrfRandomGame (expandReduction sample observer)).IsTotalQueryBound
      (qSample + 64 + qObserver) := by
  rw [expandReduction_random, Nat.add_assoc]
  apply isTotalQueryBound_bind sampleBound
  rintro ⟨context, input⟩
  exact isTotalQueryBound_bind (uniformFixedBytes_isTotalQueryBound 64)
    (fun block => observerBound context (first32 block))

end BeaconcryptCore.Computational.SecretInputKdfWorldBudgets

/--
info: 'BeaconcryptCore.Computational.SecretInputKdfWorldBudgets.hmac_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.SecretInputKdfWorldBudgets.hmac_real

/--
info: 'BeaconcryptCore.Computational.SecretInputKdfWorldBudgets.source_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.SecretInputKdfWorldBudgets.source_root

/--
info: 'BeaconcryptCore.Computational.SecretInputKdfWorldBudgets.extract_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.SecretInputKdfWorldBudgets.extract_real

/--
info: 'BeaconcryptCore.Computational.SecretInputKdfWorldBudgets.independent_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.SecretInputKdfWorldBudgets.independent_root

/--
info: 'BeaconcryptCore.Computational.SecretInputKdfWorldBudgets.extract_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.SecretInputKdfWorldBudgets.extract_uniform

/--
info: 'BeaconcryptCore.Computational.SecretInputKdfWorldBudgets.hmac_random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.SecretInputKdfWorldBudgets.hmac_random
