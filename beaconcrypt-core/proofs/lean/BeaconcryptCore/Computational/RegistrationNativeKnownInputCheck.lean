-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProtectedInputs

/-! A post-run test of an attacker-computable candidate first DH uses a newly chosen KEM suffix, rather than reusing an adaptively selected old PRK input. The test is an ordinary native related-family client: it has neither selected secret nor a private protection test. Real evaluation always agrees with public fixed Extract. A fresh protected ideal input instead supplies an independent64-byte block; collisions with prior literal addresses are bounded separately before the new suffix draw. -/
open OracleComp OracleSpec CoreModels ENNReal Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKnownInputCheck
open PqxdhJointIdentity (Primitives IdentitySeed DhOutput)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhSecretInputKdf (HmacBlock HmacSha512 extract zeroSalt)
open RegistrationNativeRelatedFamily (Spec State input)

def zero : DhOutput := List.Vector.replicate 32 0

def message (first suffix : DhOutput) : RegistrationNativeRelatedFamily.Message :=
  RegistrationNativeRelatedRoot.suppliedMessage first zero zero zero suffix

def bytes (first suffix : DhOutput) : Pqxdh.Bytes :=
  PqxdhJointGapDh.assemble (RegistrationNativeRelatedFamily.address (message first suffix)) first zero

/-- The candidate test input is completely known and does not evaluate either selected DH key. -/
theorem input_known (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (first suffix : DhOutput) : input joint dh seed scalar (message first suffix) = some (bytes first suffix) := rfl

/-- This ordinary client uses the same public fixed-HMAC oracle and the actual related-family Extract query. -/
noncomputable def checkAt (first suffix : DhOutput) : OracleComp Spec Bool := do
  let derived : Option HmacBlock ← Spec.query (.inr (.derive (message first suffix)))
  let fixed : HmacBlock ← Spec.query (.inr (.publicHmac zeroSalt (bytes first suffix)))
  pure (decide (derived ≠ some fixed))

def coins : QueryImpl unifSpec (OracleComp Spec) := fun query => Spec.query (.inl query)

noncomputable def check (first : DhOutput) : OracleComp Spec Bool := do
  let suffix ← simulateQ coins ($ᵗ DhOutput)
  checkAt first suffix

/-- Every real test is false, even after an arbitrary earlier native protocol execution and private cache. -/
theorem real_false (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (first suffix : DhOutput) (before : State) :
    (simulateQ (RegistrationNativeRelatedFamily.realImpl hmac joint dh seed scalar) (checkAt first suffix)).run' before = pure false := by
  simp only [checkAt, StateT.run'_eq, simulateQ_bind, simulateQ_spec_query,
    RegistrationNativeRelatedFamily.realImpl, RegistrationNativeRelatedFamily.impl, input_known joint dh seed scalar first suffix,
    RegistrationNativeRelatedFamily.actualExtract, StateT.run, StateT.monad_bind_def, StateT.bind, pure_bind, simulateQ_pure,
    StateT.monad_pure_def, StateT.pure, map_pure, extract, ne_eq, not_true_eq_false, decide_false]

/-- A matching known first DH makes the new literal descriptor protected; no equality of public encodings is inferred. -/
theorem protected_input (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (first suffix : DhOutput) (matching : joint.staticDh seed (dh.publicKey scalar) = some first) :
    RegistrationNativeRelatedFamily.Protected (joint.staticDh seed (dh.publicKey scalar)) (bytes first suffix) := by
  apply (RegistrationNativeRelatedFamily.input_protected_iff joint dh seed scalar (message first suffix)
    (bytes first suffix) (input_known joint dh seed scalar first suffix)).mpr
  exact matching.symm

/-- A fresh matching ideal test compares an independent complete64-byte PRK with the known fixed evaluation. No independence of the earlier original root input is assumed. -/
theorem ideal_fresh (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (first suffix : DhOutput) (before : State)
    (matching : joint.staticDh seed (dh.publicKey scalar) = some first)
    (fresh : before.cache (bytes first suffix) = none) :
    (simulateQ (RegistrationNativeRelatedFamily.idealImpl hmac joint dh seed scalar) (checkAt first suffix)).run' before =
      (fun prk : HmacBlock => decide (prk ≠ extract hmac (bytes first suffix))) <$> ($ᵗ HmacBlock) := by
  simp only [checkAt, StateT.run'_eq, simulateQ_bind, simulateQ_spec_query, map_bind,
    RegistrationNativeRelatedFamily.idealImpl, RegistrationNativeRelatedFamily.impl,
    input_known joint dh seed scalar first suffix, StateT.run, StateT.monad_bind_def, StateT.bind]
  have freshRun := RegistrationNativeRelatedFamily.protected_miss hmac _ _ _
    (protected_input joint dh seed scalar first suffix matching) fresh
  simp only [StateT.run] at freshRun
  rw [freshRun]
  simp only [simulateQ_pure, StateT.monad_pure_def, StateT.pure,
    map_pure, bind_pure_comp, extract, ne_eq, Functor.map_map, Option.some.injEq]

/-- A fresh protected test's false result has precisely the full64-byte point probability, including when the original candidate was chosen adaptively before this test. -/
theorem ideal_fresh_false (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (first suffix : DhOutput) (before : State)
    (matching : joint.staticDh seed (dh.publicKey scalar) = some first)
    (fresh : before.cache (bytes first suffix) = none) :
    Pr{let result ← (simulateQ (RegistrationNativeRelatedFamily.idealImpl hmac joint dh seed scalar) (checkAt first suffix)).run' before}[result = false] =
      (Fintype.card HmacBlock : ℝ≥0∞)⁻¹ := by
  rw [ideal_fresh hmac joint dh seed scalar first suffix before matching fresh, prEvent_map]
  simp only [decide_eq_false_iff_not, ne_eq, not_not]
  exact SampleableType.prEvent_uniformSample_eq_singleton (extract hmac (bytes first suffix))

/-- The complete PRK has512 bits; this cardinality is derived from the existing split-block equivalence. -/
theorem prk_card : Fintype.card HmacBlock = 2 ^ 512 := by
  rw [Fintype.card_congr PqxdhSecretInputKdf.blockSplitEquiv, Fintype.card_prod]
  have half : Fintype.card PqxdhSecretInputKdf.RootOutput = 2 ^ 256 :=
    PqxdhProjectionCollisions.projection32Value_card
  rw [half, ← pow_add]

/-- The fresh protected test's false-negative probability is exactly2^-512. -/
theorem ideal_fresh_false512 (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (first suffix : DhOutput) (before : State)
    (matching : joint.staticDh seed (dh.publicKey scalar) = some first)
    (fresh : before.cache (bytes first suffix) = none) :
    Pr{let result ← (simulateQ (RegistrationNativeRelatedFamily.idealImpl hmac joint dh seed scalar) (checkAt first suffix)).run' before}[result = false] =
      (2 ^ 512 : ℝ≥0∞)⁻¹ := by
  rw [ideal_fresh_false hmac joint dh seed scalar first suffix before matching fresh, prk_card]
  norm_cast

/-- The test's newly sampled final word is retained literally in the known192-byte input. -/
theorem bytes_suffix (first suffix : DhOutput) : PqxdhJointGapDh.readDh 160 (bytes first suffix) = some suffix :=
  RegistrationNativeRootAliases.read_kem (RegistrationNativeRelatedFamily.address (message first suffix)) first zero

attribute [local irreducible] bytes message

/-- The fresh verification suffix collides with a fixed earlier native-address list with at most its exact32-byte entropy union bound. -/
theorem earlier_collisions (first : DhOutput) (earlier : List Pqxdh.Bytes) :
    Pr{let suffix ← $ᵗ DhOutput}[bytes first suffix ∈ earlier] ≤
      earlier.length * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  have suffix : ∀ secret actual, some (bytes first secret) = some actual → PqxdhJointGapDh.readDh 160 actual = some secret := by
    intro secret actual equal
    cases Option.some.inj equal
    exact bytes_suffix first secret
  have bounded := RegistrationNativeRootAliases.earlier_collisions (fun secret => some (bytes first secret)) suffix earlier
  exact (prEvent_mono ($ᵗ DhOutput) (fun secret => bytes first secret ∈ earlier)
    (fun secret => ∃ actual ∈ earlier, some (bytes first secret) = some actual)
    (fun secret found => ⟨bytes first secret, found, rfl⟩)).trans bounded

end BeaconcryptCore.Computational.RegistrationNativeKnownInputCheck

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputCheck.input_known' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputCheck.input_known
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputCheck.real_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputCheck.real_false
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputCheck.protected_input' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputCheck.protected_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputCheck.ideal_fresh' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputCheck.ideal_fresh
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputCheck.ideal_fresh_false' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputCheck.ideal_fresh_false
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputCheck.prk_card' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputCheck.prk_card
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputCheck.ideal_fresh_false512' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputCheck.ideal_fresh_false512
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputCheck.bytes_suffix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputCheck.bytes_suffix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputCheck.earlier_collisions' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputCheck.earlier_collisions
