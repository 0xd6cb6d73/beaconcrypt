-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhJointDhExtractFamily
import BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix

/-! Literal native root aliases necessarily agree on the actual final32-byte KEM secret. A newly sampled uniform KEM secret can hit only a finite set of root addresses fixed before that draw, with the byte-entropy union bound proved below. These are local sequential-step facts: they never bound arbitrary later adaptive inputs, and do not replace the native generated-owner/response-origin obligations needed to classify repeated-role aliases. -/
open OracleComp OracleSpec CoreModels ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeRootAliases
open PqxdhJointDhExtractFamily (Message)
open PqxdhJointGapDh (TupleAddress DhInterface ScalarBytes assemble readDh)
open PqxdhJointIdentity (Primitives IdentitySeed DhOutput)
open PqxdhKemIndCca (MlKemSharedSecret)
variable {Context : Type}

/-- The actual full192-byte root layout retains its literal final KEM word. -/
theorem read_kem (address : TupleAddress) (first third : DhOutput) :
    readDh 160 (assemble address first third) = some address.kem := by
  simp [readDh, assemble, List.append_assoc, List.drop_append]
  apply congrArg some
  apply List.Vector.toList_injective
  exact List.take_of_length_le (by simp)

/-- This projection uses actual realized bytes, so it requires no DH, encoding or public-key injectivity. -/
theorem input_kem (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) (message : Message) (bytes : Pqxdh.Bytes)
    (realized : PqxdhJointDhExtractFamily.input joint dh seed scalar message = some bytes) :
    readDh 160 bytes = some message.kem := by
  obtain ⟨first, third, firstRun, thirdRun, equal⟩ :=
    (PqxdhJointDhExtractFamily.input_some_iff joint dh seed scalar message bytes).mp realized
  rw [← equal, read_kem]
  rfl

/-- Any complete root alias, even across unrelated DH encodings, has the same KEM secret suffix. -/
theorem alias_kem (joint : Primitives) (dh : DhInterface joint) (leftSeed rightSeed : IdentitySeed)
    (leftScalar rightScalar : ScalarBytes) (left right : Message) (bytes : Pqxdh.Bytes)
    (leftRun : PqxdhJointDhExtractFamily.input joint dh leftSeed leftScalar left = some bytes)
    (rightRun : PqxdhJointDhExtractFamily.input joint dh rightSeed rightScalar right = some bytes) :
    left.kem = right.kem :=
  Option.some.inj ((input_kem joint dh leftSeed leftScalar left bytes leftRun).symm.trans
    (input_kem joint dh rightSeed rightScalar right bytes rightRun))

private theorem uniform_point (secret : MlKemSharedSecret) :
    Pr{let sampled ← $ᵗ MlKemSharedSecret}[sampled = secret] = (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  rw [SampleableType.prEvent_uniformSample_eq_singleton, PqxdhExtractRomHiddenSuffix.secret_card]
  norm_num

/-- A fixed earlier address can equal at most one fresh-secret input, even when the other new input fields depend on that secret. -/
theorem point_collision (input : MlKemSharedSecret → Option Pqxdh.Bytes)
    (suffix : ∀ secret bytes, input secret = some bytes → readDh 160 bytes = some secret)
    (earlier : Pqxdh.Bytes) :
    Pr{let secret ← $ᵗ MlKemSharedSecret}[input secret = some earlier] ≤ (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  classical
  by_cases existsSecret : ∃ secret, input secret = some earlier
  · obtain ⟨candidate, candidateRun⟩ := existsSecret
    refine (prEvent_mono _ _ _ (fun secret reached => ?_)).trans (uniform_point candidate).le
    exact Option.some.inj ((suffix secret earlier reached).symm.trans (suffix candidate earlier candidateRun))
  · have impossible : ∀ secret, input secret ≠ some earlier := by simpa only [not_exists] using existsSecret
    rw [prEvent_eq_zero_of_forall_not _ _ impossible]
    exact zero_le

/-- The earlier root list is fixed before this uniform draw. Duplicates only make this conservative length bound larger. -/
theorem earlier_collisions (input : MlKemSharedSecret → Option Pqxdh.Bytes)
    (suffix : ∀ secret bytes, input secret = some bytes → readDh 160 bytes = some secret)
    (earlier : List Pqxdh.Bytes) :
    Pr{let secret ← $ᵗ MlKemSharedSecret}[∃ bytes ∈ earlier, input secret = some bytes] ≤
      earlier.length * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  classical
  have union := prEvent_exists_finset_le earlier.toFinset ($ᵗ MlKemSharedSecret)
    (fun bytes secret => input secret = some bytes)
  simp only [List.mem_toFinset] at union
  refine union.trans ?_
  calc ∑ bytes ∈ earlier.toFinset, Pr{let secret ← $ᵗ MlKemSharedSecret}[input secret = some bytes]
      ≤ ∑ _bytes ∈ earlier.toFinset, (256 ^ 32 : ℝ≥0∞)⁻¹ :=
        Finset.sum_le_sum fun bytes _ => point_collision input suffix bytes
    _ = earlier.toFinset.card * (256 ^ 32 : ℝ≥0∞)⁻¹ := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ earlier.length * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
      gcongr
      exact_mod_cast List.toFinset_card_le earlier

/-- A genuine pre-draw context may contain arbitrary prior effects and private addresses. The bound is applied after sampling that context and before sampling the new secret. -/
theorem prefix_collision (before : ProbComp Context) (earlier : Context → List Pqxdh.Bytes)
    (input : Context → MlKemSharedSecret → Option Pqxdh.Bytes)
    (suffix : ∀ context secret bytes, input context secret = some bytes → readDh 160 bytes = some secret)
    (cap : Nat) (bounded : ∀ context ∈ support before, (earlier context).length ≤ cap) :
    𝒟[(do
      let context ← before
      let secret ← $ᵗ MlKemSharedSecret
      pure (decide (∃ bytes ∈ earlier context, input context secret = some bytes)))] {true} ≤
      cap * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  classical
  rw [← prEvent_eq_evalDist_singleton _ true]
  apply prEvent_bind_le_of_forall_le_of_support
  intro context reached
  rw [bind_pure_comp, prEvent_map]
  simp only [decide_eq_true_eq]
  refine (earlier_collisions (input context) (suffix context) (earlier context)).trans ?_
  gcongr
  exact_mod_cast bounded context reached

end BeaconcryptCore.Computational.RegistrationNativeRootAliases

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRootAliases.read_kem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRootAliases.read_kem
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRootAliases.input_kem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRootAliases.input_kem
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRootAliases.alias_kem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRootAliases.alias_kem
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRootAliases.point_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRootAliases.point_collision
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRootAliases.earlier_collisions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRootAliases.earlier_collisions
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRootAliases.prefix_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRootAliases.prefix_collision
