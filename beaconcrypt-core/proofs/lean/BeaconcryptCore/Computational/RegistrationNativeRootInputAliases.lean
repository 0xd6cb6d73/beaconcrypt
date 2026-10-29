-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRootAliases
import BeaconcryptCore.Computational.RegistrationNativeRelatedFamily

/-! Full native input aliases, including arbitrary pinned Server identities and ordinary supplied DH coordinates, retain the exact KEM suffix. The sequential fresh-secret collision bound applies without any DH or encoding injectivity premise. -/
open OracleComp OracleSpec CoreModels ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeRootInputAliases
open PqxdhJointIdentity (Primitives IdentitySeed)
open PqxdhJointGapDh (DhInterface ScalarBytes readDh)
open RegistrationNativeRelatedFamily (Message input)

/-- Every realized full native root input retains its actual final KEM word. -/
theorem input_kem (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) (message : Message) (bytes : Pqxdh.Bytes)
    (realized : input joint dh seed scalar message = some bytes) :
    readDh 160 bytes = some message.kem := by
  obtain ⟨first, third, _firstRun, _thirdRun, equal⟩ :=
    (RegistrationNativeRelatedFamily.input_some_iff joint dh seed scalar message bytes).mp realized
  rw [← equal, RegistrationNativeRootAliases.read_kem]
  rfl

/-- Literal native root aliases necessarily agree on their complete KEM shared secret. -/
theorem alias_kem (joint : Primitives) (dh : DhInterface joint) (leftSeed rightSeed : IdentitySeed)
    (leftScalar rightScalar : ScalarBytes) (left right : Message) (bytes : Pqxdh.Bytes)
    (leftRun : input joint dh leftSeed leftScalar left = some bytes)
    (rightRun : input joint dh rightSeed rightScalar right = some bytes) : left.kem = right.kem :=
  Option.some.inj ((input_kem joint dh leftSeed leftScalar left bytes leftRun).symm.trans
    (input_kem joint dh rightSeed rightScalar right bytes rightRun))

/-- A newly sampled native KEM suffix hits an earlier fixed native-address set with at most its length times the exact 32-byte entropy term. -/
theorem earlier_collisions (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) (message : PqxdhKemIndCca.MlKemSharedSecret → Message)
    (suffix : ∀ secret, (message secret).kem = secret) (earlier : List Pqxdh.Bytes) :
    Pr{let secret ← $ᵗ PqxdhKemIndCca.MlKemSharedSecret}[
      ∃ bytes ∈ earlier, input joint dh seed scalar (message secret) = some bytes] ≤
      earlier.length * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  apply RegistrationNativeRootAliases.earlier_collisions
  intro secret bytes realized
  rw [input_kem joint dh seed scalar (message secret) bytes realized, suffix secret]

end BeaconcryptCore.Computational.RegistrationNativeRootInputAliases
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRootInputAliases.input_kem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRootInputAliases.input_kem
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRootInputAliases.alias_kem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRootInputAliases.alias_kem
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRootInputAliases.earlier_collisions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRootInputAliases.earlier_collisions
