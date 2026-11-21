-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKeyHybrid

/-! This is an additional ordinary primitive experiment for the native profile. Its uniformly secret32-byte key occupies the final32 bytes of the literal192-byte root input; an adversary chooses each160-byte head adaptively and receives the complete actual108-byte key schedule. The ideal oracle returns persistent uniform108-byte values. Public source evaluation on guessed keys remains available to adversary code. Small advantage here is an explicit extra assumption: it is not implied by ordinary secret-key HMAC PRF security or by secrecy of the selected DH input. In particular it covers candidate-dependent off-protected wrong-pin side sessions. No claim of small advantage or whole-frontend reduction is made by defining this game. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSuffixKeyPrf
open PqxdhServerAuthKeySchedule (Output)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open PqxdhSecretInputKdf (HmacSha512 extract)

abbrev Prefix := List.Vector UInt8 160
abbrev Secret := List.Vector UInt8 32
abbrev Oracle := Prefix →ₒ Output
abbrev Spec := unifSpec + Oracle

def input (head : Prefix) (key : Secret) : Pqxdh.Bytes := head.toList ++ key.toList

def value (source : FixedHkdfSha512NoSaltSource) (key : Secret) (head : Prefix) : Output :=
  PqxdhServerAuthKeySchedule.fromRoot source (RegistrationNativeRelatedRoot.nativeRoot source (input head key))

def realImpl (source : FixedHkdfSha512NoSaltSource) (key : Secret) : QueryImpl Spec ProbComp
  | .inl coin => unifSpec.query coin
  | .inr head => pure (value source key head)

noncomputable def idealImpl : QueryImpl Spec (StateT Oracle.QueryCache ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT Oracle.QueryCache ProbComp) + Oracle.randomOracle

noncomputable def real (source : FixedHkdfSha512NoSaltSource) (adversary : OracleComp Spec Bool) : ProbComp Bool := do
  let key ← $ᵗ Secret
  simulateQ (realImpl source key) adversary

noncomputable def ideal (adversary : OracleComp Spec Bool) : ProbComp Bool :=
  (simulateQ idealImpl adversary).run' ∅

noncomputable def advantage (source : FixedHkdfSha512NoSaltSource) (adversary : OracleComp Spec Bool) : ℝ :=
  (real source adversary).boolDistance (ideal adversary)

/-- Every oracle input has the actual native root-input width; invalid-length inputs are outside this primitive interface. -/
theorem input_length (head : Prefix) (key : Secret) : (input head key).length = 192 := by
  simp [input]

/-- The entire real108-byte answer contains root Expand followed by the actual initial and ongoing source schedules. -/
theorem value_extract (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect source hmac) (key : Secret) (head : Prefix) :
    value source key head = PqxdhServerAuthKeySchedule.keySchedule source hmac (extract hmac (input head key)) := by
  exact (PqxdhServerAuthKeySchedule.keySchedule_extract correct (input head key)).symm

/-- Real oracle evaluation is the same public source function on every adaptive head, with its secret key owned only by the primitive game. -/
theorem real_query (source : FixedHkdfSha512NoSaltSource) (key : Secret) (head : Prefix) :
    realImpl source key (.inr head) = pure (value source key head) := rfl

/-- The added primitive term is literally the distance between these two explicit ordinary experiments, without a negligible-advantage premise. -/
theorem distance_eq (source : FixedHkdfSha512NoSaltSource) (adversary : OracleComp Spec Bool) :
    (real source adversary).boolDistance (ideal adversary) = advantage source adversary := rfl

end BeaconcryptCore.Computational.RegistrationNativeSuffixKeyPrf
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyPrf.input_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyPrf.input_length
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyPrf.value_extract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyPrf.value_extract
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyPrf.real_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyPrf.real_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyPrf.distance_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyPrf.distance_eq
