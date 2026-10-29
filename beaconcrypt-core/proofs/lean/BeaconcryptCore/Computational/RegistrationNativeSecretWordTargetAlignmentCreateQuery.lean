-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPoolFrame
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateLocal
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyBirth

/-! Actual native birth callbacks are lowered through the symbolic local interface without changing their creation reply. The early private provider supplies the same appended pair, and every callback outside private birth retains the current key list. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateQuery
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterface (Spec)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def compiler : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (OracleComp (Spec n KemSK)) :=
  RegistrationNativeSecretWordInterface.liftLocal false ∘ₛ
    (RegistrationNativeSecretWordServerSource.realize RegistrationNativeSecretWordMessage.zero ∘ₛ
      RegistrationBeaconReferenceCompiler.trustedLift)

private theorem compiler_bound (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (bounded : work.IsQueryBoundP (RegistrationNativeKemBeaconFootprint.counted (n := n) (KemSK := KemSK) .create) 0) :
    (simulateQ compiler work).IsQueryBoundP (RegistrationNativeSecretWordTargetPoolFrame.IsCreate (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work 0 bounded
  intro query
  rcases query with effect | other | pool | key
  all_goals try cases pool
  all_goals simp [compiler, QueryImpl.compose, RegistrationBeaconReferenceCompiler.trustedLift,
    RegistrationBeaconReferenceCompiler.effect, RegistrationBeaconReferenceCompiler.indexed,
    RegistrationNativeSecretWordServerSource.realize,
    RegistrationNativeSecretWordInterface.common, RegistrationNativeSecretWordInterface.localKem,
    RegistrationNativeSecretWordInterface.liftLocal, RegistrationNativeSecretWordInterface.route,
    RegistrationNativeSecretWordInterface.routedKem, RegistrationNativeSecretWordTargetPoolFrame.IsCreate,
    RegistrationNativeKemBeaconFootprint.counted,
    isQueryBoundP_query_iff, isQueryBoundP_map_iff]

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n)
  setup wire route sign input inside provider outer

noncomputable def trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK)
    (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp) := implementation ∘ₛ compiler

/-- A complete native callback program with zero private births retains its current private key list under the actual early provider. -/
theorem program_keys (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (bounded : work.IsQueryBoundP (RegistrationNativeKemBeaconFootprint.counted (n := n) (KemSK := KemSK) .create) 0)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (result : Value × RegistrationNativeSecretWordInterpreter.State n KemSK)
    (supported : result ∈ support ((simulateQ (trusted setup wire route sign input inside selected pairs publicKey challenge outer) work).run before)) :
    result.2.kem.1.keys = before.kem.1.keys := by
  simp only [trusted, QueryImpl.simulateQ_compose] at supported
  exact RegistrationNativeSecretWordTargetPoolFrame.program_keys setup wire route sign input inside
    selected pairs publicKey challenge outer _ (compiler_bound work bounded) before result supported

/-- The actual private birth returns its old indexed length and the same genuinely appended public pair, even beyond the reservation prefix. -/
theorem create_step (before : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (result : (Nat × MlKem768PublicKey) × RegistrationNativeSecretWordInterpreter.State n KemSK)
    (supported : result ∈ support
      (((trusted setup wire route sign input inside selected pairs publicKey challenge outer)
        (.inr (.inr (.inl .create)))).run before)) :
    ∃ pair, result.1 = (before.kem.1.keys.length, pair.1) ∧ result.2.kem.1.keys = before.kem.1.keys ++ [pair] := by
  have compiled : compiler (n := n) (KemSK := KemSK) (.inr (.inr (.inl .create))) =
      (Spec n KemSK).query (.inl (.inr (.inr (.inr (.inl .create))))) := by
    simp only [compiler, QueryImpl.compose, RegistrationBeaconReferenceCompiler.trustedLift,
      RegistrationBeaconReferenceCompiler.indexed, simulateQ_spec_query,
      RegistrationNativeSecretWordServerSource.realize, RegistrationNativeSecretWordInterface.localKem,
      RegistrationNativeSecretWordInterface.liftLocal, RegistrationNativeSecretWordInterface.route,
      RegistrationNativeSecretWordInterface.routedKem]
  simp only [trusted, QueryImpl.compose, compiled, simulateQ_spec_query] at supported
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset outer _ supported
  rw [RegistrationNativeSecretWordInterpreter.kem_run, support_map] at native
  obtain ⟨answer, reached, equal⟩ := native
  have actual := PqxdhDeploymentEnvironment.support_simulateQ_subset RegistrationNativeSecretWordService.coins _ reached
  obtain ⟨pair, replied, appended, _marker⟩ := RegistrationNativeSecretWordKemEarlyBirth.create_step
    setup.baseImpl setup.kem selected pairs publicKey challenge before.kem answer actual
  cases equal
  exact ⟨pair, replied, appended⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateQuery
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateQuery.program_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateQuery.program_keys
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateQuery.create_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateQuery.create_step
