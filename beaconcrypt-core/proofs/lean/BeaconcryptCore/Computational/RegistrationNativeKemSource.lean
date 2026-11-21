-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemGame

/-! The native cut's executable CCA routing equals the actual indexed stopped source after interpreting only the selected secret's ordinary oracle. The real postchallenge comparison changes only the selected exact-ciphertext reply, whose agreement is an explicit KEM correctness fact. Complete auxiliary state and private generated-key histories are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemSource
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemGame (State combine pre post stopped)
open PqxdhKemIndCca
open PqxdhPrivateKemSource (evalKem evalKem_coins evalKem_ambient)
open PqxdhDynamicKemPost (evaluate)
variable {κ ι KemSK Auxiliary Result : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

/-- Every native request keeps its complete auxiliary and generated-owner state in the executable prechallenge/source comparison. -/
theorem pre_step (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (key : MlKem768PublicKey) (secret : KemSK)
    (member : pairs[selected]? = some (key, secret)) (query : (Spec ambient KemSK).Domain)
    (before : State Auxiliary KemSK) :
    evalKem baseImpl kem secret
      (((pre kem other selected (PqxdhDynamicKemRouter.redact selected pairs) query).run).run before) =
    (((stopped baseImpl kem other selected pairs query).run).run before) := by
  rcases query with query | (query | publicKey)
  · simp only [pre, stopped, combine, OptionT.run_mk, StateT.run, evalKem, simulateQ_map]
    exact congrArg (Functor.map (fun result => (some result.1, (result.2, before.2))))
      (evalKem_coins baseImpl kem secret ((other query).run before.1))
  · simp only [pre, stopped, combine, OptionT.run_mk, StateT.run, evalKem, simulateQ_map]
    exact congrArg (Functor.map (fun result => (result.1, (before.1, result.2))))
      (PqxdhDynamicKemRouter.step_source baseImpl kem selected pairs key secret member query before.2)
  · simp only [pre, stopped, combine, OptionT.run_mk, StateT.run, evalKem, simulateQ_map]
    exact congrArg (Functor.map (fun result => (some result, before)))
      (evalKem_ambient baseImpl kem secret (kem.encaps publicKey))

/-- Arbitrary adaptive actual native programs retain the full state under the ordinary selected-decapsulation prechallenge interpretation. -/
theorem pre_program (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (key : MlKem768PublicKey) (secret : KemSK)
    (member : pairs[selected]? = some (key, secret))
    (work : OracleComp (Spec ambient KemSK) Result) (before : State Auxiliary KemSK) :
    evalKem baseImpl kem secret
      (((simulateQ (pre kem other selected (PqxdhDynamicKemRouter.redact selected pairs)) work).run).run before) =
    (((simulateQ (stopped baseImpl kem other selected pairs) work).run).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
    unfold evalKem
    simp only [simulateQ_bind]
    rw [show simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
      (simulateQ (PqxdhStatefulPhase1EufCma.localKemPreChallengeImpl kem secret)
        (((pre kem other selected (PqxdhDynamicKemRouter.redact selected pairs) query).run).run before)) =
        (((stopped baseImpl kem other selected pairs query).run).run before) from
          pre_step baseImpl kem other selected pairs key secret member query before]
    apply bind_congr
    rintro ⟨none | answer, after⟩
    · rfl
    · exact ih answer after

/-- On real-candidate correctness, all native postchallenge callbacks are exactly their actual source operations; other-index aliases keep their own secret. -/
theorem post_step (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (key : MlKem768PublicKey) (secret : KemSK)
    (member : pairs[selected]? = some (key, secret)) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some candidate))
    (query : (Spec ambient KemSK).Domain) (before : State Auxiliary KemSK) :
    evaluate baseImpl kem secret challenge
      (((post kem other selected (PqxdhDynamicKemRouter.redact selected pairs) challenge candidate query).run).run before) =
    (((stopped baseImpl kem other selected pairs query).run).run before) := by
  rcases query with query | (query | publicKey)
  · simp only [post, stopped, combine, OptionT.run_mk, StateT.run, evaluate, simulateQ_map]
    exact congrArg (Functor.map (fun result => (some result.1, (result.2, before.2))))
      (PqxdhDynamicKemJointRouter.post_coins baseImpl kem secret challenge ((other query).run before.1))
  · simp only [post, stopped, combine, OptionT.run_mk, StateT.run, evaluate, simulateQ_map]
    have same := (PqxdhDynamicKemPost.step_pre baseImpl kem secret selected challenge candidate agreement
      (PqxdhDynamicKemRouter.redact selected pairs) query before.2).trans
        (PqxdhDynamicKemRouter.step_source baseImpl kem selected pairs key secret member query before.2)
    exact congrArg (Functor.map (fun result => (result.1, (before.1, result.2)))) same
  · simp only [post, stopped, combine, OptionT.run_mk, StateT.run, evaluate, simulateQ_map]
    exact congrArg (Functor.map (fun result => (some result, before)))
      (PqxdhDynamicKemPost.ambient baseImpl kem secret challenge (kem.encaps publicKey))

/-- Complete arbitrary native postchallenge work preserves actual optional failures, selected reveal stopping and every auxiliary/private field. -/
theorem post_program (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (key : MlKem768PublicKey) (secret : KemSK)
    (member : pairs[selected]? = some (key, secret)) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some candidate))
    (work : OracleComp (Spec ambient KemSK) Result) (before : State Auxiliary KemSK) :
    evaluate baseImpl kem secret challenge
      (((simulateQ (post kem other selected (PqxdhDynamicKemRouter.redact selected pairs) challenge candidate) work).run).run before) =
    (((simulateQ (stopped baseImpl kem other selected pairs) work).run).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
    unfold evaluate
    simp only [simulateQ_bind]
    rw [show simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
      (simulateQ (kem.IND_CCA_postChallengeImpl secret challenge)
        (((post kem other selected (PqxdhDynamicKemRouter.redact selected pairs) challenge candidate query).run).run before)) =
        (((stopped baseImpl kem other selected pairs query).run).run before) from
          post_step baseImpl kem other selected pairs key secret member challenge candidate agreement query before]
    apply bind_congr
    rintro ⟨none | answer, after⟩
    · rfl
    · exact ih answer after

end BeaconcryptCore.Computational.RegistrationNativeKemSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSource.pre_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSource.pre_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSource.pre_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSource.pre_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSource.post_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSource.post_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSource.post_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSource.post_program
