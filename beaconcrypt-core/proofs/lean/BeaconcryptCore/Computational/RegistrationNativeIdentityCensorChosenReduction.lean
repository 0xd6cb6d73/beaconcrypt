-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityChosenPublicRouter
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCensorRecognition

/-! The chosen ordinary joint-Ed adversary samples all independent other identities internally. Its constructor receives the challenged public identity, public ordinal choices and executable client only; the challenged seed remains in the ordinary oracle interpreter. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorChosenReduction
open PqxdhJointIdentity (Primitives PublicIdentity IdentitySeed Forgery AdversarySpec)
open PqxdhJointIdentityFamily (sampleFamily)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityTemplateCensorRecognition (Spec Cache)
open RegistrationNativeIdentityAdaptiveHashCapture (Candidate)
variable {count : Nat}

abbrev Client (joint : Primitives) (count : Nat) :=
  (Fin count → IdentitySeed) → (identity : PublicIdentity) → OracleComp Spec (Option (Candidate joint identity))

private def mix {A : Type} (sampler : ProbComp A)
    (next : A → PublicIdentity → OracleComp AdversarySpec Forgery) (identity : PublicIdentity) : OracleComp AdversarySpec Forgery := do
  let value ← OracleComp.liftComp sampler AdversarySpec
  next value identity

private theorem mix_advantage {A : Type} (joint : Primitives) (sampler : ProbComp A)
    (next : A → PublicIdentity → OracleComp AdversarySpec Forgery) :
    Pr{let accepted ← (do let value ← sampler; PqxdhJointIdentity.game joint (next value))}[accepted = true] =
      PqxdhJointIdentity.advantage joint (mix sampler next) := by
  unfold PqxdhJointIdentity.advantage PqxdhJointIdentity.game PqxdhJointIdentity.run mix
  simp only [simulateQ_bind, StateT.run_bind, PqxdhJointIdentityFamily.simulate_joint_uniform, bind_map_left, bind_assoc]
  exact (PqxdhSecretInputKdf.evalSPMF_sample_comm sampler PqxdhJointIdentity.sampleSeed _).prEvent_eq (· = true)

/-- Independent startup is sampled inside the actual ordinary adversary, including all constructor and auxiliary-key failures. -/
def sampled {A : Type} (sampler : ProbComp A)
    (next : A → PublicIdentity → OracleComp AdversarySpec Forgery)
    (identity : PublicIdentity) : OracleComp AdversarySpec Forgery := mix sampler next identity

/-- Averaging an independent actual startup is exactly the ordinary advantage of its internally sampled executable adversary. -/
theorem sampled_advantage {A : Type} (joint : Primitives) (sampler : ProbComp A)
    (next : A → PublicIdentity → OracleComp AdversarySpec Forgery) :
    Pr{let accepted ← (do let value ← sampler; PqxdhJointIdentity.game joint (next value))}[accepted = true] =
      PqxdhJointIdentity.advantage joint (sampled sampler next) :=
  mix_advantage joint sampler next

/-- Independent key generation is part of E's actual execution; the challenged seed is not captured. -/
noncomputable def reduction (joint : Primitives) (target : Fin (count+1)) (placeholder : Ed25519Signature)
    (fallback : Forgery) (client : Client joint count) (cache : Cache)
    (before : RegistrationNativeIdentityChosenPublicRouter.Auxiliary count) (identity : PublicIdentity) :
    OracleComp AdversarySpec Forgery :=
  mix (sampleFamily count) (fun others => RegistrationNativeIdentityAdaptiveCensor.reduction placeholder fallback
    (RegistrationNativeIdentityTemplateCensorRecognition.work joint
      (RegistrationNativeIdentityChosenPublicRouter.protocol joint target others) (client others) cache before)) identity

noncomputable def observed (joint : Primitives) (target : Fin (count+1)) (placeholder : Ed25519Signature)
    (client : Client joint count) (cache : Cache) (before : RegistrationNativeIdentityChosenPublicRouter.Auxiliary count) : ProbComp Bool := do
  let others ← sampleFamily count
  RegistrationNativeIdentityTemplateCensorRecognition.game joint placeholder
    (RegistrationNativeIdentityChosenPublicRouter.protocol joint target others) (client others) cache before

private theorem advantage_average (joint : Primitives) (target : Fin (count+1)) (placeholder : Ed25519Signature)
    (fallback : Forgery) (client : Client joint count) (cache : Cache)
    (before : RegistrationNativeIdentityChosenPublicRouter.Auxiliary count) :
    Pr{let accepted ← (do
      let others ← sampleFamily count
      PqxdhJointIdentity.game joint (RegistrationNativeIdentityAdaptiveCensor.reduction placeholder fallback
        (RegistrationNativeIdentityTemplateCensorRecognition.work joint
          (RegistrationNativeIdentityChosenPublicRouter.protocol joint target others) (client others) cache before)))}[accepted = true] =
      PqxdhJointIdentity.advantage joint (reduction joint target placeholder fallback client cache before) :=
  mix_advantage joint (sampleFamily count) _

/-- Averaging independent other-key generation leaves one explicit ordinary joint weak-EUF advantage for this fixed public target/ordinal client. No original causal-event inclusion is a premise. -/
theorem bound (joint : Primitives) (target : Fin (count+1)) (placeholder : Ed25519Signature)
    (fallback : Forgery) (client : Client joint count) (cache : Cache)
    (before : RegistrationNativeIdentityChosenPublicRouter.Auxiliary count) :
    Pr{let accepted ← observed joint target placeholder client cache before}[accepted = true] ≤
      PqxdhJointIdentity.advantage joint (reduction joint target placeholder fallback client cache before) := by
  rw [← advantage_average]
  unfold observed
  apply prEvent_bind_mono_of_forall_le
  intro others
  exact RegistrationNativeIdentityTemplateCensorRecognition.bound joint placeholder fallback
    (RegistrationNativeIdentityChosenPublicRouter.protocol joint target others) (client others) cache before

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorChosenReduction

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorChosenReduction.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorChosenReduction.bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorChosenReduction.sampled_advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorChosenReduction.sampled_advantage
