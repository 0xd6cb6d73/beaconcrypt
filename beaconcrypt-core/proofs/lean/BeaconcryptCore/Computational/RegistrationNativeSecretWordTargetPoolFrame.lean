-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhaseCore

/-! Private key-list preservation uses the actual early provider and all ordinary source effects. It neither identifies the symbolic provider with a fixed real KEM source nor assumes owner/index alignment. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPoolFrame
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterface (Spec)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def IsCreate : (Spec n KemSK).Domain → Prop
  | .inl (.inr (.inr (.inr (.inl .create)))) => True
  | _ => False
instance : DecidablePred (IsCreate (n := n) (KemSK := KemSK)) := fun query => by
  unfold IsCreate
  split <;> infer_instance

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n)
  setup wire route sign input inside provider outer

/-- Every actual callback except indexed birth retains the full current private key list. -/
theorem query_keys (query : (Spec n KemSK).Domain) (quiet : ¬IsCreate (KemSK := KemSK) query)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (result : (Spec n KemSK).Range query × RegistrationNativeSecretWordInterpreter.State n KemSK)
    (supported : result ∈ support ((implementation query).run before)) : result.2.kem.1.keys = before.kem.1.keys := by
  have native : result ∈ support
      ((RegistrationNativeSecretWordInterpreter.handler setup wire route sign input inside provider query).run before) := by
    apply PqxdhDeploymentEnvironment.support_simulateQ_subset outer _
    exact supported
  rcases query with (message | (message | common) | routed) | record
  · simp only [RegistrationNativeSecretWordInterpreter.handler, RegistrationNativeSecretWordInterpreter.roots,
      StateT.run, support_map] at native
    obtain ⟨answer, _, equal⟩ := native
    cases equal
    rfl
  · simp only [RegistrationNativeSecretWordInterpreter.handler, RegistrationNativeSecretWordInterpreter.roots,
      StateT.run, support_map] at native
    obtain ⟨answer, _, equal⟩ := native
    cases equal
    rfl
  · simp only [RegistrationNativeSecretWordInterpreter.handler, RegistrationNativeSecretWordInterpreter.ordinary,
      StateT.run, support_map] at native
    obtain ⟨answer, _, equal⟩ := native
    cases equal
    rfl
  · rw [RegistrationNativeSecretWordInterpreter.kem_run, support_map] at native
    obtain ⟨answer, reached, equal⟩ := native
    have actual := PqxdhDeploymentEnvironment.support_simulateQ_subset RegistrationNativeSecretWordService.coins _ reached
    have ordinary : ¬RegistrationNativeSecretWordKemEarlyKeys.Creates (KemSK := KemSK) routed := by
      rcases routed with (other | key) | pool | key
      · trivial
      · trivial
      · cases pool <;> first | exact quiet | trivial
      · trivial
    cases equal
    exact RegistrationNativeSecretWordKemEarlyKeys.noncreate_keys setup.baseImpl setup.kem selected pairs publicKey challenge
      routed ordinary before.kem answer actual
  · simp only [RegistrationNativeSecretWordInterpreter.handler, RegistrationNativeSecretWordInterpreter.ordinary,
      StateT.run, support_map] at native
    obtain ⟨answer, _, equal⟩ := native
    cases equal
    rfl

/-- Any actual source continuation with zero private births retains the full current private key list. -/
theorem program_keys (work : OracleComp (Spec n KemSK) Value)
    (bounded : work.IsQueryBoundP (IsCreate (KemSK := KemSK)) 0)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (result : Value × RegistrationNativeSecretWordInterpreter.State n KemSK)
    (supported : result ∈ support ((simulateQ implementation work).run before)) : result.2.kem.1.keys = before.kem.1.keys := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨first, later⟩ := bounded
      have quiet := first.resolve_right (by omega)
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, called, continued⟩ := supported
      exact (ih middle.1 (by simpa using later middle.1) middle.2 result continued).trans
        (query_keys setup wire route sign input inside selected pairs publicKey challenge outer query quiet before middle called)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPoolFrame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPoolFrame.query_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPoolFrame.query_keys
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPoolFrame.program_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPoolFrame.program_keys
