-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerEffects
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhaseCore

/-! Actual Server environment/hash programs preserve the early getter marker. The concrete selected local source still routes its real KEM getter, while ordinary World effects and local request-log updates cannot spend that getter. Every reached current environment and private World/cache remains literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerPhase
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterface (LocalSpec Spec effect liftLocal)
open RegistrationNativeSecretWordTargetServerExecution (Auxiliary lower localImpl)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativeSecretWordTargetPhaseCore (Selected)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- No actual environment-effect AST contains a selected KEM getter, even when its surrounding local routing is selected. -/
theorem effect_free (selected : Bool) (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    (simulateQ (liftLocal (KemSK := KemSK) selected) (simulateQ effect work)).IsQueryBoundP
      (Selected (KemSK := KemSK)) 0 := by
  rw [← QueryImpl.simulateQ_compose]
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ work 0 (isQueryBoundP_false _ 0)
  intro query
  simp [QueryImpl.compose, effect, liftLocal, Selected, isQueryBoundP_query_iff]

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "implementation" => localImpl (n := n) setup wire route sign input inside provider outer true

/-- Querywise current-environment lowering retains the actual marker for a locally quiet controller. -/
theorem lower_phase (work : StateT Environment (OracleComp (LocalSpec n KemSK)) Value)
    (before : Auxiliary n KemSK) (result : Value × Auxiliary n KemSK)
    (quiet : (simulateQ (liftLocal true) (work.run before.1)).IsQueryBoundP (Selected (KemSK := KemSK)) 0)
    (supported : result ∈ support ((lower implementation work).run before)) :
    result.2.2.kem.2 = before.2.kem.2 := by
  rw [RegistrationNativeSecretWordTargetServerExecution.lower_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  have actual : reached ∈ support
      ((simulateQ (RegistrationNativeSecretWordTargetSource.implementation setup wire route sign input inside provider outer)
        (simulateQ (liftLocal true) (work.run before.1))).run before.2) := by
    simpa only [localImpl, QueryImpl.simulateQ_compose] using called
  have kept := RegistrationNativeSecretWordTargetPhaseCore.program_phase setup wire route sign input inside
    selected pairs publicKey challenge outer _ quiet before.2 reached actual
  cases equal
  exact kept

/-- The actual authentication/hash source cannot change the getter marker on any result. -/
theorem effect_phase (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value)
    (before : Auxiliary n KemSK) (result : Value × Auxiliary n KemSK)
    (supported : result ∈ support ((lower implementation (StateT.lift (simulateQ effect work))).run before)) :
    result.2.2.kem.2 = before.2.kem.2 := by
  apply lower_phase setup wire route sign input inside selected pairs publicKey challenge outer _ before result _ supported
  simp only [StateT.run_lift, bind_pure_comp, simulateQ_map, isQueryBoundP_map_iff]
  exact effect_free true work

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerPhase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerPhase.effect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerPhase.effect_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerPhase.lower_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerPhase.lower_phase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerPhase.effect_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerPhase.effect_phase
