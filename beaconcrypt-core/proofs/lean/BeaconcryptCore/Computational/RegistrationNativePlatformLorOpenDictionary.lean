-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorWorldDictionary
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenService
/-! The source support dictionary leaves material demand open to the actual stateful service, including hidden, known and failed replies. Preparation keeps its source DH test and genuine prepared-state notification; concrete source equations instantiate both root leaves without a whole-controller assumption. Other source publication, KEM and record leaves retain the dictionary bodies. These are representation/support lemmas, not the complete ideal designation theorem. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorOpenDictionary
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativePlatformLorWorldDictionary (State)
variable {n : Nat} {I KemSK Value : Type} {base : OracleSpec I}
abbrev RootSpec (n : Nat) := (Message →ₒ Unit) + (Message →ₒ Option (RegistrationNativePairedChoice.Choice n))
abbrev Spec (n : Nat) := RegistrationNativePlatformLorWorldDictionary.Spec n + RootSpec n
def embed : QueryImpl (RegistrationNativePlatformLorWorldDictionary.Spec n) (OracleComp (Spec n)) :=
  fun query => (Spec n).query (.inl query)
def root : QueryImpl (RootSpec n) (OracleComp (Spec n)) := fun query => (Spec n).query (.inr query)
abbrev M (n : Nat) (KemSK Value : Type) := StateT (State n KemSK) (OracleComp (Spec n)) Value

noncomputable def handler (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK) :
    QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (M n KemSK)
  | .inl (.inl message) => fun before => do
      let _ ← root (.inl message)
      pure ((input message).map (fun _ => message),
        {before with flags := Function.update before.flags message (input message).isSome})
  | .inl (.inr (.inl (.inl message))) => fun before =>
      (fun reply => (reply,before)) <$> root (.inr message)
  | query => QueryImpl.mapStateTBase embed
      (RegistrationNativePlatformLorWorldDictionary.handler setup wire sign input inside provider) query

theorem prepare_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (message : Message) (before : State n KemSK) :
    (handler setup wire sign input inside provider (.inl (.inl message))).run before = (do
      let _ ← root (.inl message)
      pure ((input message).map (fun _ => message),
        {before with flags := Function.update before.flags message (input message).isSome})) := rfl

theorem demand_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (message : Message) (before : State n KemSK) :
    (handler setup wire sign input inside provider (.inl (.inr (.inl (.inl message))))).run before =
      (fun reply => (reply,before)) <$> root (.inr message) := rfl

theorem prepare_support (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (message : Message) (before : State n KemSK)
    (result : Option Message × State n KemSK)
    (supported : result ∈ support ((handler setup wire sign input inside provider (.inl (.inl message))).run before)) :
    result.1=(input message).map (fun _ => message) ∧ result.2.kem=before.kem := by
  rw [prepare_run,mem_support_bind_iff] at supported
  obtain ⟨reply,_called,returned⟩ := supported
  rw [mem_support_pure_iff] at returned
  cases returned
  exact ⟨rfl,rfl⟩

theorem kem_support (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (query : (RegistrationNativeSecretWordKemInterface.Routed KemSK).Domain) (before : State n KemSK)
    (result : (RegistrationNativeSecretWordKemInterface.Routed KemSK).Range query × State n KemSK)
    (supported : result ∈ support ((handler setup wire sign input inside provider (.inl (.inr (.inr query)))).run before)) :
    (result.1,result.2.kem) ∈ support ((provider query).run before.kem) := by
  simp only [handler,QueryImpl.mapStateTBase,StateT.run_mk] at supported
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset embed _ supported
  rw [RegistrationNativePlatformLorWorldDictionary.kem_run,support_map] at original
  obtain ⟨answer,called,returned⟩ := original
  have actual := PqxdhDeploymentEnvironment.support_simulateQ_subset RegistrationNativePlatformLorWorldDictionary.coins _ called
  cases returned
  exact actual

def NoRouted : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain → Prop
  | .inl (.inr (.inr _)) => False
  | _ => True

theorem nonrouted_kem (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain) (quiet : NoRouted query)
    (before : State n KemSK) (result : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range query × State n KemSK)
    (supported : result ∈ support ((handler setup wire sign input inside provider query).run before)) :
    result.2.kem=before.kem := by
  rcases query with (message | (message | commonQuery) | routedQuery) | recordQuery
  · exact (prepare_support setup wire sign input inside provider message before result supported).2
  · rw [demand_run,support_map] at supported
    obtain ⟨reply,_called,returned⟩ := supported
    cases returned
    rfl
  · simp only [handler,QueryImpl.mapStateTBase,StateT.run_mk] at supported
    have original := PqxdhDeploymentEnvironment.support_simulateQ_subset embed _ supported
    exact (RegistrationNativePlatformLorWorldDictionary.common_frame setup wire sign commonQuery before result original).2
  · exact quiet.elim
  · simp only [handler,QueryImpl.mapStateTBase,StateT.run_mk] at supported
    have original := PqxdhDeploymentEnvironment.support_simulateQ_subset embed _ supported
    rw [RegistrationNativePlatformLorWorldDictionary.record_run,support_map] at original
    obtain ⟨reply,_called,returned⟩ := original
    cases returned
    rfl

noncomputable def actualRoots (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    QueryImpl (RootSpec n)
      (StateT (RegistrationNativeSelectiveHiddenService.State n) (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)))
  | .inl message => (fun _ => ()) <$>
      (QueryImpl.mapStateTBase PqxdhRecordLiftInterface.effectLift
        (fun (query : Message) => RegistrationNativeSelectiveHiddenService.prepare
          (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
          (RegistrationNativeSecretWordMessage.eval candidate query))) message
  | .inr message =>
      (QueryImpl.mapStateTBase PqxdhRecordLiftInterface.effectLift
        (fun (query : Message) => RegistrationNativeSelectiveHiddenService.demand setup.source
          (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
          (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
          candidate (RegistrationNativeSecretWordMessage.eval candidate query))) message

private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (work before >>= fun result => next result.1 result.2) := rfl
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map _ _ _
private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value,before) := rfl

theorem actual_prepare (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : Message)
    (before : RegistrationNativeSelectiveHiddenService.State n) :
    ((actualRoots setup seed scalar candidate (.inl message)) >>= fun _ => pure
      ((RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar message).map
        (fun _ => RegistrationNativeSecretWordMessage.eval candidate message))).run before =
      simulateQ PqxdhRecordLiftInterface.effectLift
        ((RegistrationNativeSelectiveHiddenService.prepare
          (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
          (RegistrationNativeSecretWordMessage.eval candidate message)).run before) := by
  change ((actualRoots setup seed scalar candidate (.inl message)) >>= fun _ => pure
    ((RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar message).map
      (fun _ => RegistrationNativeSecretWordMessage.eval candidate message))) before = _
  simp only [actualRoots,bind_apply,map_apply,QueryImpl.mapStateTBase,StateT.mk,
    RegistrationNativeSelectiveHiddenService.prepare,RegistrationNativeSelectiveHiddenService.onHidden,
    RegistrationNativeHiddenService.prepare,StateT.run,simulateQ_pure,map_pure,pure_bind,pure_apply]
  rw [←RegistrationNativeSecretWordMessage.input_eval setup.joint setup.dh seed scalar candidate message]
  simp only [Option.map_map,Prod.map_apply,id_eq]
  rfl
theorem actual_demand (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : Message)
    (before : RegistrationNativeSelectiveHiddenService.State n) :
    ((actualRoots setup seed scalar candidate (.inr message))).run before =
      simulateQ PqxdhRecordLiftInterface.effectLift
        ((RegistrationNativeSelectiveHiddenService.demand setup.source
          (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
          (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
          candidate (RegistrationNativeSecretWordMessage.eval candidate message)).run before) := rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformLorOpenDictionary


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorOpenDictionary.prepare_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorOpenDictionary.prepare_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorOpenDictionary.demand_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorOpenDictionary.demand_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorOpenDictionary.prepare_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorOpenDictionary.prepare_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorOpenDictionary.kem_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorOpenDictionary.kem_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorOpenDictionary.nonrouted_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorOpenDictionary.nonrouted_kem

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorOpenDictionary.actual_prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorOpenDictionary.actual_prepare

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorOpenDictionary.actual_demand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorOpenDictionary.actual_demand
