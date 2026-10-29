-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropyWorld

/-! Erasing the adapter's public mailbox recovers the exact native World computation for arbitrary adaptive ordinary programs. This is proved from the concrete restricted callbacks and does not assume a source simulation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEntropyCore
open RegistrationNativeEntropyInterface (Environment metadata userHmac)
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhSecretInputKdf (zeroSalt)
variable {n : Nat} {E Value : Type}

def compiler : QueryImpl RegistrationNativeInterface.Spec (OracleComp PqxdhDeploymentInterface.Spec)
  | .inl coin => PqxdhDeploymentInterface.Spec.query (.inl coin)
  | .inr (.create edPin mlPin keyId) => do
      let _ ← PqxdhDeploymentInterface.Spec.query (.inr (.hmac zeroSalt (metadata mlPin)))
      PqxdhDeploymentInterface.Spec.query (.inr (.create edPin keyId))
  | .inr (.bundle owner) => PqxdhDeploymentInterface.Spec.query (.inr (.bundle owner))
  | .inr (.accept raw) => PqxdhDeploymentInterface.Spec.query (.inr (.accept raw))
  | .inr (.build session payload) => PqxdhDeploymentInterface.Spec.query (.inr (.build session payload))
  | .inr (.finish owner raw) => PqxdhDeploymentInterface.Spec.query (.inr (.finish owner raw))
  | .inr (.hmac key message) => PqxdhDeploymentInterface.Spec.query (.inr (.hmac key (userHmac message)))
  | .inr (.hash bytes) => PqxdhDeploymentInterface.Spec.query (.inr (.hash bytes))
  | .inr (.serverSend keyId plaintext) => PqxdhDeploymentInterface.Spec.query (.inr (.serverSend keyId plaintext))
  | .inr (.serverRaw raw) => PqxdhDeploymentInterface.Spec.query (.inr (.serverRaw raw))
  | .inr (.beaconSend owner plaintext) => PqxdhDeploymentInterface.Spec.query (.inr (.beaconSend owner plaintext))
  | .inr (.beaconRaw owner raw) => PqxdhDeploymentInterface.Spec.query (.inr (.beaconRaw owner raw))

def implementation (env : Environment n E) : QueryImpl RegistrationNativeInterface.Spec
    (StateT (RegistrationNativeEntropyPort.State E) (OracleComp (WorldSpec n))) :=
  PqxdhRecordLiftInterface.native (RegistrationNativeEntropyPort.environment env) ∘ₛ compiler

/-- The compiler's extra metadata operation has no World effect; every original ordinary callback and poststate is exact. -/
theorem query_drop (env : Environment n E) (query : RegistrationNativeInterface.Spec.Domain)
    (before : RegistrationNativeEntropyPort.State E) :
    Prod.map id Prod.snd <$> (implementation env query).run before =
      (RegistrationNativeEntropyWorld.native env query).run before.2 := by
  cases query with
  | inl coin => rfl
  | inr command =>
      cases command <;> simp only [implementation, QueryImpl.compose, compiler,
        simulateQ_bind, simulateQ_spec_query, PqxdhRecordLiftInterface.native,
        RegistrationNativeEntropyWorld.native, PqxdhRecordLiftInterface.environmentStep,
        RegistrationNativeEntropyWorld.environmentStep, RegistrationNativeEntropyPort.environment,
        RegistrationNativeEntropyPort.step, RegistrationNativeEntropyPort.native,
        RegistrationNativeEntropyInterface.decode_userHmac,
        StateT.run, simulateQ_map, Functor.map_map, Prod.map, id_eq]
      all_goals simp [StateT.lift, Functor.map_map, Prod.map]
      all_goals try rfl
      rename_i edPin mlPin keyId
      change Prod.map id Prod.snd <$>
        ((pure (zeroSalt, (mlPin, before.2)) : OracleComp (WorldSpec n) _) >>= fun marked =>
          simulateQ PqxdhRecordLiftInterface.effectLift
            ((fun result => (result.1, (marked.2.1, result.2))) <$>
              (env.step ⟨.create edPin marked.2.1 keyId, trivial⟩).run marked.2.2)) = _
      simp only [pure_bind, simulateQ_map, Functor.map_map]
      exact id_map _

/-- Whole adaptive ordinary programs have the exact native World trace and full native state after dropping the public transport mailbox. -/
theorem program_drop (env : Environment n E) (work : OracleComp RegistrationNativeInterface.Spec Value)
    (before : RegistrationNativeEntropyPort.State E) :
    Prod.map id Prod.snd <$> (simulateQ (implementation env) work).run before =
      (simulateQ (RegistrationNativeEntropyWorld.native env) work).run before.2 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd (query_drop env) work before

end BeaconcryptCore.Computational.RegistrationNativeEntropyCore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyCore.query_drop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyCore.query_drop
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyCore.program_drop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyCore.program_drop
