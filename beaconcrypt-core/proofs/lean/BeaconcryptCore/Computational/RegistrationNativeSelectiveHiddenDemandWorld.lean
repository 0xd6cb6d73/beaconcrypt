-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemand
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreter
import BeaconcryptCore.Computational.RegistrationNativeRecordHandleSlots
import BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentWorld

/-! The actual closed selective material callback retains its successful hidden reference and persistent slot under the same cursor/Protocol/private-service interpretation. This consumes the real atom/protected-head receipt at the executing descriptor, rather than postulating a selected ideal reply. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemandWorld
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeHiddenEnvironmentWorld (State lower)
variable {n : Nat} {ι KemSK E Secret ProviderState Value : Type} {base : OracleSpec ι}

/-- Actual lowering can only choose a supported reply of the original local World program. -/
theorem lower_support (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec E Value) (route : RawCtxServerRouting.SenderDecoder)
    {Local Result : Type} (work : StateT Local (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)) Result)
    (before : State n Local Secret) (result : Result × State n Local Secret)
    (supported : result ∈ support ((lower service codec route work).run before)) :
    (result.1, result.2.1.1.1) ∈ support (work.run before.1.1.1) := by
  rw [RegistrationNativeHiddenEnvironmentWorld.lower_run, support_map] at supported
  obtain ⟨reached, called, returned⟩ := supported
  have original := RegistrationNativeRecordHandleSlots.open_support service codec route (work.run before.1.1.1)
    before.1.1.2 before.1.2 before.2 reached called
  have equal : reached.1.1.1 = (result.1, result.2.1.1.1) := congrArg (fun value => (value.1, value.2.1.1.1)) returned
  rw [← equal]
  exact original

private theorem simulation_support {Index Target Result : Type} {spec : OracleSpec Index} {target : OracleSpec Target}
    (implementation : QueryImpl spec (OracleComp target)) (work : OracleComp spec Result) (result : Result)
    (supported : result ∈ support (simulateQ implementation work)) : result ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure, mem_support_pure_iff] using supported
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
      obtain ⟨reply, _called, continued⟩ := supported
      rw [mem_support_bind_iff]
      exact ⟨reply, mem_support_query _ _, ih reply continued⟩

/-- The executing native selected material query can only succeed with its own hidden slot and public material. -/
theorem source_demand (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (message : RegistrationNativeRelatedFamily.Message) (bytes : Pqxdh.Bytes)
    (before after : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (choice : RegistrationNativePairedChoice.Choice n)
    (realized : RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes)
    (selected : RegistrationNativeSelectiveHiddenService.selected
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true)
    (original : (some choice, after) ∈ support
      ((RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider
        (.inl (.inr (.inl (.inl message))))).run before)) :
    ∃ reference, choice = .hidden reference ∧ after.1.keys.slots bytes = some reference.slot ∧
      after.1.keys.materials reference.slot = some reference.material := by
  rw [RegistrationNativeSelectiveHiddenInterpreter.query_demand] at original
  simp only [RegistrationNativeSelectiveHiddenInterpreter.onKeys, StateT.run, support_map] at original
  obtain ⟨result, possible, returned⟩ := original
  have reached := simulation_support PqxdhRecordLiftInterface.effectLift _ _ possible
  have reply : result.1 = some choice := congrArg Prod.fst returned
  have keys : result.2.1 = after.1.keys := congrArg (fun value => value.2.1.keys) returned
  have known : result.2.2 = after.2 := congrArg (fun value => value.2.2) returned
  have equal : result = (some choice, (after.1.keys, after.2)) :=
    Prod.ext reply (Prod.ext keys known)
  rw [equal] at reached
  exact RegistrationNativeSelectiveHiddenDemand.successful setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
    candidate message bytes (before.1.keys, before.2) (after.1.keys, after.2)
    choice realized selected reached

/-- The executing native selected material query can only succeed with its own hidden slot and public material. -/
theorem demand (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (message : RegistrationNativeRelatedFamily.Message) (bytes : Pqxdh.Bytes)
    (before after : State n (RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) Secret)
    (choice : RegistrationNativePairedChoice.Choice n)
    (realized : RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes)
    (selected : RegistrationNativeSelectiveHiddenService.selected
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true)
    (supported : (some choice, after) ∈ support ((lower service (RegistrationNativeWire.ledgerCodec wire) route
      (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider
        (.inl (.inr (.inl (.inl message)))))).run before)) :
    ∃ reference, choice = .hidden reference ∧ after.1.1.1.1.keys.slots bytes = some reference.slot ∧
      after.1.1.1.1.keys.materials reference.slot = some reference.material := by
  have original := lower_support service (RegistrationNativeWire.ledgerCodec wire) route _ before (some choice, after) supported
  rw [RegistrationNativeSelectiveHiddenInterpreter.query_demand] at original
  simp only [RegistrationNativeSelectiveHiddenInterpreter.onKeys, StateT.run, support_map] at original
  obtain ⟨result, possible, returned⟩ := original
  have reached := simulation_support PqxdhRecordLiftInterface.effectLift _ _ possible
  have reply : result.1 = some choice := congrArg Prod.fst returned
  have keys : result.2.1 = after.1.1.1.1.keys := congrArg (fun value => value.2.1.keys) returned
  have known : result.2.2 = after.1.1.1.2 := congrArg (fun value => value.2.2) returned
  have equal : result = (some choice, (after.1.1.1.1.keys, after.1.1.1.2)) :=
    Prod.ext reply (Prod.ext keys known)
  rw [equal] at reached
  exact RegistrationNativeSelectiveHiddenDemand.successful setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
    candidate message bytes (before.1.1.1.1.keys, before.1.1.1.2) (after.1.1.1.1.keys, after.1.1.1.2)
    choice realized selected reached

end BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemandWorld

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemandWorld.lower_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemandWorld.lower_support
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemandWorld.demand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemandWorld.demand

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemandWorld.source_demand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemandWorld.source_demand
