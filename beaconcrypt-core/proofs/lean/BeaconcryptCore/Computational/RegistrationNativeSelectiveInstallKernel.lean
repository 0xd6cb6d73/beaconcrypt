-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocation
import BeaconcryptCore.Computational.RegistrationNativeG2Trace
import BeaconcryptCore.Computational.RegistrationNativeInstallHistory
import BeaconcryptCore.Computational.RegistrationNativeRecordHandleSlots

/-! The actual selective typed callback retains its original G2 chronology beside the complete allocation, cursor, Protocol control and private service state. Dropping only that observer recovers the existing exact allocation kernel, so its physical-index and safety invariants remain about the same execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveInstallKernel
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeHiddenEnvironmentWorld (lower)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev State (n : Nat) (KemSK ProviderState Secret : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativeG2Trace.State × RegistrationNativeSelectiveAllocationJoint.State n KemSK ProviderState Secret source

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : A → B) (work : StateT S m A) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

noncomputable def front
    (implementation : QueryImpl TypedSpec (RegistrationNativePublicFrontend.M n KemSK source))
    (trace : RegistrationNativeG2Trace.State) (query : TypedSpec.Domain) :
    RegistrationNativePublicFrontend.M n KemSK source (TypedSpec.Range query × RegistrationNativeG2Trace.State) := fun before =>
  (fun result => ((result.1.1, result.2), result.1.2)) <$>
    (simulateQ RegistrationNativeG2Trace.handler ((implementation query).run before)).run trace

/-- The typed callback observer erases to precisely the same original frontend state transition. -/
theorem front_erase
    (implementation : QueryImpl TypedSpec (RegistrationNativePublicFrontend.M n KemSK source))
    (trace : RegistrationNativeG2Trace.State) (query : TypedSpec.Domain) :
    Prod.fst <$> front implementation trace query = implementation query := by
  funext before
  simp only [front, state_map_apply, Functor.map_map, Prod.map_def, id_eq]
  exact RegistrationNativeG2Trace.program_erase ((implementation query).run before) trace

private theorem close_map (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (observe : Value → Next) (work : RegistrationNativePublicFrontend.M n KemSK source Value) :
    RegistrationNativeSelectiveEntropyEffects.close setup wire sign seed scalar candidate provider (observe <$> work) =
      observe <$> RegistrationNativeSelectiveEntropyEffects.close setup wire sign seed scalar candidate provider work := by
  funext before
  simp only [RegistrationNativeSelectiveEntropyEffects.close, StateT.run_map, state_map_apply, simulateQ_map,
    Functor.map_map, Prod.map_def, id_eq]

private theorem lower_map
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (observe : Value → Next)
    (work : StateT (RegistrationNativeSelectiveEntropyEnvironment.State n KemSK ProviderState source)
      (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)) Value) :
    lower service codec route (observe <$> work) = observe <$> lower service codec route work := by
  funext before
  simp only [lower, StateT.run_map, state_map_apply, RegistrationNativeHiddenEnvironmentWorld.interpret_map,
    Functor.map_map, Prod.map_def, id_eq]

noncomputable def typed (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (selectedOwner selectedAccept : Nat) : QueryImpl TypedSpec (StateT (State n KemSK ProviderState Secret source) ProbComp) := fun query before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (lower service codec route (RegistrationNativeSelectiveEntropyEffects.close setup wire sign seed scalar candidate provider
      (front (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar))
        before.1 query))).run before.2

/-- Erasing only the same-run chronology recovers the actual original selective allocation callback, including every physical World and private state. -/
theorem typed_erase (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (selectedOwner selectedAccept : Nat) (query : TypedSpec.Domain) (before : State n KemSK ProviderState Secret source) :
    Prod.map id Prod.snd <$> (typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept query).run before =
      (RegistrationNativeSelectiveAllocation.typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept query).run before.2 := by
  rw [RegistrationNativeSelectiveAllocation.typed,
    ← front_erase (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar)) before.1 query,
    close_map, lower_map]
  unfold typed
  simp only [StateT.run, state_map_apply, Functor.map_map, Prod.map_def, id_eq]

/-- The actual traced callback preserves physical owner allocation after dropping only its additive observer. -/
theorem typed_holds (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (selectedOwner selectedAccept : Nat) (query : TypedSpec.Domain) (before : State n KemSK ProviderState Secret source)
    (result : TypedSpec.Range query × State n KemSK ProviderState Secret source)
    (prior : RegistrationNativeSelectiveAllocationJoint.Holds before.2)
    (supported : result ∈ support
      ((typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept query).run before)) :
    RegistrationNativeSelectiveAllocationJoint.Holds result.2.2 := by
  have mapped := Set.mem_image_of_mem (Prod.map id Prod.snd) supported
  rw [← support_map, typed_erase] at mapped
  exact RegistrationNativeSelectiveAllocation.typed_holds setup checks wire sign seed scalar candidate provider service codec route
    selectedOwner selectedAccept query before.2 (result.1, result.2.2) prior mapped

private theorem lower_storage
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : StateT (RegistrationNativeSelectiveEntropyEnvironment.State n KemSK ProviderState source)
      (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)) Value)
    (before : RegistrationNativeSelectiveAllocationJoint.State n KemSK ProviderState Secret source)
    (result : Value × RegistrationNativeSelectiveAllocationJoint.State n KemSK ProviderState Secret source)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (supported : result ∈ support ((lower service codec route work).run before)) :
    PqxdhRecordLiftProtocolHistory.Safe result.2.1.2 ∧
      ∀ handle slot, PqxdhRecordLiftIdeal.handleSlot before.1.2 handle = some slot →
        PqxdhRecordLiftIdeal.handleSlot result.2.1.2 handle = some slot := by
  rw [RegistrationNativeHiddenEnvironmentWorld.lower_run, support_map] at supported
  obtain ⟨actual, called, equal⟩ := supported
  cases equal
  exact RegistrationNativeRecordHandleSlots.interpreted service codec route (work.run before.1.1.1)
    before.1.1.2 before.1.2 safe before.2 actual called

/-- The same actual traced callback preserves Protocol safety and every already installed physical hidden slot under an arbitrary permitted private service. -/
theorem typed_storage (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (selectedOwner selectedAccept : Nat) (query : TypedSpec.Domain) (before : State n KemSK ProviderState Secret source)
    (result : TypedSpec.Range query × State n KemSK ProviderState Secret source)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.2.1.2)
    (supported : result ∈ support
      ((typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept query).run before)) :
    PqxdhRecordLiftProtocolHistory.Safe result.2.2.1.2 ∧
      ∀ handle slot, PqxdhRecordLiftIdeal.handleSlot before.2.1.2 handle = some slot →
        PqxdhRecordLiftIdeal.handleSlot result.2.2.1.2 handle = some slot := by
  simp only [typed, StateT.run, support_map] at supported
  obtain ⟨actual, called, equal⟩ := supported
  cases equal
  exact lower_storage service codec route _ before.2 actual safe called

end BeaconcryptCore.Computational.RegistrationNativeSelectiveInstallKernel
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveInstallKernel.front_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveInstallKernel.front_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveInstallKernel.typed_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveInstallKernel.typed_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveInstallKernel.typed_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveInstallKernel.typed_holds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveInstallKernel.typed_storage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveInstallKernel.typed_storage
