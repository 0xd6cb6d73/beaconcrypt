-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocation
import BeaconcryptCore.Computational.RegistrationNativeG2Trace
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveCoinEmbedding
import BeaconcryptCore.Computational.RegistrationNativeRecordHandleSlots
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemandWorld
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveInstallKernel
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeHiddenEnvironmentWorld (lower)
open RegistrationNativePlatformPublicCoinEmbedding (embed)
variable {n : Nat} {I KemSK ProviderState Platform E Reader Response Secret Value Next : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

abbrev State (n : Nat) (KemSK ProviderState Platform Secret : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativeG2Trace.State × RegistrationNativePlatformHiddenAllocationCreate.State n KemSK ProviderState Platform Secret source

abbrev FrontendM (n : Nat) (KemSK Platform : Type) (source : RegistrationNativeMldsa.Source) :=
  StateT (RegistrationNativePlatformPublicFrontend.State source Platform) (OracleComp (RegistrationNativePublicFrontend.Spec n KemSK))

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : A → B) (work : StateT S m A) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

def embedded (work : RegistrationNativePlatformPublicFrontend.M n KemSK Platform source Value) : FrontendM n KemSK Platform source Value :=
  fun before => simulateQ embed (work.run before)

noncomputable def front
    (implementation : QueryImpl TypedSpec (RegistrationNativePlatformPublicFrontend.M n KemSK Platform source))
    (trace : RegistrationNativeG2Trace.State) (query : TypedSpec.Domain) : FrontendM n KemSK Platform source (TypedSpec.Range query × RegistrationNativeG2Trace.State) := fun before =>
  (fun result => ((result.1.1, result.2), result.1.2)) <$>
    (simulateQ RegistrationNativeG2Trace.handler (simulateQ embed ((implementation query).run before))).run trace

/-- The observer erases to the same corrected frontend tree with its explicit external-coin embedding and complete P state. -/
theorem front_erase
    (implementation : QueryImpl TypedSpec (RegistrationNativePlatformPublicFrontend.M n KemSK Platform source))
    (trace : RegistrationNativeG2Trace.State) (query : TypedSpec.Domain) :
    Prod.fst <$> front implementation trace query = embedded (implementation query) := by
  funext before
  simp only [front, embedded, map_apply, Functor.map_map, Prod.map_def, id_eq]
  exact RegistrationNativeG2Trace.program_erase _ trace

noncomputable def close (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (work : FrontendM n KemSK Platform source Value) :
    StateT (RegistrationNativePlatformSelectiveEntropyEnvironment.State n KemSK ProviderState Platform source)
      (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)) Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
      (work.run before.1)).run before.2

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)

private theorem close_map (observe : Value → Next) (work : FrontendM n KemSK Platform source Value) :
    close setup wire sign seed scalar candidate provider (observe <$> work) =
      observe <$> close setup wire sign seed scalar candidate provider work := by
  funext before
  simp only [close, StateT.run_map, map_apply, simulateQ_map, Functor.map_map, Prod.map_def, id_eq]

private theorem lower_map
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (observe : Value → Next)
    (work : StateT (RegistrationNativePlatformSelectiveEntropyEnvironment.State n KemSK ProviderState Platform source)
      (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)) Value) :
    lower service codec route (observe <$> work) = observe <$> lower service codec route work := by
  funext before
  simp only [lower, StateT.run_map, map_apply, RegistrationNativeHiddenEnvironmentWorld.interpret_map,
    Functor.map_map, Prod.map_def, id_eq]

/-- Closing the explicit embedding is exactly the current selective backend, without erasing World costs or private state. -/
theorem close_embedded (work : RegistrationNativePlatformPublicFrontend.M n KemSK Platform source Value) :
    close setup wire sign seed scalar candidate provider (embedded work) =
      RegistrationNativePlatformHiddenAllocationCore.close
        (RegistrationNativePlatformSelectiveEntropyBackend.handler setup wire sign seed scalar candidate provider) work := by
  funext before
  simp only [close, embedded, RegistrationNativePlatformHiddenAllocationCore.close, StateT.run]
  rw [RegistrationNativePlatformSelectiveCoinEmbedding.program]

variable [primitive : AdapterSealPrimitive.Operations]
    (checks : Checks) (credential : RegistrationNativeMldsa.Credential source)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "owned" => RegistrationNativeMldsa.owned source credential
local notation "frontend" => RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks canonical source owned selectedOwner selectedAccept
  (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

noncomputable def typed : QueryImpl TypedSpec (StateT (State n KemSK ProviderState Platform Secret source) ProbComp) := fun query before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (lower service codec route (close setup canonical owned seed scalar candidate provider
      (front frontend before.1 query))).run before.2

/-- Erasing only G2 chronology recovers the literal corrected allocation callback and every reached frontend, platform, cursor, control and private state. -/
theorem typed_erase (query : TypedSpec.Domain) (before : State n KemSK ProviderState Platform Secret source) :
    Prod.map id Prod.snd <$> (typed setup wire seed scalar candidate provider checks credential selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route query).run before =
      (RegistrationNativePlatformHiddenAllocation.typed setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route query).run before.2 := by
  have closed := congrArg (fun work => lower service codec route (close setup canonical owned seed scalar candidate provider work))
    (front_erase frontend before.1 query)
  rw [close_map, lower_map, close_embedded] at closed
  change _ = (lower service codec route (RegistrationNativePlatformHiddenAllocationCore.close
    (RegistrationNativePlatformSelectiveEntropyBackend.handler setup canonical owned seed scalar candidate provider) (frontend query))).run before.2
  rw [← closed]
  simp only [typed, StateT.run, map_apply, Functor.map_map, Prod.map_def, id_eq]

/-- The same traced corrected callback retains the derived physical/local allocation invariant. -/
theorem typed_holds (query : TypedSpec.Domain) (before : State n KemSK ProviderState Platform Secret source)
    (result : TypedSpec.Range query × State n KemSK ProviderState Platform Secret source)
    (prior : RegistrationNativePlatformHiddenAllocationCore.Holds before.2)
    (supported : result ∈ support ((typed setup wire seed scalar candidate provider checks credential selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route query).run before)) :
    RegistrationNativePlatformHiddenAllocationCore.Holds result.2.2 := by
  have mapped := Set.mem_image_of_mem (Prod.map id Prod.snd) supported
  rw [← support_map, typed_erase] at mapped
  exact RegistrationNativePlatformHiddenAllocation.typed_holds setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route query before.2 (result.1, result.2.2) prior mapped

omit primitive in
private theorem lower_storage
    (work : StateT (RegistrationNativePlatformSelectiveEntropyEnvironment.State n KemSK ProviderState Platform source)
      (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)) Value)
    (before : RegistrationNativePlatformHiddenAllocationCreate.State n KemSK ProviderState Platform Secret source)
    (result : Value × RegistrationNativePlatformHiddenAllocationCreate.State n KemSK ProviderState Platform Secret source)
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

/-- Protocol safety and every already installed physical slot persist under the actual traced callback, including every external platform effect. -/
theorem typed_storage (query : TypedSpec.Domain) (before : State n KemSK ProviderState Platform Secret source)
    (result : TypedSpec.Range query × State n KemSK ProviderState Platform Secret source)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.2.1.2)
    (supported : result ∈ support ((typed setup wire seed scalar candidate provider checks credential selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route query).run before)) :
    PqxdhRecordLiftProtocolHistory.Safe result.2.2.1.2 ∧
      ∀ handle slot, PqxdhRecordLiftIdeal.handleSlot before.2.1.2 handle = some slot →
        PqxdhRecordLiftIdeal.handleSlot result.2.2.1.2 handle = some slot := by
  simp only [typed, StateT.run, support_map] at supported
  obtain ⟨actual, called, equal⟩ := supported
  cases equal
  exact lower_storage service codec route _ before.2 actual safe called

/-- Forgetting only private interpretation retains the literal corrected reply, frontend/P poststate and original G2 observer on its explicit embedded tree. -/
theorem open_support (query : TypedSpec.Domain) (before : State n KemSK ProviderState Platform Secret source)
    (result : TypedSpec.Range query × State n KemSK ProviderState Platform Secret source)
    (supported : result ∈ support ((typed setup wire seed scalar candidate provider checks credential selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route query).run before)) :
    ((result.1, result.2.2.1.1.1.1), result.2.1) ∈ support
      ((simulateQ RegistrationNativeG2Trace.handler (simulateQ embed ((frontend query).run before.2.1.1.1.1))).run before.1) := by
  simp only [typed, StateT.run, support_map] at supported
  obtain ⟨raw, actual, returned⟩ := supported
  rcases raw with ⟨⟨reply, trace⟩, after⟩
  cases returned
  have opened := RegistrationNativeSelectiveHiddenDemandWorld.lower_support service codec route _ before.2 ((reply, trace), after) actual
  simp only [close, StateT.run, support_map] at opened
  obtain ⟨closed, called, closedEq⟩ := opened
  have original : closed.1 ∈ support ((front frontend before.1 query).run before.2.1.1.1.1) := by
    apply support_simulateQ_run'_subset
      (RegistrationNativeSelectiveHiddenInterpreter.handler setup canonical owned seed scalar candidate provider) _ before.2.1.1.1.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst called
  simp only [front, StateT.run, support_map] at original
  obtain ⟨native, possible, nativeEq⟩ := original
  have value : closed.1.1 = (reply, trace) := congrArg Prod.fst closedEq
  have frontendState : closed.1.2 = after.1.1.1.1 := congrArg (fun result => result.2.1) closedEq
  have same : native = ((reply, after.1.1.1.1), trace) :=
    Prod.ext
      (Prod.ext ((congrArg (fun result => result.1.1) nativeEq).trans (congrArg Prod.fst value))
        ((congrArg Prod.snd nativeEq).trans frontendState))
      ((congrArg (fun result => result.1.2) nativeEq).trans (congrArg Prod.snd value))
  rw [← same]
  exact possible

end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveInstallKernel

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveInstallKernel.front_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveInstallKernel.front_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveInstallKernel.close_embedded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveInstallKernel.close_embedded

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveInstallKernel.typed_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveInstallKernel.typed_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveInstallKernel.typed_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveInstallKernel.typed_holds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveInstallKernel.typed_storage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveInstallKernel.typed_storage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveInstallKernel.open_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveInstallKernel.open_support
