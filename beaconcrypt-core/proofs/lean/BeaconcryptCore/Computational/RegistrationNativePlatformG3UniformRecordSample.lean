-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordTraceView
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefixState
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceStateProperties
/-! The genuine whole-prefix sampler supplies the reserved selected KEM row at its own reached physical coin state. Only the sampler result is projected for this support receipt; physical counters, cache and poststate remain in the actual traced execution. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSample
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicRecordOpaqueInitialized (Context prior)
variable {I KemSK Platform E Value Secret : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
open RegistrationNativePlatformG3UniformRecordProgram (Sample sample program)
variable (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform)
local notation "cap" => budget.cap 4 + budget.cap 5
local notation "codec" => RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)

omit primitive in
private theorem profile_selected (count : Nat) (chosenIndex : Fin (count+1))
    (profile : RegistrationNativeSecretWordAliasOuter.Profile KemSK)
    (supported : profile ∈ support (RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem count chosenIndex)) :
    count ≤ profile.pairs.length ∧ ∃ chosen,profile.pairs[chosenIndex.val]?=some chosen ∧ chosen.1=profile.publicKey := by
  simp only [RegistrationNativeG3NativeRepeatUniformBound.prior,mem_support_bind_iff] at supported
  obtain ⟨chosen,_chosen,others,_others,pair,_pair,returned⟩ := supported
  rw [mem_support_pure_iff] at returned
  cases returned
  refine ⟨by simp only [List.length_ofFn];omega,chosen,?_,rfl⟩
  simpa only [List.nil_append,List.length_nil,Nat.zero_add] using PqxdhLiveKemSelection.selected_index [] chosenIndex chosen others

omit primitive in
/-- The actual complete sampler contains the genuine selected row, with enough rows for every original constructor. -/
theorem sample_selected (parameters : Sample KemSK (budget.cap 4+budget.cap 5))
    (supported : parameters ∈ support (sample setup budget selected)) :
    budget.create ≤ parameters.profile.pairs.length ∧ ∃ chosen,parameters.profile.pairs[selected.val]?=some chosen ∧ chosen.1=parameters.profile.publicKey := by
  simp only [sample,RegistrationNativePlatformG3UniformOpaqueGame.draws,bind_assoc,pure_bind,mem_support_bind_iff] at supported
  obtain ⟨seed,_seed,scalar,_scalar,unused,_unused,profile,reserved,candidate,_candidate,materials,_materials,returned⟩ := supported
  rw [mem_support_pure_iff] at returned
  cases returned
  exact profile_selected setup budget.create selected profile reserved

/-- Actual physical sampler interpretation retains that same selected-row receipt beside the unchanged reached private execution. -/
theorem staged_selected
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec (budget.cap 4+budget.cap 5)) (StateT Secret ProbComp))
    (initialSecret : Secret) (parameters : Sample KemSK (budget.cap 4+budget.cap 5))
    (result : RegistrationNativePlatformSelectiveRecordTraceHidden.Result (budget.cap 4+budget.cap 5) KemSK
      RegistrationNativeKemSwitchSource.Phase Platform Secret Value source)
    (supported : (parameters,result) ∈ support (RegistrationNativePlatformG3UniformRecordTrace.staged setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous service initialSecret)) :
    budget.create ≤ parameters.profile.pairs.length ∧ ∃ chosen,parameters.profile.pairs[selected.val]?=some chosen ∧ chosen.1=parameters.profile.publicKey := by
  simp only [RegistrationNativePlatformG3UniformRecordTrace.staged,mem_support_bind_iff,mem_support_pure_iff] at supported
  obtain ⟨sampled,called,result,_continued,same⟩ := supported
  cases same
  apply sample_selected setup budget selected sampled.1
  apply OracleComp.support_simulateQ_run'_subset (RegistrationNativePlatformRecordPrefixState.coins service) _ initialSecret
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst called

/-- The actual warm trace view keeps its own genuine selected row without changing the physical cache or its sampling accounting. -/
theorem view_selected (modes : PqxdhRecordLiftWorldCompiler.Label (budget.cap 4+budget.cap 5) → PqxdhRecordLiftIdeal.KeyMode)
    (parameters : Sample KemSK (budget.cap 4+budget.cap 5))
    (observed : RegistrationNativeRecordPackage.View (budget.cap 4+budget.cap 5)
      (RegistrationNativePlatformSelectiveRecordTraceStartup.Extra (budget.cap 4+budget.cap 5) KemSK RegistrationNativeKemSwitchSource.Phase Platform source) Value)
    (supported : (parameters,observed) ∈ support (RegistrationNativePlatformG3UniformRecordTraceView.run setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous modes)) :
    budget.create ≤ parameters.profile.pairs.length ∧ ∃ chosen,parameters.profile.pairs[selected.val]?=some chosen ∧ chosen.1=parameters.profile.publicKey := by
  rw [RegistrationNativePlatformG3UniformRecordTraceView.run,support_map] at supported
  obtain ⟨raw,called,same⟩ := supported
  cases same
  exact staged_selected setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous
    (PqxdhRecordLiftIdeal.ctxInterpreter modes id setup codec) PqxdhRecordLiftIdeal.CtxPrivate.initial raw.1 raw.2 called

end BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSample

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSample.sample_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSample.sample_selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSample.staged_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSample.staged_selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSample.view_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSample.view_selected
