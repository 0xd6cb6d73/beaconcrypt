-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTraceSource
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyExecution
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointErasure
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenInterpreter (Provider)
variable {n : Nat} {I KemSK ProviderState Physical A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
local notation "backend" => RegistrationNativePlatformRecordPartnerSlotInput.closed setup wire sign seed scalar candidate provider physical
local notation "actual" => RegistrationNativePlatformRecordPartnerSlotTrace.handler setup wire sign seed scalar candidate provider physical

private theorem world_embedding :
    RegistrationNativeSelectiveHiddenInterpreter.handler (n := n) setup wire sign seed scalar candidate provider ∘ₛ
      RegistrationNativePlatformPublicCoinEmbedding.embed =
      RegistrationNativePlatformSelectiveEntropyBackend.handler setup wire sign seed scalar candidate provider := by
  funext query
  cases query with
  | inl query =>
      simp only [QueryImpl.apply_compose, RegistrationNativePlatformPublicCoinEmbedding.embed,
        simulateQ_spec_query, RegistrationNativePlatformSelectiveEntropyBackend.handler]
  | inr coin =>
      funext before
      simp only [QueryImpl.apply_compose, RegistrationNativePlatformPublicCoinEmbedding.embed,
        RegistrationNativePublicFrontend.effect, RegistrationNativePublicFrontend.liftLocal, simulateQ_spec_query,
        RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onBase,
        RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.effect,
        RegistrationNativePlatformSelectiveEntropyBackend.handler, StateT.run_lift, bind_pure_comp,
        PqxdhRecordLiftInterface.effectLift, Functor.map_map]
      rfl

/-- Dropping only the two private analysis observers retains the literal complete native/private/physical execution. -/
theorem erase (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A)
    (before : RegistrationNativePlatformRecordPartnerSlotTrace.State n KemSK ProviderState Physical) :
    (fun result => (result.1,result.2.2.2)) <$> (simulateQ actual work).run before =
      (simulateQ backend work).run before.2.2 := by
  rw [RegistrationNativePlatformRecordPartnerSlotTrace.program_source setup wire sign seed scalar candidate provider physical]
  have slots := congrArg (fun tree => (simulateQ backend tree).run before.2.2)
    (RegistrationNativePlatformPublicRecordSlots.program_erase
      ((simulateQ RegistrationNativeG2Trace.handler work).run before.2.1) before.1)
  have trace := congrArg (fun tree => (simulateQ backend tree).run before.2.2)
    (RegistrationNativeG2Trace.program_erase work before.2.1)
  simp only [simulateQ_map,StateT.run_map] at slots trace
  rw [←trace,←slots]
  simp only [Functor.map_map]

/-- The same joint observer closes the exact source World AST under an arbitrary persistent physical record interpreter and warm state. -/
theorem world_source (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A)
    (before : RegistrationNativePlatformRecordPartnerSlotTrace.State n KemSK ProviderState Physical) :
    (fun result => (result.1,result.2.2.2)) <$> (simulateQ actual work).run before =
      (fun result => (result.1.1,(result.1.2,result.2))) <$>
        (simulateQ physical ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider) work).run before.2.2.1)).run before.2.2.2 := by
  rw [erase]
  rw [RegistrationNativePlatformRecordPartnerSlotInput.closed,OracleComp.simulateQ_flattenStateT_run,
    ←QueryImpl.simulateQ_mapStateTBase_run,bind_pure_comp]
variable {Platform E : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (checks : PqxdhServerAuthExperiment.Checks) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))


/-- The current complete raw frontend has the same warm physical execution after erasing only its joint slot/descriptor observers. All native replies, ledger, source and platform state remain literal. -/
theorem run (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (front : RegistrationNativePlatformPublicFrontend.State source Platform)
    (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) (physicalBefore : Physical)
    (slots : RegistrationNativePlatformPublicRecordSlots.State n) (trace : RegistrationNativeG2Trace.State) :
    (fun result => ((result.1.1,(result.1.2,result.2.2.2.1)),result.2.2.2.2)) <$>
      (simulateQ (RegistrationNativePlatformRecordPartnerSlotTrace.handler setup
        (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider physical)
        (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
          (RegistrationNativePlatformPublicFrontend.run setup checks wire source (RegistrationNativeMldsa.owned source credential)
            selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
            serverKeyId bounds mode work front))).run (slots,trace,(privateBefore,physicalBefore)) =
    (simulateQ physical (RegistrationNativePlatformSelectiveEntropyExecution.run setup checks wire source credential seed scalar candidate provider
      selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      serverKeyId bounds mode work (front,privateBefore))).run physicalBefore := by
  have whole := congrArg (Functor.map (fun result => ((result.1.1,(result.1.2,result.2.1)),result.2.2)))
    (world_source setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) (RegistrationNativeMldsa.owned source credential)
      seed scalar candidate provider physical
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        (RegistrationNativePlatformPublicFrontend.run setup checks wire source (RegistrationNativeMldsa.owned source credential)
          selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          serverKeyId bounds mode work front)) (slots,trace,(privateBefore,physicalBefore)))
  conv_rhs at whole => rw [←QueryImpl.simulateQ_compose,world_embedding]
  have execution := congrArg (fun tree => (simulateQ physical tree).run physicalBefore)
    (RegistrationNativePlatformSelectiveEntropyExecution.run_source setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work (front,privateBefore))
  simp only [simulateQ_map,StateT.run_map,Functor.map_map] at execution whole
  exact whole.trans execution

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointErasure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointErasure.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointErasure.erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointErasure.world_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointErasure.world_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointErasure.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointErasure.run
