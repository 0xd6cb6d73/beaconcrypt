-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaRouting
import BeaconcryptCore.Computational.RegistrationNativePlatformReceiptPreservation
/-! Non-signing runtime callbacks retain the exact true-count ML table and chronological native signing receipts. Dynamic ordinary writer failures occur after these private coordinates have been retained. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaReceiptPreservation
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativePlatformMldsaTableProgram (runState)
variable {n : Nat} {E Platform Native ι KemSK : Type} {base : OracleSpec ι}

private theorem after_property (source : RegistrationNativeMldsa.Source)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : StateT Native (RegistrationNativePlatformMldsaProgram.M (handleSource source) Platform) (Option RawCtxSourceSend.Encrypted))
    (before : Native) (previous : Platform) (pool : Pool source) (property : Native → Pool source → Prop)
    (keeps : ∀ result ∈ support (runState source work before previous pool), property result.1.1.2 result.2)
    (result : ((Option RawCtxSourceSend.Encrypted × Native) × Platform) × Pool source)
    (supported : result ∈ support (runState source (RegistrationNativePlatformOrdinaryMldsaRouting.after reserve work) before previous pool)) :
    property result.1.1.2 result.2 := by
  rw [RegistrationNativePlatformOrdinaryMldsaRouting.table_after, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  simp only [bind_pure_comp, support_map] at continued
  obtain ⟨gated, _allocated, same⟩ := continued
  cases same
  exact keeps middle reached

/-- All non-signing actual runtime callbacks preserve both private ML logs, including refused ordinary frame publication. -/
theorem handler [primitive : AdapterSealPrimitive.Operations]
    (source : RegistrationNativeMldsa.Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential (handleSource source))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (allowed : RegistrationNativeMldsaReceiptPreservation.NonSigning query)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (previous : Platform) (pool : Pool source)
    (result : ((RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Platform) × Pool source)
    (supported : result ∈ support (runState source
      (RegistrationNativePlatformOrdinaryMldsaProfile.handler setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query) before previous pool)) :
    result.2 = pool ∧ result.1.1.2.server.world.world.2 = before.server.world.world.2 := by
  rw [RegistrationNativePlatformOrdinaryMldsaRouting.handler] at supported
  have original := RegistrationNativePlatformReceiptPreservation.handler (n := n) source setup checks
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation
    reserveRegistration reservePeer erased helper writer query allowed before previous pool
  cases query with
  | inl coin => exact original result supported
  | inr query => cases query with
    | serverSend keyId plaintext =>
      apply after_property source reserveFrame _ before previous pool
        (fun current nextPool => nextPool = pool ∧ current.server.world.world.2 = before.server.world.world.2) _ result supported
      exact original
    | beaconSend owner plaintext =>
      apply after_property source reserveFrame _ before previous pool
        (fun current nextPool => nextPool = pool ∧ current.server.world.world.2 = before.server.world.world.2) _ result supported
      exact original
    | _ => exact original result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaReceiptPreservation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaReceiptPreservation.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaReceiptPreservation.handler
