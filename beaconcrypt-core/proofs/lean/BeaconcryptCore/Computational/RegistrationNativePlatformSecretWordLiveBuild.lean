-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBuildSessions
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBuildFree
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveState
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSafety
/-! The actual common-state Word build uses only prepared moved references and retains exactly the remaining one-use sessions. This combines its literal dynamic source compiler with the checked preparation interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBuild
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked AllPrepared)
open RegistrationNativeSecretWordLiveFlags (Valid)
open RegistrationNativeSecretWordLiveSessions (Live)
open RegistrationNativePlatformSecretWordOrdinary (State)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}

private theorem support_simulate_subset {J K : Type} {spec : OracleSpec J} {target : OracleSpec K}
    (implementation : QueryImpl spec (OracleComp target)) (work : OracleComp spec A) (value : A)
    (supported : value ∈ support (simulateQ implementation work)) : value ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure result =>
      rw [simulateQ_pure, mem_support_pure_iff] at supported
      rw [mem_support_pure_iff]
      exact supported
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
      obtain ⟨reply, _called, supported⟩ := supported
      change value ∈ support ((spec.query query : OracleComp spec _) >>= next)
      rw [mem_support_bind_iff]
      exact ⟨reply, mem_support_query query reply, ih reply supported⟩

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool)

/-- Every raw supported source build leaves exactly the session roster after the original one-use take. -/
theorem sessions (source : RegistrationNativeMldsa.Source) (handle : Nat) (application : Option (Slice U8))
    (before : State source Platform) (result : RustM (Option (U64 × Pqxdh.Bytes)) × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordFrontend.build (n := n) setup sign view failure allocation
      erased helper writer reserve handle application source).run before)) :
    result.2.1.server.sessions = (RegistrationNativeSecretWordServerMaterial.take handle before.1.server).2.sessions := by
  simp only [RegistrationNativePlatformSecretWordFrontend.build, StateT.run, support_map] at supported
  obtain ⟨reached, possible, equal⟩ := supported
  have raw := support_simulate_subset _ _ reached possible
  have same := RegistrationNativePlatformSecretWordLiveBuildSessions.body_sessions setup.source view failure allocation erased helper sign writer reserve
    handle application before.1.server (before.1.environment.receipts, before.2) reached raw
  cases equal
  exact same

/-- The literal full source build demands no reference outside its internally live taken capability. -/
theorem prepared (source : RegistrationNativeMldsa.Source) (handle : Nat) (application : Option (Slice U8))
    (before : State source Platform) (context : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (valid : Valid input context) (live : Live before.1.server context.flags) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider)
      ((RegistrationNativePlatformSecretWordFrontend.build (n := n) setup sign view failure allocation erased helper writer reserve
        handle application source).run before) context := by
  simp only [RegistrationNativePlatformSecretWordFrontend.build, StateT.run]
  apply RegistrationNativeSecretWordLiveFrontendSafety.mapped setup wire route sign input inside provider _ _ context valid
  apply RegistrationNativeSecretWordLiveCaps.of_bound setup wire route sign input inside provider _ context valid
  exact RegistrationNativePlatformSecretWordLiveBuildFree.embedded_free context.flags _
    (RegistrationNativePlatformSecretWordLiveBuildFree.body_free setup.source view failure allocation erased helper sign writer reserve
      context.flags handle application before.1.server (before.1.environment.receipts, before.2) live)

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBuild

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBuild.sessions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBuild.sessions

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBuild.prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBuild.prepared
