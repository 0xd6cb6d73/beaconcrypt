-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCreateBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPoolPrefix
/-! The current full Word source consumes the early KEM reservation in exact birth order under its original public create allowance. The current source-derived constructor cap rules out fallback; no final-owner activation or private row association is supplied as a premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPoolPrefix
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
open RegistrationNativeSecretWordTargetPublication (key)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

open RegistrationNativePlatformSecretWordAliasAlignment (State)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n) setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformSecretWordExecution.typed (n := n) setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer controller



open RegistrationNativeSecretWordTargetPoolPrefix (Prefixed)

/-- The actual complete current raw frontend retains its reserved private-key prefix and original public create cap. -/
theorem run_prefix (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (frontend : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK) (empty : before.kem.1.keys = [])
    (result : ((A × RegistrationNativeLedger.State) × RegistrationNativePlatformSecretWordOrdinary.State source Platform) ×
      RegistrationNativeSecretWordInterpreter.State n KemSK)
    (supported : result ∈ support ((simulateQ implementation
      (RegistrationNativePlatformSecretWordFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work frontend)).run before)) :
    Prefixed pairs result.2 ∧ result.2.kem.1.keys.length ≤ budget.create := by
  have bill := RegistrationNativePlatformSecretWordTargetCreateBounds.run_bound (n := n) setup checks wire source sign
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    serverKeyId bounds mode work budget bounded frontend
  have initial : Prefixed pairs before := by simp only [Prefixed, empty, List.length_nil, List.take_zero]
  have room : before.kem.1.keys.length + budget.create ≤ pairs.length := by simpa only [empty, List.length_nil, Nat.zero_add] using reserved
  simpa only [empty, List.length_nil, Nat.zero_add] using
    RegistrationNativeSecretWordTargetPoolPrefix.program_prefix setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside
      selected pairs publicKey challenge outer _ budget.create bill before initial room result supported

/-- The same exact reserved birth prefix holds directly in the original full-ledger product state. -/
theorem full_prefix (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (before : State n KemSK source Platform) (empty : before.2.kem.1.keys = [])
    (result : A × (RegistrationNativeLedger.State × State n KemSK source Platform))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      serverKeyId bounds typed mode work before)) :
    Prefixed pairs result.2.2.2 ∧ result.2.2.2.kem.1.keys.length ≤ budget.create := by
  rw [RegistrationNativeFullCompiler.compile_run, support_map] at supported
  obtain ⟨typedResult, called, same⟩ := supported
  rw [RegistrationNativePlatformSecretWordExecution.typed, OracleComp.simulateQ_flattenStateT_run,
    bind_pure_comp, support_map] at called
  obtain ⟨sourceResult, sourceCalled, typedEq⟩ := called
  rw [← QueryImpl.simulateQ_mapStateTBase_run] at sourceCalled
  have prefixed := run_prefix setup checks wire source route sign input inside selected pairs publicKey challenge outer
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    serverKeyId bounds mode work budget bounded reserved before.1 before.2 empty sourceResult sourceCalled
  cases typedEq
  cases same
  exact prefixed

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPoolPrefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPoolPrefix.run_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPoolPrefix.run_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPoolPrefix.full_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPoolPrefix.full_prefix
