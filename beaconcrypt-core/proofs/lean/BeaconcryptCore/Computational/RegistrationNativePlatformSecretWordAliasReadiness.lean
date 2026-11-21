-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasClient
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessTraceSource
/-! The actual corrected chronological Word client derives native preparation safety from its own source program and literal empty initial sessions. Its full raw ledger, owner roster, provider and platform result are retained, and evaluated atom/literal aliases remain covered. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasReadiness
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message input)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordNativeReadinessTrace (read)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

variable (route : RawCtxServerRouting.SenderDecoder) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK)

local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "word" => RegistrationNativePlatformSecretWordFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before
local notation "initial" => RegistrationNativeSecretWordInterpreter.initial ordinary kem

/-- Every actual alias-client outcome retains its internally derived native preparation audit. -/
theorem client_no_bad (empty : before.1.server.sessions = [])
    (result : RegistrationNativePlatformSecretWordAliasClient.Result source n KemSK A Platform)
    (supported : result ∈ support (RegistrationNativePlatformSecretWordAliasClient.client setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      route (input setup.joint setup.dh seed scalar) inside provider serverKeyId bounds mode work before ordinary kem)) :
    (read setup seed scalar candidate result.1.2).bad = false := by
  simp only [RegistrationNativePlatformSecretWordAliasClient.client, RegistrationNativeSecretWordInterpreter.execute] at supported
  rw [← RegistrationNativePlatformSecretWordLiveSource.traced_source setup checks wire source route sign
    (input setup.joint setup.dh seed scalar) inside provider selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before empty ordinary kem] at supported
  have mapped := Set.mem_image_of_mem
    (fun actual => (actual.1, (read setup seed scalar candidate actual.1.2, actual.2))) supported
  rw [← support_map] at mapped
  have observed := RegistrationNativeSecretWordNativeReadinessTraceSource.nested_source setup canonical route sign inside provider seed scalar candidate
    word RegistrationNativeSecretWordFrontendTrace.initial initial
  simp only [RegistrationNativeSecretWordFrontendTrace.program] at mapped
  rw [← observed] at mapped
  have safe := RegistrationNativePlatformSecretWordLiveSource.traced_prepared setup checks wire source route sign
    (input setup.joint setup.dh seed scalar) inside provider selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer serverKeyId bounds mode work before empty ordinary kem
  exact (RegistrationNativeSecretWordNativeReadinessRun.program_good setup canonical route sign inside provider seed scalar candidate
    _ _ (RegistrationNativeSecretWordNativeReadiness.initial_good setup seed scalar candidate ordinary kem) safe
    (result.1, (read setup seed scalar candidate result.1.2, result.2)) mapped).2.2

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasReadiness

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasReadiness.client_no_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasReadiness.client_no_bad
