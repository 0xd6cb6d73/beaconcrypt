-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3OpenClosure
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasSource
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasReadiness
/-! The literal corrected public query tree closes through the actual early provider and finite native key compiler. Preparation cleanliness is derived from that tree's source chronology and empty initial sessions; the full reached ledger, platform and ordinary/provider result is retained before the final private-state observation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3CheckedActual
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (input)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativePlatformSecretWordOrdinary (evaluate)
open PqxdhKemIndCca
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

variable (route : RawCtxServerRouting.SenderDecoder) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK)

variable (target : Option PqxdhJointIdentity.DhOutput) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "actual" => simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
  (RegistrationNativePlatformPublicFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work (evaluate candidate before))
local notation "early" => RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate

noncomputable def nativeRun :=
  (simulateQ (RegistrationNativeSecretWordNativePlain.native setup canonical route sign seed scalar target early)
    (RegistrationNativeG2Trace.program actual)).run
      (RegistrationNativeSecretWordNativePlainProvider.embed candidate
        (RegistrationNativeSecretWordCheckedClosure.drop (RegistrationNativeSecretWordInterpreter.initial ordinary kem)))

/-- Every reached actual native trace has no valid demand without its earlier actual preparation. -/
theorem no_bad (empty : before.1.server.sessions = []) (result)
    (supported : result ∈ support (nativeRun setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route candidate seed scalar serverKeyId bounds mode work before ordinary kem target selected pairs publicKey challenge)) :
    (RegistrationNativeSecretWordNativeReadinessTrace.readNative setup seed scalar result.1.2.events).bad = false := by
  rw [nativeRun, RegistrationNativePlatformSecretWordAliasSource.native_source setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route candidate seed scalar serverKeyId bounds mode work before ordinary kem target selected pairs publicKey challenge empty] at supported
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported
  rw [support_map] at original
  obtain ⟨observed, reached, equal⟩ := original
  cases equal
  change (RegistrationNativeSecretWordNativeReadinessTrace.readNative setup seed scalar
    (RegistrationNativeSecretWordCheckedTrace.state candidate observed.1.2).events).bad = false
  rw [RegistrationNativeSecretWordNativeReadinessTrace.evaluated_read]
  exact RegistrationNativePlatformSecretWordAliasReadiness.client_no_bad setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route
    (RegistrationNativeSecretWordProtection.inside target) (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge)
    candidate seed scalar serverKeyId bounds mode work before ordinary kem empty observed reached

noncomputable def client :=
  RegistrationNativePlatformG3OpenClosure.client setup canonical route sign seed scalar target early actual ordinary
    (RegistrationNativeSecretWordKemProvider.evalState candidate kem)

/-- The actual open-retained frontend closes to its same native chronological result; no whole-source or readiness premise is supplied. -/
theorem client_source (empty : before.1.server.sessions = []) :
    client setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route candidate seed scalar serverKeyId bounds mode work before ordinary kem target selected pairs publicKey challenge =
      Prod.fst <$> nativeRun setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route candidate seed scalar serverKeyId bounds mode work before ordinary kem target selected pairs publicKey challenge := by
  apply RegistrationNativePlatformG3OpenClosure.client_source
  intro result supported
  have clean := no_bad setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route candidate seed scalar serverKeyId bounds mode work before ordinary kem target selected pairs publicKey challenge empty result supported
  have same := congrArg Prod.snd (RegistrationNativeG3NativeCheckedTrace.read_native setup seed scalar result.1.2.events)
  exact same.symm.trans clean

end BeaconcryptCore.Computational.RegistrationNativePlatformG3CheckedActual

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3CheckedActual.no_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3CheckedActual.no_bad

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3CheckedActual.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3CheckedActual.client_source
