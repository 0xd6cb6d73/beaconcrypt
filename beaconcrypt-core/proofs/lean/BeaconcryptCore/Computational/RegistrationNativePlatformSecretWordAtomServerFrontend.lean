-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerControl
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
/-! The literal whole corrected Server build records at most its moved Ready’s atom weight in the same chronological observer. It retains the actual stateful publication and complete frontend/platform result. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerFrontend
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
variable {n : Nat} {I KemSK Platform E A Observation : Type} {base : OracleSpec I}

open RegistrationNativeSecretWordFrontendTrace (State handler)
open RegistrationNativeSecretWordAtomInstallTrace (count)

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map _ _ _

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


/-- The actual full corrected build callback funds its same-run attempts only from its literal consumed handle. -/
theorem build_count (role : PqxdhRecordLiftInterface.Role) (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform) (trace : State)
    (result : (RustM (Option (U64 × Pqxdh.Bytes)) × RegistrationNativePlatformSecretWordOrdinary.State source Platform) × State)
    (supported : result ∈ support ((simulateQ handler
      ((RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.build handle application))).run before)).run trace)) :
    count role result.2 ≤ count role trace + (if role = .server then 1 else 0) *
      RegistrationNativeSecretWordAtomSessionCredit.weight (RegistrationNativeSecretWordServerMaterial.take handle before.1.server).1 := by
  simp only [RegistrationNativePlatformSecretWordFrontend.handler, RegistrationNativePlatformSecretWordFrontend.build,
    StateT.run, simulateQ_map, map_apply, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  cases equal
  exact RegistrationNativePlatformSecretWordAtomServerControl.body_count setup.source view failure allocation erased helper sign writer reservePeer
    role handle application before.1.server (before.1.environment.receipts, before.2) trace reached called

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerFrontend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerFrontend.build_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerFrontend.build_count
