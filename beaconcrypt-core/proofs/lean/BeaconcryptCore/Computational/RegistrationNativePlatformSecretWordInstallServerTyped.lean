-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallServerControl
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
/-! The literal whole corrected Server build retains its exact successful installation count in the same chronological observer, including all actual stateful publication failures and the complete frontend/platform result. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallServerTyped
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
variable {n : Nat} {I KemSK Platform E A Observation : Type} {base : OracleSpec I}

open RegistrationNativeSecretWordFrontendTrace (State handler)
open RegistrationNativeSecretWordInstallOrdinals (messages)
open RegistrationNativeInstallBeaconComplete (present)

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


/-- The actual full corrected build callback has exactly its same-result successful installation count after preserving public response-byte presence. -/
theorem build_count (role : PqxdhRecordLiftInterface.Role) (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform) (trace : State)
    (result : (RustM (Option (U64 × Pqxdh.Bytes)) × RegistrationNativePlatformSecretWordOrdinary.State source Platform) × State)
    (supported : result ∈ support ((simulateQ handler
      ((RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.build handle application))).run before)).run trace)) :
    ∃ added, messages role result.2.events = messages role trace.events ++ added ∧
      added.length = if role = .server ∧ present result.1.1 = true then 1 else 0 := by
  simp only [RegistrationNativePlatformSecretWordFrontend.handler, RegistrationNativePlatformSecretWordFrontend.build,
    StateT.run, simulateQ_map, map_apply, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  cases equal
  have counted := RegistrationNativePlatformSecretWordInstallServerControl.body_count setup.source view failure allocation erased helper sign writer reservePeer
    role handle application before.1.server (before.1.environment.receipts, before.2) trace reached called

  have same (reply : RustM (Option (U64 × alloc.vec.Vec U8))) :
      present (RegistrationNativePlatformPublicFrontend.responseBytes reply) = present reply := by
    cases reply with
    | fail error | div => rfl
    | ok value => cases value <;> rfl
  simpa only [Prod.map_def,id_eq,same] using counted

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallServerTyped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallServerTyped.build_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallServerTyped.build_count
