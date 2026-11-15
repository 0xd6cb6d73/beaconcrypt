-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleTypedKeyCapture
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstBundleCut

/-! First signing at a public bundle preserves the captured owner's fixed prekey/PQ policy in the final same-handle owner. The source callback and the immutable-key relation are both derived from the same complete full-compiler run. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstBundleFixed
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxKeyJournal (Whole drop owners)
open RegistrationNativeStageTrace (Call Path Executed)
open RegistrationNativePlatformIdentityCtxFirstBundleCut (messages)
variable {V : Type}
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "actual" => RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint frontend

/-- A newly signed source message in any actual bundle callback obeys the final same-handle owner's exact fixed-key policy. -/
theorem full_new_fixed (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (before : Whole n KemSK Platform source) (empty : owners before = [])
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (before, [])))
    (call : Call TypedSpec (Whole n KemSK Platform source)) (member : call ∈ result.2.2.2)
    (called : Executed actual call) (index : Nat) (queryEq : call.query = .inr (.bundle index))
    (identity : Nat) (message : Pqxdh.Bytes) (fresh : message ∉ messages identity call.before)
    (signed : message ∈ messages identity call.after)
    (finalOwner : RegistrationNativeIdentityFrontend.Owner source) (finalMember : finalOwner ∈ owners result.2.2.1)
    (sameHandle : finalOwner.identity.handle = identity) :
    RegistrationNativeEdKeyPolicy.Allowed (PqxdhPhase2InputBytes.word finalOwner.prekeyPublic) finalOwner.kemPublic message := by
  rcases call with ⟨query, leading, reply, trailing⟩
  dsimp only at queryEq
  subst query
  have supported := RegistrationNativePlatformIdentityCtxKeyJournal.query_support setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.bundle index)) leading (reply, trailing) called
  obtain ⟨captured, found, capturedHandle, allowed⟩ := RegistrationNativePlatformIdentityCtxBundleTypedKeyCapture.typed_new
    setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    index (drop leading) (reply, drop trailing) supported identity message fresh signed
  have immutable := RegistrationNativePlatformIdentityCtxKeyJournal.full_same_handle setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before empty result reached
    ⟨.inr (.bundle index), leading, reply, trailing⟩ member index captured found finalOwner finalMember (sameHandle.trans capturedHandle.symm)
  have preEq := congrArg (fun tuple => tuple.2.1) immutable
  have pqEq := congrArg (fun tuple => tuple.2.2) immutable
  change finalOwner.prekeyPublic = captured.prekeyPublic at preEq
  change finalOwner.kemPublic = captured.kemPublic at pqEq
  rw [preEq, pqEq]
  exact allowed

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstBundleFixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstBundleFixed.full_new_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstBundleFixed.full_new_fixed
