-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityBundleWanted
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationContradiction
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTuple
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedOwner
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover
import BeaconcryptCore.Computational.RegistrationNativeStageTraceCut
import BeaconcryptCore.Computational.RegistrationNativeRegistrationMarkCausal
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal
/-! A successful first-signing bundle is already a strict earlier publication of the accepted unsigned tuple. No before-callback target selection is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstUnpublished
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxKeyJournal (Whole drop owners)
open RegistrationNativeStageTrace (Call Path Executed)
open RegistrationNativeIdentityBundlePhase (Keeps Closed)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reserve
local notation "wire" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "actual" => RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint frontend


variable {V : Type}
local notation "FullState" => RegistrationNativeIdentityCensorEdOutgoingSource.Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source)

/-- The actual first one-time signing callback cannot publish successfully before this original Issued origin violation. -/
theorem success (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (before : Whole n KemSK Platform source) (empty : owners before=[])
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (before,[])))
    (attempt : RegistrationNativePlatformIdentityCtxCausalAttempt.Attempt setup.joint wire budget result.2.2.2 result.2.2.1)
    (issued : RegistrationNativePlatformIdentityCtxFiniteCover.Issued attempt)
    (leading trailing : List (Call TypedSpec (Whole n KemSK Platform source)))
    (index : Nat) (bytes : Pqxdh.Bytes) (first last : Whole n KemSK Platform source)
    (split : attempt.leading=leading++⟨.inr (.bundle index),first,.ok (some bytes),last⟩::trailing)
    (called : (.ok (some bytes),last) ∈ support ((actual (.inr (.bundle index))).run first))
    (unsigned : PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime ∉ RegistrationNativePlatformIdentityCtxSigningHistoryFrame.messages attempt.finalOwner.identity.handle first.2)
    (signed : PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime ∈ RegistrationNativePlatformIdentityCtxSigningHistoryFrame.messages attempt.finalOwner.identity.handle last.2) : False := by
  have role : RegistrationNativeIdentitySigningRole.oneTime (PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime)=true := by
    simp [RegistrationNativeIdentitySigningRole.oneTime,PqxdhEd25519EufCma.oneTimeMessage]
  have supported := RegistrationNativePlatformIdentityCtxKeyJournal.query_support setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.bundle index)) first (.ok (some bytes),last) called
  obtain ⟨owner,scalar,found,handle,wanted,tuple⟩ := RegistrationNativeIdentityBundleWanted.bundle setup checks representation created
    index reserve (drop first) (drop last) bytes supported attempt.finalOwner.identity.handle _ unsigned signed role
  exact RegistrationNativeIdentityCensorPublicationContradiction.earlier setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work budget before empty result reached attempt issued
      leading trailing ⟨.inr (.bundle index),first,.ok (some bytes),last⟩ split index bytes rfl owner found handle
        (setup.dh.publicKey scalar) wanted.symm tuple

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstUnpublished

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstUnpublished.success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstUnpublished.success
