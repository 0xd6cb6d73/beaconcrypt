-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationContradiction
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTuple
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedOwner
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover
import BeaconcryptCore.Computational.RegistrationNativeStageTraceCut
import BeaconcryptCore.Computational.RegistrationNativeRegistrationMarkCausal
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal
/-! Actual canonical active publication at a projected original callback contradicts the original strict earlier-publication failure through concrete unsigned-tuple readback. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveUnpublished
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
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
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

/-- An active successful canonical source publication strictly before the original Issued acceptance is impossible on that same original projected callback. -/
theorem active (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (before : Whole n KemSK Platform source) (empty : owners before=[])
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (before,[])))
    (attempt : RegistrationNativePlatformIdentityCtxCausalAttempt.Attempt setup.joint wire budget result.2.2.2 result.2.2.1)
    (issued : RegistrationNativePlatformIdentityCtxFiniteCover.Issued attempt)
    (leading trailing : List (Call TypedSpec (Whole n KemSK Platform source)))
    (call : Call TypedSpec (Whole n KemSK Platform source)) (split : attempt.leading=leading++call::trailing)
    (index : Nat) (bytes : Pqxdh.Bytes)
    (marked : RegistrationNativeRawRegistrationJournal.typedMark call.query call.reply=some (.bundle index (some bytes)))
    (position : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (current after : FullState)
    (same : RegistrationNativeIdentityCensorActualHashSource.project current=RegistrationNativeIdentityCensorNormalizedJournal.project placeholder call.before)
    (seed : PqxdhJointIdentity.IdentitySeed)
    (held : current.1.2.target=some (PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime))
    (sourceTarget : current.2.target=some (PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime))
    (found : current.2.pool.seeds[attempt.finalOwner.identity.handle]?=some seed)
    (supported : (.ok (some bytes),after) ∈ support (RegistrationNativeIdentityCensorAdaptivePostselection.call setup checks wire route representation created credential view
      failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve attempt.finalOwner.identity.handle position placeholder false (.inr (.bundle index)) current))
    (active : after.1.2.active=true) : False := by
  have role : RegistrationNativeIdentitySigningRole.oneTime (PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime)=true := by
    simp [RegistrationNativeIdentitySigningRole.oneTime,PqxdhEd25519EufCma.oneTimeMessage]
  obtain ⟨owner,scalar,ownerAt,handle,oneTime,tuple⟩ := RegistrationNativeIdentityCensorActiveTuple.marked setup checks representation created
    attempt.finalOwner.identity.handle index placeholder reserve wire route credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper
      position _ role current after seed held sourceTarget found bytes supported active
  obtain ⟨original,originalAt,keyEq⟩ := RegistrationNativeIdentityCensorNormalizedOwner.captured placeholder call.before current same index owner ownerAt
  have originalHandle : original.identity.handle=attempt.finalOwner.identity.handle :=
    (congrArg (fun key=>key.1.handle) keyEq).trans handle
  have originalTuple : (PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec wire) bytes).bind PqxdhDeploymentPublishedTuple.candidateTuple=
      some ⟨PqxdhPhase2InputBytes.word original.prekeyPublic,setup.dh.publicKey scalar,original.kemPublic⟩ := by
    have preEq : original.prekeyPublic=owner.prekeyPublic := congrArg (fun key=>key.2.1) keyEq
    have pqEq : original.kemPublic=owner.kemPublic := congrArg (fun key=>key.2.2) keyEq
    rw [preEq,pqEq]
    exact tuple
  exact RegistrationNativeIdentityCensorPublicationContradiction.earlier setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work budget before empty result reached attempt issued
      leading trailing call split index bytes marked original originalAt originalHandle (setup.dh.publicKey scalar) oneTime.symm originalTuple

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveUnpublished

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveUnpublished.active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveUnpublished.active
