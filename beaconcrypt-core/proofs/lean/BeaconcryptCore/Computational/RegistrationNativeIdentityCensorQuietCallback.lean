-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveUnpublished
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
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietCallback
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

/-- Every actual selected canonical callback before the original issued acceptance survives the public publication stop. -/
theorem quiet (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (before : Whole n KemSK Platform source) (empty : owners before=[])
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (before,[])))
    (attempt : RegistrationNativePlatformIdentityCtxCausalAttempt.Attempt setup.joint wire budget result.2.2.2 result.2.2.1)
    (issued : RegistrationNativePlatformIdentityCtxFiniteCover.Issued attempt)
    (leading trailing : List (Call TypedSpec (Whole n KemSK Platform source)))
    (query : TypedSpec.Domain) (reply : TypedSpec.Range query) (first last : Whole n KemSK Platform source)
    (split : attempt.leading=leading++⟨query,first,reply,last⟩::trailing)
    (position : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (current after : FullState)
    (same : RegistrationNativeIdentityCensorActualHashSource.project current=RegistrationNativeIdentityCensorNormalizedJournal.project placeholder first)
    (seed : PqxdhJointIdentity.IdentitySeed)
    (selected : RegistrationNativeIdentityCensorAdaptivePostselection.Selected attempt.finalOwner.identity.handle
      (PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime) seed current)
    (supported : (reply,after) ∈ support (RegistrationNativeIdentityCensorAdaptivePostselection.call setup checks wire route representation created credential view
      failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve attempt.finalOwner.identity.handle position placeholder false query current)) :
    RegistrationNativeIdentityCensorAdaptivePostselection.published query reply after=false := by
  cases query with
  | inl coin => rfl
  | inr command => cases command with
    | bundle index =>
        cases reply with
        | fail error | div => simp [RegistrationNativeIdentityCensorAdaptivePostselection.published,RegistrationNativeRawAdapter.resultOption]
        | ok optional => cases optional with
          | none => simp [RegistrationNativeIdentityCensorAdaptivePostselection.published,RegistrationNativeRawAdapter.resultOption]
          | some bytes =>
              cases active : after.1.2.active with
              | false => simp [RegistrationNativeIdentityCensorAdaptivePostselection.published,active]
              | true => exact False.elim (RegistrationNativeIdentityCensorActiveUnpublished.active setup checks route representation created credential view failure allocation
                  reserveRegistration reservePeer reserveFrame erased helper reserve serverKeyId bounds mode work budget before empty result reached attempt issued
                    leading trailing ⟨.inr (.bundle index),first,.ok (some bytes),last⟩ split index bytes rfl position placeholder current after same
                      seed selected.1 selected.2.1 selected.2.2 supported active)
    | _ => rfl
end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietCallback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietCallback.quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietCallback.quiet
