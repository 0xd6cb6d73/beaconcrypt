-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedInitialized
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedStartup
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedConditional
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedChosenGame
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial
/-! Actual initialized unissued-field probability is bounded by the finite sum of executable ordinary joint weak-EUF reductions. Every independent startup and family draw is inside each reduction; no conditional security bound is a caller input. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedBound
open RegistrationNativeIdentityTemplateProtocol (PublicSpec)
variable {Value : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I}
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (CoreModels.core.result.Result Unit E)) (erased : beaconcrypt_core.commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

variable (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (previous : Platform)


local notation "actual(" budget ")" => RegistrationNativeIdentityUnissuedInitialized.game (n := n) setup checks wire route representation view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit identityIndex serverKeyId bounds mode adversary previous budget

/-- Genuine startup averages the actual conditional public-cut bound into one ordinary executable reduction for each public identity/accept/field index. -/
theorem at_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication,RegistrationNativeInterface.Respects budget (adversary publication))
    (identity : Fin (budget.create+1)) (accept : Fin budget.accept) (tag : Fin 3) (fallback : PqxdhJointIdentity.Forgery) :
    Pr{let result ← actual(budget)}[RegistrationNativeIdentityUnissuedInitialized.At setup source budget identity accept tag result] ≤
      PqxdhJointIdentity.advantage setup.joint
        (RegistrationNativeIdentityUnissuedNativeClient.reduction (n := n) setup checks wire route representation view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit identityIndex serverKeyId bounds mode adversary previous identity accept.val tag fallback) := by
  rw [←RegistrationNativeIdentityUnissuedStartup.probability_eq]
  unfold RegistrationNativeIdentityUnissuedInitialized.game RegistrationNativeIdentityUnissuedStartup.completeGame
  apply prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _
  intro initialized _reached
  cases initialized with
  | some initial =>
      simp only [prEvent_map]
      exact RegistrationNativeIdentityUnissuedConditional.bound setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source bounds mode adversary previous initial budget (bounded initial.public) identity accept.val tag fallback
  | none => simp [RegistrationNativeIdentityUnissuedInitialized.At]

/-- The same initialized original event pays the explicit finite identity/accept/field reduction family once. -/
theorem bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication,RegistrationNativeInterface.Respects budget (adversary publication))
    (fallback : PqxdhJointIdentity.Forgery) :
    Pr{let result ← actual(budget)}[RegistrationNativeIdentityUnissuedInitialized.Any setup source budget result] ≤
      RegistrationNativeIdentityUnissuedInitialized.loss (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source ensureInit identityIndex serverKeyId bounds mode adversary previous budget fallback := by
  apply (RegistrationNativeIdentityUnissuedInitialized.finite_union setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds mode adversary previous budget).trans
  exact Finset.sum_le_sum (fun identity _ => Finset.sum_le_sum (fun accept _ => Finset.sum_le_sum (fun tag _ =>
    at_bound setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded identity accept tag fallback)))

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedBound.at_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedBound.at_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedBound.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedBound.bound
