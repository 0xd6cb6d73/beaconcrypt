-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedBound
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalMarginal
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedStartup
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedConditional
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedChosenGame
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial
/-! The genuine original initialized source Unissued event is bounded by an explicit finite family of executable ordinary joint weak-EUF reductions. Actual startup failures, warm cache, same-run source histories and persistent platform outcomes are retained throughout. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalInitialized
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



noncomputable def game : ProbComp (Option (RegistrationNativeIdentityUnissuedOriginalCore.Original n KemSK Platform Value source)) := do
  let initialized ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId
  match initialized with
  | none => pure none
  | some initial => some <$> (RegistrationNativeIdentityUnissuedOriginalCore.original setup checks wire route representation view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer source bounds mode adversary previous initial)

def Unissued (budget : PqxdhDeploymentInterface.Budget)
    (result : Option (RegistrationNativeIdentityUnissuedOriginalCore.Original n KemSK Platform Value source)) : Prop :=
  result.elim False (RegistrationNativeIdentityUnissuedOriginalMarginal.Unissued setup wire source budget)

/-- Actual independent startup averages the original complete source journal's Unissued cover into the same eager family event. -/
theorem event_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication,RegistrationNativeInterface.Respects budget (adversary publication)) :
    Pr{let result ← (game (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous)}[Unissued setup wire source budget result] ≤
    Pr{let result ← (RegistrationNativeIdentityUnissuedInitialized.game (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous budget)}[RegistrationNativeIdentityUnissuedInitialized.Any setup source budget result] := by
  unfold game RegistrationNativeIdentityUnissuedInitialized.game
  apply prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _
  intro initialized _reached
  cases initialized with
  | none => simp [Unissued,RegistrationNativeIdentityUnissuedInitialized.Any,RegistrationNativeIdentityUnissuedInitialized.At]
  | some initial =>
      simp only [prEvent_map]
      exact RegistrationNativeIdentityUnissuedOriginalMarginal.fixed_bound setup checks wire route representation view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer source bounds mode adversary previous initial budget (bounded initial.public)

/-- The original initialized Unissued event pays only the explicit ordinary reduction family; no source, per-target security or capacity conclusion is supplied by callers. -/
theorem bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication,RegistrationNativeInterface.Respects budget (adversary publication))
    (fallback : PqxdhJointIdentity.Forgery) :
    Pr{let result ← (game (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous)}[Unissued setup wire source budget result] ≤
    RegistrationNativeIdentityUnissuedInitialized.loss (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous budget fallback :=
  (event_bound setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded).trans
      (RegistrationNativeIdentityUnissuedBound.bound setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded fallback)

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalInitialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalInitialized.event_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalInitialized.event_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalInitialized.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedOriginalInitialized.bound
