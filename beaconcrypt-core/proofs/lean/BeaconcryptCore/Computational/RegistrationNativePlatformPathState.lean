-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformInitPendingJournal

/-! Actual corrected chronological source paths extend one shared cache and preserve their configured Server pin and its reached hash receipt. All native/platform states and failed callback outcomes remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPathState
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeTokenSource (Present Born)
open RegistrationNativeStageTrace (Call Path Executed)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform

variable [primitive : AdapterSealPrimitive.Operations]
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "impl" => RegistrationNativePlatformInitPendingJournal.callback coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationServerNativeSource.authenticate
  RegistrationServerNativeSource.agree RegistrationWorldAuthentication.begin RegistrationAuthenticationShared.begin

private theorem actual (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before after : Whole)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (supported : (reply, after) ∈ support ((impl query).run before)) :
    ((reply, after.1), after.2) ∈ support
      (((RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer erased helper writer query).run before.1).run before.2) := by
  simp only [RegistrationNativePlatformInitPendingJournal.callback, RegistrationNativePlatformPackedState.pack, StateT.run, support_map] at supported
  obtain ⟨⟨⟨value, native⟩, platform⟩, called, same⟩ := supported
  cases same
  exact called

/-- The cache grows along the literal chronological source path. -/
theorem cache {first last : Whole} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)}
    (reached : Path impl first calls last) : RegistrationNativeWorldCache.cache first.1 ≤ RegistrationNativeWorldCache.cache last.1 := by
  induction reached with
  | nil state => exact le_refl _
  | cons call called rest last following ih =>
    have sourceCalled := actual coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
      call.query call.before call.after call.reply called
    exact (RegistrationNativePlatformHandlerCache.handler coins setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer call.query call.before.1 call.before.2 ((call.reply, call.after.1), call.after.2) sourceCalled).trans ih

/-- The actual configured pin remains fixed across every source callback in the same path. -/
theorem pin {first last : Whole} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)}
    (reached : Path impl first calls last) : last.1.server.pin = first.1.server.pin := by
  induction reached with
  | nil state => rfl
  | cons call called rest last following ih =>
    have sourceCalled := actual coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
      call.query call.before call.after call.reply called
    exact ih.trans (RegistrationNativePlatformServerPinTrace.handler_pin coins setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer call.query call.before.1 call.before.2 ((call.reply, call.after.1), call.after.2) sourceCalled)

/-- The earlier actual cached-pin receipt survives the whole source path with its same literal configured pin. -/
theorem pinned {first last : Whole} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)}
    (reached : Path impl first calls last)
    (initial : RegistrationNativeServerPinRecompute.Cached first.1.server.pin (RegistrationNativeWorldCache.cache first.1)) :
    RegistrationNativeServerPinRecompute.Cached last.1.server.pin (RegistrationNativeWorldCache.cache last.1) := by
  rw [pin coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer reached]
  exact RegistrationNativeServerPinCached.extend _ _ _ initial
    (cache coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer reached)

end BeaconcryptCore.Computational.RegistrationNativePlatformPathState

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPathState.cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPathState.cache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPathState.pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPathState.pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPathState.pinned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPathState.pinned
