-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRun
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountStop

/-! First-candidate stopping uses the actual corrected callback packed with its complete external platform state. The public trial observer ignores only the independently checked private accounting view. Every source allocation outcome and platform poststate remains in the free program. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountStop
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPackedState (pack)
variable {n : Nat} {KemSK Platform E Value ι : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

abbrev State (n : Nat) (KemSK Platform : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativeExperiment.State n KemSK source × Platform

def projection (before : State n KemSK Platform source) :=
  (RegistrationNativeMldsaMainView.project before.1, before.2)

theorem idempotent (before : State n KemSK Platform source) : projection (projection before) = projection before := by
  simp only [projection, RegistrationNativeMldsaMainView.idempotent]

def observe (publicKey : RegistrationNativeMldsaEuf.PublicKey) : RegistrationNativeMldsaStop.Observer
    (spec := RegistrationNativeRawAdapter.TypedSpec) (State := State n KemSK Platform source)
    (Candidate := RegistrationNativeMldsaEuf.Forgery) :=
  fun query before reply after => RegistrationNativeMldsaTrialObserver.observe source.verify publicKey query before.1 reply after.1

private theorem observe_view (publicKey : RegistrationNativeMldsaEuf.PublicKey) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before after : State n KemSK Platform source) (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) :
    observe publicKey query (projection before) reply (projection after) = observe publicKey query before reply after :=
  RegistrationNativeMldsaTrialObserverView.observe_count source.verify publicKey query before.1 after.1 reply

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

noncomputable def handler : QueryImpl RegistrationNativeRawAdapter.TypedSpec
    (StateT (State n KemSK Platform source) (OracleComp (RegistrationNativeMldsaProgram.Spec source))) :=
  fun query => pack (RegistrationNativePlatformMldsaProfile.handler setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer erased helper writer query)

/-- The literal complete corrected callback and full platform coordinate instantiate first-candidate stopping under both count equations. -/
theorem program (publicKey : RegistrationNativeMldsaEuf.PublicKey)
    (defaultReply : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) :
    RegistrationNativeMldsaCountRules.Correct (RegistrationNativeMldsaCountStop.view (projection (n := n) (source := source)))
      (simulateQ (RegistrationNativeMldsaStop.freeze
        (handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer)
        (observe publicKey) defaultReply) work) :=
  RegistrationNativeMldsaCountStop.program _ idempotent (observe publicKey) (observe_view publicKey)
    _ defaultReply (RegistrationNativePlatformMldsaCountRun.handler setup checks wire route representation created credential
      view failure allocation reserveRegistration reservePeer erased helper writer) work
end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountStop

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountStop.idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountStop.idempotent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountStop.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountStop.program
