-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicWrapperChildren
import BeaconcryptCore.Refinement.AdapterPublicBundleBody
import BeaconcryptCore.Computational.RegistrationNativePlatformCutLift
/-! Actual extracted source Init and response writer children commute with the private signing-cut lift. Every reached trusted writer primitive retains complete native and platform state; the cut is unchanged. No whole writer correspondence premise is assumed. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicWrapperCutChildren
open BeaconcryptCore.Computational
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformCutJournal (State)
open RegistrationNativePlatformCutErasure (liftWorld)
variable [ed : AdapterInitEdPrimitive.Operations]
variable {S E : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

def lifted (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT S m)) :
    QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT (State S) m) :=
  fun query => liftWorld (writer query)

theorem init (authentication : QueryImpl AdapterInitAuthenticationRequestMonad.Spec (StateT (State S) m))
    (recording : QueryImpl AdapterRecordRequestMonad.Spec (StateT (State S) m))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT S m))
    (packet : beaconcrypt_parse.transport.initkex) :
    ((AdapterPublicWrapperChildren.children authentication recording (lifted writer)).encodeInit packet).run =
      liftWorld (simulateQ writer (AdapterRegistrationWriterRequestExtraction.encodeInit
        (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E) packet).run) := by
  rw [AdapterPublicWrapperChildren.init_writer_run]
  exact RegistrationNativePlatformCutLift.program writer _

theorem response (authentication : QueryImpl AdapterInitAuthenticationRequestMonad.Spec (StateT (State S) m))
    (recording : QueryImpl AdapterRecordRequestMonad.Spec (StateT (State S) m))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT S m))
    (packet : beaconcrypt_parse.transport.kexresponse) :
    ((AdapterPublicWrapperChildren.children authentication recording (lifted writer)).encodeResponse packet).run =
      liftWorld (simulateQ writer (AdapterRegistrationWriterRequestExtraction.encodeResponse
        (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E) packet).run) := by
  rw [AdapterPublicWrapperChildren.response_writer_run]
  exact RegistrationNativePlatformCutLift.program writer _
end BeaconcryptCore.Refinement.AdapterPublicWrapperCutChildren
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperCutChildren.init' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperCutChildren.init

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperCutChildren.response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperCutChildren.response
