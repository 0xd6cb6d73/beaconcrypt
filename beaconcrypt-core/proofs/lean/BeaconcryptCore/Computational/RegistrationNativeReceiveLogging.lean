-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeExtractedReceive

/-! Receive primitive requests contain no writer call. The original production-frame logger therefore retains its literal incoming frame list through every receive callback, including optional hash/AEAD failure. This is a structural request-program identity, with no primitive or codec security assumption. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.RegistrationNativeReceiveLogging

/-- Every receive-native query is forwarded without modifying the original frame log. -/
theorem receive_lift_log {Value : Type} (work : OracleComp RawCtxSourceOpen.NativeSpec Value)
    (frames : List PqxdhDeploymentNative.Frame) :
    (simulateQ PqxdhDeploymentNative.frameLog
      (simulateQ RawCtxMixedOwner.receiveLift work)).run frames =
      (fun value => (value, frames)) <$> simulateQ RawCtxMixedOwner.receiveLift work := by
  induction work using OracleComp.inductionOn generalizing frames with
  | pure value => rfl
  | query_bind query next ih =>
      rcases query with request | (input | input)
      all_goals simp only [simulateQ_bind, simulateQ_spec_query, RawCtxMixedOwner.receiveLift,
        PqxdhDeploymentNative.frameLog, StateT.run_bind, StateT.run_lift,
        map_bind, ih]
      all_goals rfl

/-- Expanding the actual owner opening interface also adds no writer frame. -/
theorem logged_receive {Value : Type} (work : OracleComp RawCtxWholeOwner.PrimitiveSpec Value) :
    PqxdhDeploymentNative.logged (simulateQ RawCtxMixedOwner.receiveAdapter work) =
      (fun value => (value, [])) <$> simulateQ RawCtxMixedOwner.receiveAdapter work := by
  simpa only [PqxdhDeploymentNative.logged, RawCtxMixedOwner.receiveAdapter,
    QueryImpl.simulateQ_compose] using
    receive_lift_log (simulateQ RawCtxSourceOpen.nativeAdapter work) []

end BeaconcryptCore.Computational.RegistrationNativeReceiveLogging

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeReceiveLogging.receive_lift_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeReceiveLogging.receive_lift_log

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeReceiveLogging.logged_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeReceiveLogging.logged_receive
