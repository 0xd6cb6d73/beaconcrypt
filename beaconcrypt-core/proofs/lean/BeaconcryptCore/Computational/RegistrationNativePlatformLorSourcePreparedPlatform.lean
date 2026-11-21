-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTraceCore
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePlatform
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedCore
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedControl
/-! The actual platform extension of the traced Word interpreter derives individual preparation echo and chronological recording facts while retaining every reply and state coordinate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPlatform
open RegistrationNativeSecretWordInterface (Spec LocalSpec prepare liftLocal)
open RegistrationNativeSecretWordMessage (Message ServerReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativePlatformLorSourcePreparedTraceCore (Prepared prepare_recorded)
variable {n : Nat} {KemSK Platform Private Reader E : Type}
variable (implementation : QueryImpl (Spec n KemSK) (StateT Private ProbComp)) (input : Message → Option Key)
local notation "actual" => RegistrationNativePlatformLorStatefulSupport.trace implementation
local notation "extended" => RegistrationNativePlatformLorSourcePlatform.extend (Platform := Platform) actual
/-- The actual platform extension retains the same preparation event in the same private trace. -/
theorem recorded (message : Message) (before : Platform × (RegistrationNativeSecretWordFrontendTrace.State × Private))
    (result : Option Message × (Platform × (RegistrationNativeSecretWordFrontendTrace.State × Private)))
    (supported : result∈support ((extended (.inl (.inl message))).run before)) :
    Prepared message result.2.2.1 := by
  simp only [RegistrationNativePlatformLorSourcePlatform.extend,StateT.run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  have prepared := prepare_recorded implementation message before.2 reached called
  have traceEq := congrArg (fun value=>value.2.2.1) equal
  change reached.2.1=result.2.2.1 at traceEq
  rw [←traceEq]
  exact prepared

variable (echo : ∀ message before result,result∈support ((implementation (.inl (.inl message))).run before) →
  result.1=(input message).map (fun _=>message))
include echo in
/-- Preparation echo is derived through the actual trace and platform interpreters without altering any reply. -/
theorem echo_extended (message : Message) (before : Platform × (RegistrationNativeSecretWordFrontendTrace.State × Private))
    (result : Option Message × (Platform × (RegistrationNativeSecretWordFrontendTrace.State × Private)))
    (supported : result∈support ((extended (.inl (.inl message))).run before)) :
    result.1=(input message).map (fun _=>message) := by
  simp only [RegistrationNativePlatformLorSourcePlatform.extend,StateT.run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  have source := RegistrationNativePlatformLorSourceKemTrace.query_support implementation (.inl (.inl message)) before.2 reached called
  have value := echo message before.2.2 (reached.1,reached.2.2) source
  have replyEq := congrArg Prod.fst equal
  change reached.1=result.1 at replyEq
  rw [←replyEq]
  exact value
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPlatform
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPlatform.recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPlatform.recorded
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPlatform.echo_extended' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPlatform.echo_extended
