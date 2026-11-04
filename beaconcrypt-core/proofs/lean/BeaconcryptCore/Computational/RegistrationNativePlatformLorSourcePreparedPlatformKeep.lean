-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTraceCore
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePlatform
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedCore
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedControl
/-! Every actual platform-extended source query retains preparations already present in the same private chronological trace. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPlatformKeep
open RegistrationNativeSecretWordInterface (Spec LocalSpec prepare liftLocal)
open RegistrationNativeSecretWordMessage (Message ServerReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativePlatformLorSourcePreparedTraceCore (Prepared prepare_recorded)
variable {n : Nat} {KemSK Platform Private Reader E : Type}
variable (implementation : QueryImpl (Spec n KemSK) (StateT Private ProbComp)) (input : Message → Option Key)
local notation "actual" => RegistrationNativePlatformLorStatefulSupport.trace implementation
local notation "extended" => RegistrationNativePlatformLorSourcePlatform.extend (Platform := Platform) actual
/-- The actual extended source query preserves every preparation that was already present before the callback. -/
theorem keeps_extended (message : Message) (query : (Spec n KemSK).Domain)
    (before : Platform × (RegistrationNativeSecretWordFrontendTrace.State × Private))
    (result : (Spec n KemSK).Range query × (Platform × (RegistrationNativeSecretWordFrontendTrace.State × Private)))
    (supported : result∈support ((extended query).run before)) (prepared : Prepared message before.2.1) :
    Prepared message result.2.2.1 := by
  simp only [RegistrationNativePlatformLorSourcePlatform.extend,StateT.run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  obtain ⟨added,appended⟩ := RegistrationNativePlatformLorSourcePreparedTraceCore.query_suffix implementation query before.2 reached called
  have traceEq := congrArg (fun value=>value.2.2.1.events) equal
  change reached.2.1.events=result.2.2.1.events at traceEq
  dsimp only [Prepared] at prepared ⊢
  rw [←traceEq,appended]
  exact List.mem_append_left _ prepared
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPlatformKeep
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPlatformKeep.keeps_extended' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPlatformKeep.keeps_extended
