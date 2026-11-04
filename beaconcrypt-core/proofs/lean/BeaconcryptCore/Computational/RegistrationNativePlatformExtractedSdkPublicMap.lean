-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
/-! A pure public reply adapter changes neither the SDK execution nor its private continuation state. In particular, converting returned SDK vectors to original public bytes retains the exact source call and all platform effects. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublicMap
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
variable {N A B : Type} {Private : N →Type} {model : ProbComp (A×N)}
def map (publicReply : A →B) (call : TotalStep Private model) :
    TotalStep Private (Prod.map publicReply id <$>model) := {
  step:={
    Packet:=call.step.Packet
    sample:=call.step.sample
    sourceType:=call.step.sourceType
    sourceReply:=call.step.sourceReply
    sourceState:=call.step.sourceState
    sourceCall:=call.step.sourceCall
    source_exact:=call.step.source_exact
    native:=fun packet=>(publicReply (call.step.native packet).1,(call.step.native packet).2)
    native_exact:=by
      have same:=congrArg (fun action=>Prod.map publicReply id <$>action) call.step.native_exact
      simpa only [Functor.map_map,Prod.map,id_eq] using same
    store:=call.step.store}
  observe:=fun returned=>publicReply (call.observe returned)
  normal:=call.normal
  reply:=fun packet supported returned actual=>congrArg publicReply (call.reply packet supported returned actual) }
theorem source (publicReply : A →B) (call : TotalStep Private model) :
    (map publicReply call).step.sourceCall=call.step.sourceCall := rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublicMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublicMap.map' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublicMap.map

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublicMap.source' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublicMap.source
