-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
/-! Public result conversion keeps the same actual source call, supported receipt and returned-object continuation. It never regenerates a packet or changes a native/private poststate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReply
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
variable {N A B : Type} {Private : N →Type} {model : ProbComp (A ×N)}

noncomputable def map (observe : A →B) (call : TotalStep Private model) :
    TotalStep Private (Prod.map observe id <$>model) := {
  step:={
    Packet:=call.step.Packet
    sample:=call.step.sample
    sourceType:=call.step.sourceType
    sourceReply:=call.step.sourceReply
    sourceState:=call.step.sourceState
    sourceCall:=call.step.sourceCall
    source_exact:=call.step.source_exact
    native:=fun packet=>Prod.map observe id (call.step.native packet)
    native_exact:=by
      have equation:=congrArg (fun work=>Prod.map observe id <$>work) call.step.native_exact
      simpa only [Functor.map_map,Function.comp_def] using equation
    store:=call.step.store }
  observe:=observe ∘call.observe
  normal:=call.normal
  reply:=by
    intro packet supported returned actual
    exact congrArg observe (call.reply packet supported returned actual) }

theorem source (observe : A →B) (call : TotalStep Private model) :
    (map observe call).step.sourceCall=call.step.sourceCall := rfl

theorem store (observe : A →B) (call : TotalStep Private model)
    (packet : {value //value∈support call.step.sample}) :
    RegistrationNativePlatformExtractedSdkPublic.store (map observe call) packet=
      RegistrationNativePlatformExtractedSdkPublic.store call packet := rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReply
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReply.map' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReply.map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReply.source' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReply.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReply.store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReply.store
