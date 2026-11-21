-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReceiptFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLowModel
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSigningQuiet
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n :Nat} {I KemSK P E R Error :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitives :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto :CryptoOperations (RustT ProbComp)]
variable [originalLocal :LocalOperations (RustT (StateT P ProbComp))]
variable [originalContainers :ContainerOperations (RustT (StateT P ProbComp))]
variable {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
variable (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)
variable {Value :Type}
variable (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential source)
local notation "Private"=>RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential
local notation "physical"=>RegistrationNativePlatformPublicAdapterAuditLowModel.physical (n:=n) configuration created credential

local notation "typed"=>RegistrationNativePlatformPublicAdapterAuditModel.typed configuration created credential
local notation "failure"=>RegistrationNativePlatformPublicAdapterAuditModel.failure credential

def Quiet :RegistrationNativeInterface.Spec.Domain→Prop
  | .inr (.bundle _) | .inr (.build _ _)=>False
  | _=>True

omit material platform ed primitives [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  [FrameDispatchFallback.Operations] originalGenerators originalCrypto originalLocal originalContainers in
private theorem form_quiet (wire :RegistrationNativeWire.Wire) (query :RegistrationNativeInterface.Spec.Domain) (allowed :Quiet query)
    (chosen :RegistrationNativeRawAdapter.TypedSpec.Domain) (observe :RegistrationNativeRawAdapter.TypedSpec.Range chosen→RegistrationNativeInterface.Spec.Range query)
    (form :RegistrationNativePlatformPublicAdapterTypedAuditRaw.form wire query=.query chosen observe) :
    RegistrationNativePlatformPublicAdapterReceiptFrame.Quiet chosen :=by
  cases query with
  | inl coin=>cases form;trivial
  | inr command=>cases command with
    | bundle _ | build _ _=>exact allowed.elim
    | create edPin mlPin keyId=>
      cases parsed:PqxdhDeploymentInterface.parsePin edPin <;>cases parsedMl:RegistrationNativeWire.parseMldsaPin mlPin <;>
        simp only [RegistrationNativePlatformPublicAdapterTypedAuditRaw.form,parsed,parsedMl,reduceCtorEq] at form
      cases form
      trivial
    | accept bytes=>
      cases parsed:RegistrationNativeWire.readInit wire bytes <;>
        simp only [RegistrationNativePlatformPublicAdapterTypedAuditRaw.form,parsed,reduceCtorEq] at form
      cases form
      trivial
    | _=>cases form;trivial

omit [PublicWrapperPlatform.CryptoOperations] in
theorem raw (query :RegistrationNativeInterface.Spec.Domain) (allowed :Quiet query)
    (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source)
    (result :RegistrationNativeInterface.Spec.Range query×RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source)
    (supported :result∈support ((RegistrationNativePlatformPublicAdapterAuditModel.raw configuration created credential query).run before)) :
    result.2.1.1.server.world.world.2=before.1.1.server.world.world.2 :=by
  unfold RegistrationNativePlatformPublicAdapterAuditModel.raw at supported
  rw [RegistrationNativePlatformPublicAdapterTypedAuditRaw.query] at supported
  cases form:RegistrationNativePlatformPublicAdapterTypedAuditRaw.form RegistrationNativeConcreteCodec.wire query with
  | pure value=>
    simp only [form,support_pure,Set.mem_singleton_iff] at supported
    cases supported
    rfl
  | query chosen observe=>
    simp only [form,support_map] at supported
    obtain ⟨middle,called,same⟩:=supported
    simp only [RegistrationNativePlatformPublicAdapterTypedAudit.handler,StateT.run,support_map] at called
    obtain ⟨actual,called,retained⟩:=called
    subst middle
    subst result
    exact RegistrationNativePlatformPublicAdapterReceiptFrame.typed configuration created credential chosen
      (form_quiet RegistrationNativeConcreteCodec.wire query allowed chosen observe form) before.1 actual called

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSigningQuiet

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSigningQuiet.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSigningQuiet.raw
