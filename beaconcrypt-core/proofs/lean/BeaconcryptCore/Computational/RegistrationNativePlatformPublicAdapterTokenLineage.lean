-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDispatch
import BeaconcryptCore.Refinement.AdapterPublicServerAcceptanceParsed
/-! A retained one-use token carries the actual successful source identity parse receipt into a later response build. Arbitrary fixed-width keys or caller-created tokens need not parse. The invariant is initialized from an empty source token store and updated at the actual source acceptance. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTokenLineage
open BeaconcryptCore.Refinement
variable [ed : AdapterInitEdPrimitive.Operations]

def Parsed (tokens : Nat →Option beaconcrypt_public_wrapper.server.RegistrationOutput) : Prop :=
  ∀index token,tokens index=some token →AdapterPublicServerToken.ParsedToken token

theorem empty : Parsed (fun _=>none) := by
  intro index token impossible
  cases impossible

theorem erase (tokens : Nat →Option beaconcrypt_public_wrapper.server.RegistrationOutput)
    (before : Parsed tokens) (handle : Nat) : Parsed (Function.update tokens handle none) := by
  intro index token stored
  by_cases same:index=handle
  · subst index
    simp only [Function.update_self,reduceCtorEq] at stored
  · rw [Function.update_of_ne same] at stored
    exact before index token stored

theorem insert (tokens : Nat →Option beaconcrypt_public_wrapper.server.RegistrationOutput)
    (before : Parsed tokens) (handle : Nat) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (parsed : AdapterPublicServerToken.ParsedToken token) : Parsed (Function.update tokens handle (some token)) := by
  intro index current stored
  by_cases same:index=handle
  · subst index
    rw [Function.update_self,Option.some.injEq] at stored
    cases stored
    exact parsed
  · rw [Function.update_of_ne same] at stored
    exact before index current stored

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable {n : Nat} {I KemSK Platform R : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK)
variable (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)

structure Carrier (current : RegistrationNativeExperiment.State n KemSK source ×Platform) where
  base : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current
  parsed : Parsed base.base.objects.tokens

noncomputable def frame (current after : RegistrationNativeExperiment.State n KemSK source ×Platform)
    (before : Carrier (R:=R) setup view views created credential current)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential after)
    (same : objects.base.objects.tokens=before.base.base.objects.tokens) : Carrier (R:=R) setup view views created credential after :=
  ⟨objects,by rw [same]; exact before.parsed⟩

omit material platform ed in
private theorem cast_cancel {A B : Type} (same : A=B) (value : B) : same.mp (same.mpr value)=value := by
  cases same
  rfl

noncomputable def of_strong {Reply : Type}
    {model : ProbComp (Reply ×(RegistrationNativeExperiment.State n KemSK source ×Platform))}
    (call : RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential) model)
    (parsed : ∀packet : {value //value∈support call.step.sample},
      Parsed (RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects.tokens) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (Carrier (R:=R) setup view views created credential) model := {
  step:={
    Packet:=call.step.Packet
    sample:=call.step.sample
    sourceType:=call.step.sourceType
    sourceReply:=call.step.sourceReply
    sourceState:=call.step.sourceState
    sourceCall:=call.step.sourceCall
    source_exact:=call.step.source_exact
    native:=call.step.native
    native_exact:=call.step.native_exact
    store:=fun packet supported=>by
      have marked : call.step.sourceReply packet=.ok (RegistrationNativePlatformExtractedSdkPublic.returned call ⟨packet,supported⟩):=
        RegistrationNativePlatformExtractedSdkPublic.returned_exact call ⟨packet,supported⟩
      rw [marked]
      exact ⟨RegistrationNativePlatformExtractedSdkPublic.store call ⟨packet,supported⟩,parsed ⟨packet,supported⟩⟩ }
  observe:=call.observe
  normal:=call.normal
  reply:=call.reply }

theorem of_strong_base {Reply : Type}
    {model : ProbComp (Reply ×(RegistrationNativeExperiment.State n KemSK source ×Platform))}
    (call : RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential) model)
    (parsed : ∀packet : {value //value∈support call.step.sample},
      Parsed (RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects.tokens)
    (packet : {value //value∈support call.step.sample}) :
    (RegistrationNativePlatformExtractedSdkPublic.store (of_strong setup view views created credential call parsed) packet).base=
      RegistrationNativePlatformExtractedSdkPublic.store call packet := by
  simp only [RegistrationNativePlatformExtractedSdkPublic.store,of_strong,cast_cancel]

variable (current : RegistrationNativeExperiment.State n KemSK source ×Platform)
variable (before : Carrier (R:=R) setup view views created credential current)

theorem token (handle : Nat) (stored : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (present : before.base.base.objects.tokens handle=some stored) : AdapterPublicServerToken.ParsedToken stored :=
  before.parsed handle stored present

noncomputable def move (handle : Nat) : Carrier (R:=R) setup view views created credential
    (AdapterPublicServerBuildOwnership.moved handle current.1,current.2) where
  base:=RegistrationNativePlatformPublicAdapterBuildDispatch.move setup view views created credential current before.base handle
  parsed:=erase before.base.base.objects.tokens before.parsed handle

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTokenLineage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTokenLineage.empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTokenLineage.empty
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTokenLineage.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTokenLineage.erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTokenLineage.insert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTokenLineage.insert
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTokenLineage.token' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTokenLineage.token
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTokenLineage.move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTokenLineage.move
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTokenLineage.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTokenLineage.frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTokenLineage.of_strong' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTokenLineage.of_strong
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTokenLineage.of_strong_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTokenLineage.of_strong_base
