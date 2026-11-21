-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCommon
/-! The unchanged-log packet construction transports a concrete ordinary operation without introducing any source stages. Its source proof consumes the already discharged actual call equality and carries the same P alongside the original log. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedNoStage
open BeaconcryptCore.Refinement
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
open RegistrationNativePlatformPublicAdapterSourceEvents (Log)
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations]
variable {n :Nat} {KemSK R P N :Type}
variable (Private :N→Type) (model :QueryImpl RegistrationNativePlatformPublicAdapterLowSpec.Spec (StateT N ProbComp))
variable (calls :∀query current,Private current→TotalStep Private ((model query).run current))
variable (basePhysical :∀current,Private current→RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P)

noncomputable def augment (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain)
    (before :RegistrationNativePlatformExtractedSdkPublic.State Private) (prior :Log n KemSK R P) :=
  RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged (calls query before.1 before.2) prior

theorem joint (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain)
    (plain :RegistrationNativePlatformPublicAdapterSourceRuntime.M n KemSK R P (RegistrationNativePlatformPublicAdapterLowSpec.Spec.Range query))
    (law :∀before :RegistrationNativePlatformExtractedSdkPublic.State Private,
      (fun result=>RegistrationNativePlatformPublicAdapterSourceRuntime.embed (result.1,basePhysical result.2.1 result.2.2)) <$>
        (RegistrationNativePlatformExtractedSdkPublic.handler Private model calls query).run before=
      RegistrationNativePlatformPublicAdapterSourceRuntime.run plain (basePhysical before.1 before.2))
    (before :RegistrationNativePlatformPublicAdapterLoggedCommon.State Private n KemSK R P) :
    (fun result=>RegistrationNativePlatformPublicAdapterSourceRuntime.embed
      (result.1,RegistrationNativePlatformPublicAdapterLoggedCommon.physical Private basePhysical result.2)) <$>
      (RegistrationNativePlatformPublicAdapterLoggedRuntime.handler Private model calls (augment Private model calls) query).run before=
    RegistrationNativePlatformPublicAdapterSourceRuntime.run
      (RegistrationNativePlatformPublicAdapterSourceLogLift.lift plain)
      (RegistrationNativePlatformPublicAdapterLoggedCommon.physical Private basePhysical before) :=by
  have unchanged:=RegistrationNativePlatformPublicAdapterLoggedRuntime.query_unchanged Private model calls (Log:=Log n KemSK R P) query before
  change (RegistrationNativePlatformPublicAdapterLoggedRuntime.handler Private model calls (augment Private model calls) query).run before=_ at unchanged
  rw [unchanged,Functor.map_map,
    RegistrationNativePlatformPublicAdapterSourceLogLift.run_lift]
  have observed:=congrArg (fun computation=>(fun result=>(result.1,(result.2.1,(result.2.2,before.2)))) <$>computation) (law before.1)
  simp only [Functor.map_map] at observed
  exact observed

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedNoStage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedNoStage.joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedNoStage.joint
