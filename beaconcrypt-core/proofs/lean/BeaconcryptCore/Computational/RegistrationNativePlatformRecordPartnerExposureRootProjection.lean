-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureExtract
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureNormalize
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootDemandSource
/-! The actual native root dictionary projects to the opaque normalized-demand proxy at its source-prepared queries. Projection erases only the preparation shadow; both caches, the literal allocator counters and every World effect remain. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootProjection
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativePlatformRecordPartnerExposureExtract (extract Image)
open RegistrationNativePlatformRecordPartnerExposureNormalize (message)
variable {n : Nat} {I KemSK : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (filler : PqxdhServerAuthKeySchedule.Output)
local notation "Input"=>RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
local notation "inside"=>RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))
local notation "realize"=>RegistrationNativePlatformRecordPartnerExposureRootSource.realization (n := n) setup.source candidate filler
local notation "native"=>RegistrationNativePlatformLorOpenDictionary.actualRoots (n := n) setup seed scalar candidate

private theorem operand_flag (original : Message) (before : RegistrationNativeSelectiveHiddenService.State n)
    (validFlag : (Input original).isSome=true → before.1.prepared (RegistrationNativeSecretWordMessage.eval candidate original)=true)
    (key : Key) (formed : Input (message candidate original)=some key) :
    before.1.prepared (RegistrationNativeSecretWordMessage.eval candidate (message candidate original))=true := by
  rw [RegistrationNativePlatformRecordPartnerExposureNormalize.eval]
  apply validFlag
  have available := congrArg Option.isSome formed
  rw [RegistrationNativePlatformRecordPartnerExposureNormalize.input] at available
  simpa only [Option.isSome_map,Option.isSome_some] using available

private theorem operand_safe (original : Message) (key : Key) (secret : PqxdhKemIndCca.MlKemSharedSecret)
    (formed : Input (message candidate original)=some key) (_protected : inside key.head=true)
    (word : key.word=.literal secret) : secret≠candidate := by
  intro same
  subst secret
  exact RegistrationNativePlatformRecordPartnerExposureNormalize.no_literal setup.joint setup.dh seed scalar candidate original key formed word

private theorem demand_lift (original : Message) (before : RegistrationNativeSelectiveHiddenService.State n)
    (image : Image candidate before)
    (validFlag : (Input original).isSome=true → before.1.prepared (RegistrationNativeSecretWordMessage.eval candidate original)=true) :
    (fun result=>(result.1,RegistrationNativePlatformRecordPartnerExposureSlots.native candidate before.1.prepared result.2)) <$>
      simulateQ realize ((RegistrationNativePlatformRecordPartnerExposureRoot.demand setup.source Input inside (message candidate original)).run
        (extract candidate before))=
      (native (.inr original)).run before := by
  have source := RegistrationNativePlatformRecordPartnerExposureRootDemandSource.actual_demand candidate filler setup seed scalar
    (message candidate original) (extract candidate before) before.1.prepared
    (operand_flag setup seed scalar candidate original before validFlag)
    (operand_safe setup seed scalar candidate original)
  have operand : native (.inr (message candidate original))=native (.inr original) := by
    simp only [RegistrationNativePlatformLorOpenDictionary.actualRoots,QueryImpl.mapStateTBase,
      RegistrationNativePlatformRecordPartnerExposureNormalize.eval]
  rw [operand,RegistrationNativePlatformRecordPartnerExposureExtract.native_extract candidate before image] at source
  exact source

/-- A source-prepared native demand has the same full reply and opaque-cache projection as the normalized executable proxy. -/
theorem demand (original : Message) (before : RegistrationNativeSelectiveHiddenService.State n)
    (image : Image candidate before)
    (validFlag : (Input original).isSome=true → before.1.prepared (RegistrationNativeSecretWordMessage.eval candidate original)=true) :
    Prod.map id (extract candidate) <$> (native (.inr original)).run before=
      simulateQ realize ((RegistrationNativePlatformRecordPartnerExposureRoot.handler setup.source Input inside
        (.inr (message candidate original))).run (extract candidate before)) := by
  have mapped := congrArg (Functor.map (Prod.map id (extract candidate)))
    (demand_lift setup seed scalar candidate filler original before image validFlag)
  simpa only [Functor.map_map,Function.comp_def,Prod.map_apply,id_eq,
    RegistrationNativePlatformRecordPartnerExposureExtract.extract_native,Prod.eta,id_map',
    RegistrationNativePlatformRecordPartnerExposureRoot.handler] using mapped.symm

include filler in
/-- Every supported actual native demand result remains inside the source-derived opaque address image. -/
theorem demand_image (original : Message) (before : RegistrationNativeSelectiveHiddenService.State n)
    (image : Image candidate before)
    (validFlag : (Input original).isSome=true → before.1.prepared (RegistrationNativeSecretWordMessage.eval candidate original)=true)
    (result : Option (RegistrationNativePairedChoice.Choice n) ×RegistrationNativeSelectiveHiddenService.State n)
    (supported : result∈support ((native (.inr original)).run before)) : Image candidate result.2 := by
  rw [←demand_lift setup seed scalar candidate filler original before image validFlag,support_map] at supported
  obtain ⟨reached,_called,equal⟩ := supported
  cases equal
  exact RegistrationNativePlatformRecordPartnerExposureExtract.image_native candidate _ _

/-- Actual native preparation changes only the erased flag shadow and keeps the same opaque-address state. -/
theorem prepare (original : Message) (before : RegistrationNativeSelectiveHiddenService.State n) :
    Prod.map id (extract candidate) <$> (native (.inl original)).run before=
      simulateQ realize ((RegistrationNativePlatformRecordPartnerExposureRoot.handler setup.source Input inside (.inl original)).run
        (extract candidate before)) := by
  rfl

/-- Native preparation retains the established opaque address image through its actual source flag update. -/
theorem prepare_image (original : Message) (before : RegistrationNativeSelectiveHiddenService.State n)
    (image : Image candidate before)
    (result : Unit ×RegistrationNativeSelectiveHiddenService.State n)
    (supported : result∈support ((native (.inl original)).run before)) : Image candidate result.2 := by
  let changed := Function.update before.1.prepared (RegistrationNativeSecretWordMessage.eval candidate original)
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar (RegistrationNativeSecretWordMessage.eval candidate original)).isSome
  change result∈support (pure ((),({before.1 with prepared:=changed},before.2)) :
    OracleComp (PqxdhRecordLiftInterface.WorldSpec n) _) at supported
  rw [mem_support_pure_iff] at supported
  cases supported
  exact image

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootProjection
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootProjection.demand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootProjection.demand

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootProjection.demand_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootProjection.demand_image

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootProjection.prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootProjection.prepare

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootProjection.prepare_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootProjection.prepare_image
