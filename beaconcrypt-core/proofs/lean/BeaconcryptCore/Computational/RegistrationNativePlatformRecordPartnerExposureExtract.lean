-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSlots
/-! The analysis projection reads opaque atom-head addresses from the actual native slot table while keeping both material caches and exact allocator counters. Its image invariant is discharged by the genuine cold table and preserved through the actual root query correspondence. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureExtract
open RegistrationNativePlatformRecordPartnerExposureSlots (State native project)
open RegistrationNativeSecretWord (Word Key)
open RegistrationNativeSuffixKeyPrf (Secret Prefix)
variable {n : Nat}

def extract (candidate : Secret) (before : RegistrationNativeSelectiveHiddenService.State n) : State n :=
  ⟨fun head=>before.1.slots (RegistrationNativeSecretWord.eval candidate ⟨head,.atom⟩),
    before.1.next,before.1.demands,before.1.materials,before.2⟩

def Image (candidate : Secret) (before : RegistrationNativeSelectiveHiddenService.State n) : Prop :=
  project candidate (extract candidate before).assignments=before.1.slots

/-- Extracting the literal native image retains the same opaque addresses and every cache/counter coordinate. -/
theorem extract_native (candidate : Secret) (prepared : RegistrationNativeRelatedFamily.Message →Bool) (before : State n) :
    extract candidate (native candidate prepared before)=before := by
  cases before
  simp only [extract,native,RegistrationNativePlatformRecordPartnerExposureSlots.project_atom]

/-- A source-derived image table reconstructs its exact full native address dictionary. -/
theorem native_extract (candidate : Secret) (before : RegistrationNativeSelectiveHiddenService.State n) (image : Image candidate before) :
    native candidate before.1.prepared (extract candidate before)=before := by
  rcases before with ⟨⟨prepared,slots,next,demands,materials⟩,known⟩
  dsimp only [Image,extract] at image
  simp only [native,extract,image]

/-- Every concrete opaque allocation result lies in the exact native image; no converse slot assumption is required. -/
theorem image_native (candidate : Secret) (prepared : RegistrationNativeRelatedFamily.Message →Bool) (before : State n) :
    Image candidate (native candidate prepared before) := by
  unfold Image
  rw [extract_native]
  rfl

/-- Genuine cold source addresses project to a candidate-independent state while retaining the sampled material44 table and ordinary108 cache. -/
theorem cold_extract (candidate : Secret) (materials : (RegistrationNativePairedServices.MaterialSpec n).QueryCache)
    (known : RegistrationNativeSelectiveHiddenService.KnownOracle.QueryCache) :
    extract candidate ({RegistrationNativeHiddenService.initial with materials:=materials},known)=
      (⟨fun _=>none,0,0,materials,known⟩ : State n) := rfl

/-- The source's cold address dictionary discharges the image invariant internally. -/
theorem cold_image (candidate : Secret) (materials : (RegistrationNativePairedServices.MaterialSpec n).QueryCache)
    (known : RegistrationNativeSelectiveHiddenService.KnownOracle.QueryCache) :
    Image candidate ({RegistrationNativeHiddenService.initial with materials:=materials},known) := by
  rw [←RegistrationNativePlatformRecordPartnerExposureSlots.cold_source candidate materials known]
  exact image_native candidate _ _

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureExtract
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureExtract.extract_native' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureExtract.extract_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureExtract.native_extract' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureExtract.native_extract

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureExtract.image_native' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureExtract.image_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureExtract.cold_extract' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureExtract.cold_extract

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureExtract.cold_image' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureExtract.cold_image
