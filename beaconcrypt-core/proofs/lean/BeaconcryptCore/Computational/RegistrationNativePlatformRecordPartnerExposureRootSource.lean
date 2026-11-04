-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRoot
import BeaconcryptCore.Computational.RegistrationNativeSecretWordProtection
/-! Individual root proxy demands recover their exact native state under the analysis interpretation. World coins, opaque slots and both material caches are retained; no public algorithm receives the candidate. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootSource
open RegistrationNativePlatformRecordPartnerExposureRoot (Spec)
open RegistrationNativePlatformRecordPartnerExposureSlots (State native)
open PqxdhRecordLiftInterface (Slot WorldSpec effectLift coinLift)
open RegistrationNativeSecretWordMessage (Message)
open PqxdhServerAuthKeySchedule (Output)
variable {n : Nat} {A : Type}

def realization (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (candidate : RegistrationNativeSuffixKeyPrf.Secret) (filler : Output) :
    QueryImpl (Spec n) (OracleComp (WorldSpec n))
  | .inl (.inl (.inl coin))=>coinLift coin
  | .inl (.inl (.inr _))=>pure filler
  | .inl (.inr head)=>pure (RegistrationNativeSuffixKeyPrf.value source candidate head)
  | .inr query=>(WorldSpec n).query query

variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (candidate : RegistrationNativeSuffixKeyPrf.Secret) (filler : Output)
local notation "actual" => realization (n := n) source candidate filler

/-- The proxy's local cache randomness follows the same literal World coin route. -/
theorem coins_source (work : ProbComp A) :
    simulateQ actual (simulateQ (RegistrationNativePlatformRecordPartnerExposureRoot.coins (n := n)) work)=simulateQ coinLift work := by
  rw [←QueryImpl.simulateQ_compose]
  congr 1

private theorem env_coins (work : ProbComp A) :
    simulateQ (effectLift (n := n)) (simulateQ RegistrationNativeHiddenService.coins work)=simulateQ coinLift work := by
  rw [←QueryImpl.simulateQ_compose]
  congr 1

/-- Actual hidden material reads preserve the same native allocator, prepared map and complete known cache. -/
theorem material_source (prepared : RegistrationNativeRelatedFamily.Message →Bool) (slot : Slot n) (before : State n) :
    (fun result=>(result.1,native candidate prepared result.2)) <$>
      simulateQ actual ((RegistrationNativePlatformRecordPartnerExposureRoot.material slot).run before)=
    simulateQ effectLift ((RegistrationNativeSelectiveHiddenService.onHidden (RegistrationNativeHiddenService.material slot)).run (native candidate prepared before)) := by
  simp only [RegistrationNativePlatformRecordPartnerExposureRoot.material,RegistrationNativeSelectiveHiddenService.onHidden,
    RegistrationNativeHiddenService.material,native,StateT.run]
  cases cached : before.materials slot with
  | some output=>simp only [simulateQ_pure,map_pure]
  | none=>
    simp only [simulateQ_map,Functor.map_map,coins_source,env_coins]

/-- Actual known protected material reads preserve both the opaque allocator and literal native108 cache. -/
theorem known_source (prepared : RegistrationNativeRelatedFamily.Message →Bool) (bytes : Pqxdh.Bytes) (before : State n) :
    (fun result=>(result.1,native candidate prepared result.2)) <$>
      simulateQ actual ((RegistrationNativePlatformRecordPartnerExposureRoot.known bytes).run before)=
    simulateQ effectLift ((RegistrationNativeSelectiveHiddenService.known bytes).run (native candidate prepared before)) := by
  simp only [RegistrationNativePlatformRecordPartnerExposureRoot.known,RegistrationNativeSelectiveHiddenService.known,native,StateT.run]
  cases cached : before.known bytes with
  | some output=>simp only [simulateQ_pure,map_pure]
  | none=>simp only [simulateQ_map,Functor.map_map,coins_source,env_coins]
/-- Native selection sees exactly the symbolic public head and evaluated final word. -/
theorem selected_eval (target : Option PqxdhJointIdentity.DhOutput) (key : RegistrationNativeSecretWord.Key) :
    RegistrationNativeSelectiveHiddenService.selected (RegistrationNativeKeyFamilyPreparation.inside target) candidate
      (RegistrationNativeSecretWord.eval candidate key)=
      (RegistrationNativeSecretWordProtection.inside target key.head && decide (key.word.eval candidate=candidate)) := by
  have suffix : PqxdhJointGapDh.readDh 160 (RegistrationNativeSecretWord.eval candidate key)=some (key.word.eval candidate) := by
    simp [PqxdhJointGapDh.readDh,RegistrationNativeSecretWord.eval]
    apply List.Vector.toList_injective
    exact List.take_of_length_le (by simp)
  simp only [RegistrationNativeSelectiveHiddenService.selected,←RegistrationNativeSecretWordProtection.inside_eval,suffix,Option.some.injEq]
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootSource.coins_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootSource.coins_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootSource.material_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootSource.material_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootSource.known_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootSource.known_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootSource.selected_eval' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootSource.selected_eval
