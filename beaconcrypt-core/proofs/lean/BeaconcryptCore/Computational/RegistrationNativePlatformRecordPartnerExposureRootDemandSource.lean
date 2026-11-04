-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootSource
/-! A single genuine material demand projects to the native selective service with the same retained caches and chronology. Only its own valid preparation and absence of a candidate-equal protected literal are local premises. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootDemandSource
open RegistrationNativePlatformRecordPartnerExposureSlots (State native)
open PqxdhRecordLiftInterface (effectLift)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open PqxdhServerAuthKeySchedule (Output)
variable {n : Nat}
variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (candidate : RegistrationNativeSuffixKeyPrf.Secret) (filler : Output)
local notation "realize" => RegistrationNativePlatformRecordPartnerExposureRootSource.realization (n := n) source candidate filler

/-- The individual native demand is the exact projected proxy callback before a candidate-equal protected literal appears. -/
theorem demand_source (input : Message →Option Key) (nativeInput : RegistrationNativeRelatedFamily.Message →Option Pqxdh.Bytes)
    (target : Option PqxdhJointIdentity.DhOutput) (message : Message) (before : State n)
    (prepared : RegistrationNativeRelatedFamily.Message →Bool)
    (inputLaw : nativeInput (RegistrationNativeSecretWordMessage.eval candidate message)=
      (input message).map (RegistrationNativeSecretWord.eval candidate))
    (validFlag : ∀key,input message=some key→prepared (RegistrationNativeSecretWordMessage.eval candidate message)=true)
    (literalSafe : ∀key secret,input message=some key→RegistrationNativeSecretWordProtection.inside target key.head=true→
      key.word=.literal secret→secret≠candidate) :
    (fun result=>(result.1,native candidate prepared result.2)) <$>
      simulateQ realize ((RegistrationNativePlatformRecordPartnerExposureRoot.demand source input
        (RegistrationNativeSecretWordProtection.inside target) message).run before)=
    simulateQ effectLift ((RegistrationNativeSelectiveHiddenService.demand source nativeInput
      (RegistrationNativeKeyFamilyPreparation.inside target) candidate (RegistrationNativeSecretWordMessage.eval candidate message)).run
      (native candidate prepared before)) := by
  cases formed : input message with
  | none=>
    have nativeNone : nativeInput (RegistrationNativeSecretWordMessage.eval candidate message)=none := by
      rw [inputLaw,formed,Option.map_none]
    cases flag : prepared (RegistrationNativeSecretWordMessage.eval candidate message) <;>
      simp only [RegistrationNativePlatformRecordPartnerExposureRoot.demand,RegistrationNativeSelectiveHiddenService.demand,
        RegistrationNativeSelectiveHiddenService.onHidden,RegistrationNativeHiddenService.demand,native,StateT.run,
        formed,nativeNone,flag,Bool.false_eq_true,ite_true,ite_false,simulateQ_pure,map_pure]
  | some key=>
    have flag := validFlag key formed
    have nativeSome : nativeInput (RegistrationNativeSecretWordMessage.eval candidate message)=some (RegistrationNativeSecretWord.eval candidate key) := by
      rw [inputLaw,formed,Option.map_some]
    cases protectedInput : RegistrationNativeSecretWordProtection.inside target key.head with
    | false=>
      have nativeOutside : RegistrationNativeKeyFamilyPreparation.inside target (RegistrationNativeSecretWord.eval candidate key)=false := by
        rw [←RegistrationNativeSecretWordProtection.inside_eval,protectedInput]
      have selectedFalse : RegistrationNativeSelectiveHiddenService.selected (RegistrationNativeKeyFamilyPreparation.inside target) candidate
          (RegistrationNativeSecretWord.eval candidate key)=false := by
        rw [RegistrationNativePlatformRecordPartnerExposureRootSource.selected_eval,protectedInput,Bool.false_and]
      cases wordEq : key.word with
      | atom=>
        simp only [RegistrationNativePlatformRecordPartnerExposureRoot.demand,RegistrationNativeSelectiveHiddenService.demand,
          RegistrationNativeSelectiveHiddenService.onHidden,RegistrationNativeHiddenService.demand,native,StateT.run,formed,nativeSome,
          flag,protectedInput,nativeOutside,selectedFalse,wordEq,Bool.false_eq_true,Bool.false_and,Bool.not_false,ite_true,ite_false,
          simulateQ_map,simulateQ_spec_query,RegistrationNativePlatformRecordPartnerExposureRootSource.realization,simulateQ_pure,map_pure]
        simp only [RegistrationNativeSuffixKeyPrf.value,RegistrationNativeSuffixKeyPrf.input,RegistrationNativeSecretWord.eval,wordEq,RegistrationNativeSecretWord.Word.eval]
      | literal secret=>
        simp only [RegistrationNativePlatformRecordPartnerExposureRoot.demand,RegistrationNativeSelectiveHiddenService.demand,
          RegistrationNativeSelectiveHiddenService.onHidden,RegistrationNativeHiddenService.demand,native,StateT.run,formed,nativeSome,
          flag,protectedInput,nativeOutside,selectedFalse,wordEq,Bool.false_eq_true,Bool.false_and,Bool.not_false,ite_true,ite_false,
          simulateQ_pure,map_pure]
        simp only [RegistrationNativeSuffixKeyPrf.value,RegistrationNativeSuffixKeyPrf.input,RegistrationNativeSecretWord.eval,wordEq,RegistrationNativeSecretWord.Word.eval]
    | true=>
      cases wordEq : key.word with
      | atom=>
        have chosen : RegistrationNativeSelectiveHiddenService.selected (RegistrationNativeKeyFamilyPreparation.inside target) candidate
            (RegistrationNativeSecretWord.eval candidate key)=true := by
          rw [RegistrationNativePlatformRecordPartnerExposureRootSource.selected_eval,protectedInput,wordEq]
          simp [RegistrationNativeSecretWord.Word.eval]
        rw [RegistrationNativeSelectiveHiddenService.demand_selected source nativeInput _ candidate _ _ _ flag nativeSome chosen]
        simp only [RegistrationNativePlatformRecordPartnerExposureRoot.demand,StateT.run,formed,protectedInput,ite_true,wordEq,
          simulateQ_bind,simulateQ_spec_query,RegistrationNativePlatformRecordPartnerExposureRootSource.realization,pure_bind]
        simp only [RegistrationNativeSelectiveHiddenService.onHidden,RegistrationNativeHiddenService.demand,native,StateT.run,
          flag,nativeSome,chosen,ite_true]
        have evaluated : RegistrationNativeSecretWord.eval candidate key=RegistrationNativeSecretWord.eval candidate ⟨key.head,.atom⟩ := by
          simp only [RegistrationNativeSecretWord.eval,wordEq]
        let counted : State n:={before with demands:=before.demands+1}
        have allocated : RegistrationNativeHiddenService.reserve (RegistrationNativeSecretWord.eval candidate key)
            (native candidate prepared counted).1=
          ((RegistrationNativePlatformRecordPartnerExposureSlots.reserve key.head counted).1,
            (native candidate prepared (RegistrationNativePlatformRecordPartnerExposureSlots.reserve key.head counted).2).1) := by
          rw [evaluated]
          exact RegistrationNativePlatformRecordPartnerExposureSlots.reserve_source candidate prepared key.head counted
        dsimp only [native,counted] at allocated
        rw [allocated]
        have keptKnown : (RegistrationNativePlatformRecordPartnerExposureSlots.reserve key.head counted).2.known=before.known := by
          unfold RegistrationNativePlatformRecordPartnerExposureSlots.reserve
          split
          · rfl
          · split <;> rfl
        cases reserved : RegistrationNativePlatformRecordPartnerExposureSlots.reserve key.head counted with
        | mk chosenSlot after=>
          rw [reserved] at keptKnown
          dsimp only at keptKnown
          cases chosenSlot with
          | none=>simp only [simulateQ_pure,map_pure,keptKnown]
          | some slot=>
            have same := RegistrationNativePlatformRecordPartnerExposureRootSource.material_source source candidate filler prepared slot after
            have mapped := congrArg (Functor.map (fun result=>(some (RegistrationNativePairedChoice.Choice.hidden ⟨slot,result.1⟩),result.2))) same
            simpa only [RegistrationNativeSelectiveHiddenService.onHidden,native,StateT.run,simulateQ_map,Functor.map_map,keptKnown] using mapped
      | literal secret=>
        have different := literalSafe key secret formed protectedInput wordEq
        have nativeProtected : RegistrationNativeKeyFamilyPreparation.inside target (RegistrationNativeSecretWord.eval candidate key)=true := by
          rw [←RegistrationNativeSecretWordProtection.inside_eval,protectedInput]
        have chosenFalse : RegistrationNativeSelectiveHiddenService.selected (RegistrationNativeKeyFamilyPreparation.inside target) candidate
            (RegistrationNativeSecretWord.eval candidate key)=false := by
          rw [RegistrationNativePlatformRecordPartnerExposureRootSource.selected_eval,protectedInput,wordEq]
          simp [RegistrationNativeSecretWord.Word.eval,different]
        rw [RegistrationNativeSelectiveHiddenService.demand_other source nativeInput _ candidate _ _ _ flag nativeSome nativeProtected chosenFalse]
        simp only [RegistrationNativePlatformRecordPartnerExposureRoot.demand,StateT.run,formed,protectedInput,ite_true,wordEq,
          simulateQ_bind,simulateQ_spec_query,RegistrationNativePlatformRecordPartnerExposureRootSource.realization,pure_bind]
        have evaluated : RegistrationNativeSecretWord.eval secret key=RegistrationNativeSecretWord.eval candidate key := by
          simp only [RegistrationNativeSecretWord.eval,wordEq,RegistrationNativeSecretWord.Word.eval]
        rw [evaluated]
        let counted : State n:={before with demands:=before.demands+1}
        have same := RegistrationNativePlatformRecordPartnerExposureRootSource.known_source source candidate filler prepared
          (RegistrationNativeSecretWord.eval candidate key) counted
        have mapped := congrArg (Functor.map (fun result=>(some (RegistrationNativePairedChoice.Choice.known (n := n) result.1),result.2))) same
        simpa only [native,counted,StateT.run,simulateQ_map,Functor.map_map] using mapped
variable {I KemSK : Type} {base : OracleSpec I}
/-- The literal concrete native root callback discharges the pointwise source-input correspondence internally. -/
theorem actual_demand (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (message : Message) (before : State n) (prepared : RegistrationNativeRelatedFamily.Message →Bool)
    (validFlag : ∀key,RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar message=some key→
      prepared (RegistrationNativeSecretWordMessage.eval candidate message)=true)
    (literalSafe : ∀key secret,RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar message=some key→
      RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)) key.head=true→
      key.word=.literal secret→secret≠candidate) :
    (fun result=>(result.1,native candidate prepared result.2)) <$>
      simulateQ (RegistrationNativePlatformRecordPartnerExposureRootSource.realization setup.source candidate filler)
        ((RegistrationNativePlatformRecordPartnerExposureRoot.demand setup.source
          (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
          (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) message).run before)=
    (RegistrationNativePlatformLorOpenDictionary.actualRoots setup seed scalar candidate (.inr message)).run (native candidate prepared before) :=
  demand_source setup.source candidate filler (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar) (setup.joint.staticDh seed (setup.dh.publicKey scalar))
    message before prepared (RegistrationNativeSecretWordMessage.input_eval setup.joint setup.dh seed scalar candidate message).symm validFlag literalSafe
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootDemandSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootDemandSource.demand_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootDemandSource.demand_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootDemandSource.actual_demand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootDemandSource.actual_demand
