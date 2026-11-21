-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordMessage
/-! Normalizing only the private material-demand operand preserves its actual evaluated descriptor and all optional DH input branches. The original source frontend and chronological trace continue to carry the original message. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureNormalize
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Word Key)
open PqxdhKemIndCca (MlKemSharedSecret)

def message (candidate : MlKemSharedSecret) (before : Message) : Message :=
  {before with kem:=if before.kem=.literal candidate then .atom else before.kem}

/-- Demand-operand normalization leaves the exact native descriptor unchanged. -/
theorem eval (candidate : MlKemSharedSecret) (before : Message) :
    RegistrationNativeSecretWordMessage.eval candidate (message candidate before)=
      RegistrationNativeSecretWordMessage.eval candidate before := by
  cases word : before.kem with
  | atom=>simp [message,word,RegistrationNativeSecretWordMessage.eval]
  | literal value=>
    by_cases same : value=candidate
    · simp [message,word,same,RegistrationNativeSecretWordMessage.eval,Word.eval]
    · simp [message,word,same,RegistrationNativeSecretWordMessage.eval]

/-- Optional source DH input normalization changes only the final opaque word and retains the whole public head. -/
theorem input (joint : PqxdhJointIdentity.Primitives) (dh : PqxdhJointGapDh.DhInterface joint)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : MlKemSharedSecret) (before : Message) :
    RegistrationNativeSecretWordMessage.input joint dh seed scalar (message candidate before)=
      (RegistrationNativeSecretWordMessage.input joint dh seed scalar before).map (RegistrationNativeSecretWord.normalize candidate) := by
  have first : RegistrationNativeRelatedFamily.firstValue joint dh seed scalar
      (RegistrationNativeSecretWordMessage.eval RegistrationNativeSecretWordMessage.zero (message candidate before))=
      RegistrationNativeRelatedFamily.firstValue joint dh seed scalar
        (RegistrationNativeSecretWordMessage.eval RegistrationNativeSecretWordMessage.zero before) := by
    cases before.third <;> rfl
  simp only [RegistrationNativeSecretWordMessage.input,first,Option.bind_eq_bind,Option.pure_def,Option.map_bind]
  congr 1
  funext first
  simp only [Function.comp_apply,Option.map_bind]
  congr 1

/-- A normalized actual input never carries a literal copy of the selected candidate. -/
theorem no_literal (joint : PqxdhJointIdentity.Primitives) (dh : PqxdhJointGapDh.DhInterface joint)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : MlKemSharedSecret) (before : Message) (key : Key)
    (realized : RegistrationNativeSecretWordMessage.input joint dh seed scalar (message candidate before)=some key) :
    key.word≠.literal candidate := by
  rw [input] at realized
  rw [Option.map_eq_some_iff] at realized
  obtain ⟨original,_formed,equal⟩ := realized
  rw [←equal]
  unfold RegistrationNativeSecretWord.normalize
  split
  · intro impossible
    cases impossible
  · assumption

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureNormalize
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureNormalize.eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureNormalize.eval

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureNormalize.input' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureNormalize.input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureNormalize.no_literal' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureNormalize.no_literal
