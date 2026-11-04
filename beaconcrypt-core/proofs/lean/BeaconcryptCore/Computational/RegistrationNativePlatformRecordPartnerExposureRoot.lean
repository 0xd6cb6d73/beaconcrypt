-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSlots
import BeaconcryptCore.Computational.RegistrationNativePlatformLorOpenDictionary
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceCaps
/-! The actual recovery root proxy uses opaque atom-head slots and retains its material44/known108 caches and counters. It receives no candidate bytes; preparation is notified by the existing open source dictionary, and material demands alone log protected-key or suffix requests. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRoot
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativePlatformRecordPartnerExposureSlots (State reserve)
open PqxdhDeploymentHiddenLayout (Material)
open PqxdhServerAuthKeySchedule (Output)
open PqxdhRecordLiftInterface (Slot WorldSpec)
variable {n : Nat}
abbrev Spec (n : Nat) := Combined + WorldSpec n
abbrev RootSpec (n : Nat) := RegistrationNativePlatformLorOpenDictionary.RootSpec n

def world : QueryImpl (WorldSpec n) (OracleComp (Spec n)) := fun query=>(Spec n).query (.inr query)
def coins : QueryImpl unifSpec (OracleComp (Spec n)) := world ∘ₛ PqxdhRecordLiftInterface.coinLift

noncomputable def material (slot : Slot n) : StateT (State n) (OracleComp (Spec n)) Material := fun before=>
  match before.materials slot with
  | some output=>pure (output,before)
  | none=>(fun output=>(output,{before with materials:=before.materials.cacheQuery slot output})) <$>
      simulateQ coins ($ᵗ Material)

noncomputable def known (bytes : Pqxdh.Bytes) : StateT (State n) (OracleComp (Spec n)) Output := fun before=>
  match before.known bytes with
  | some output=>pure (output,before)
  | none=>(fun output=>(output,{before with known:=before.known.cacheQuery bytes output})) <$>
      simulateQ coins ($ᵗ Output)

noncomputable def demand (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message →Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix →Bool) (message : Message) :
    StateT (State n) (OracleComp (Spec n)) (Option (RegistrationNativePairedChoice.Choice n)) := fun before=>
  let counted:={before with demands:=before.demands+1}
  match input message with
  | none=>pure (none,counted)
  | some key=>
    if inside key.head then do
      let _ ←(Spec n).query (.inl (.inl (.inr key)))
      match key.word with
      | .atom=>match reserve key.head counted with
        | (none,after)=>pure (none,after)
        | (some slot,after)=>(fun result=>(some (.hidden ⟨slot,result.1⟩),result.2)) <$> (material slot).run after
      | .literal secret=>(fun result=>(some (.known result.1),result.2)) <$>
          (known (RegistrationNativeSecretWord.eval secret key)).run counted
    else match key.word with
      | .atom=>(fun output=>(some (.known output),counted)) <$> (Spec n).query (.inl (.inr key.head))
      | .literal secret=>pure (some (.known (RegistrationNativeSuffixKeyPrf.value source secret key.head)),counted)

noncomputable def handler (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message →Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix →Bool) :
    QueryImpl (RootSpec n) (StateT (State n) (OracleComp (Spec n)))
  | .inl _=>pure ()
  | .inr message=>demand source input inside message

/-- The genuine source preparation notification has no material access and changes no proxy cache or counter. -/
theorem prepare_run (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message →Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix →Bool) (message : Message) (before : State n) :
    (handler source input inside (.inl message)).run before=pure ((),before) := rfl

/-- A refused input retains all cache and allocation fields, counting the actual attempted demand. -/
theorem demand_missing (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message →Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix →Bool) (message : Message) (before : State n)
    (missing : input message=none) : (demand source input inside message).run before=
      pure (none,{before with demands:=before.demands+1}) := by
  simp only [demand,StateT.run,missing]

/-- Existing hidden material is reused literally with the complete proxy state. -/
theorem material_hit (slot : Slot n) (before : State n) (output : Material) (found : before.materials slot=some output) :
    (material slot).run before=pure (output,before) := by simp only [material,StateT.run,found]

/-- Existing ordinary protected material is reused literally with the complete proxy state. -/
theorem known_hit (bytes : Pqxdh.Bytes) (before : State n) (output : Output) (found : before.known bytes=some output) :
    (known (n := n) bytes).run before=pure (output,before) := by simp only [known,StateT.run,found]
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRoot
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRoot.prepare_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRoot.prepare_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRoot.demand_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRoot.demand_missing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRoot.material_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRoot.material_hit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRoot.known_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRoot.known_hit
