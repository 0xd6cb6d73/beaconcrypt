-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenService
import BeaconcryptCore.Computational.RegistrationNativeSecretWordSource
import BeaconcryptCore.Computational.RegistrationNativeSuffixKeyPrf
/-! Candidate-independent opaque atom-head addresses project to the exact complete native input addresses. Existing material44 and known108 caches are retained; only the slot dictionary representation changes. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSlots
open PqxdhRecordLiftInterface (Slot)
open RegistrationNativeSuffixKeyPrf (Prefix Secret)
open RegistrationNativeSecretWord (Word Key)
variable {n : Nat}
abbrev Slots (n : Nat) := Prefix → Option (Slot n)

def project (candidate : Secret) (assignments : Slots n) (bytes : Pqxdh.Bytes) : Option (Slot n) :=
  (RegistrationNativeSecretWord.decode candidate bytes).bind fun key=>
    match key.word with
    | .atom=>assignments key.head
    | .literal _=>none

/-- The atom's complete native input retains exactly its opaque public-head slot. -/
theorem project_atom (candidate : Secret) (assignments : Slots n) (head : Prefix) :
    project candidate assignments (RegistrationNativeSecretWord.eval candidate ⟨head,.atom⟩)=assignments head := by
  simp [project,RegistrationNativeSecretWord.decode_eval,RegistrationNativeSecretWord.normalize]

/-- Extending one opaque address changes precisely its corresponding complete native input entry. -/
theorem project_update (candidate : Secret) (assignments : Slots n) (head : Prefix) (slot : Slot n) :
    project candidate (Function.update assignments head (some slot))=
      Function.update (project candidate assignments) (RegistrationNativeSecretWord.eval candidate ⟨head,.atom⟩) (some slot) := by
  funext bytes
  by_cases same : bytes=RegistrationNativeSecretWord.eval candidate ⟨head,.atom⟩
  · subst bytes
    rw [project_atom,Function.update_self,Function.update_self]
  · rw [Function.update_of_ne same]
    unfold project
    cases parsed : RegistrationNativeSecretWord.decode candidate bytes with
    | none=>rfl
    | some key=>
      simp only [Option.bind_some]
      cases word : key.word with
      | literal value=>rfl
      | atom=>
        have different : key.head≠head := by
          intro equal
          have formed := RegistrationNativeSecretWord.decode_some candidate bytes key parsed
          have sameKey : key=⟨head,.atom⟩ := by cases key; simp_all only
          rw [sameKey] at formed
          exact same formed.symm
        exact Function.update_of_ne different _ _

structure State (n : Nat) where
  assignments : Slots n
  next : Nat
  demands : Nat
  materials : (RegistrationNativePairedServices.MaterialSpec n).QueryCache
  known : RegistrationNativeSelectiveHiddenService.KnownOracle.QueryCache

def native (candidate : Secret) (prepared : RegistrationNativeRelatedFamily.Message → Bool) (before : State n) :
    RegistrationNativeSelectiveHiddenService.State n :=
  (⟨prepared,project candidate before.assignments,before.next,before.demands,before.materials⟩,before.known)

def reserve (head : Prefix) (before : State n) : Option (Slot n) × State n :=
  match before.assignments head with
  | some slot=>(some slot,before)
  | none=>if room : before.next<n then
      let slot : Slot n:=⟨before.next,room⟩
      (some slot,{before with assignments:=Function.update before.assignments head (some slot),next:=before.next+1})
    else (none,before)

/-- The actual native allocator is exactly the opaque allocator under the full-byte projection, retaining all counter/cache fields. -/
theorem reserve_source (candidate : Secret) (prepared : RegistrationNativeRelatedFamily.Message → Bool)
    (head : Prefix) (before : State n) :
    RegistrationNativeHiddenService.reserve (RegistrationNativeSecretWord.eval candidate ⟨head,.atom⟩) (native candidate prepared before).1=
      ((reserve head before).1,(native candidate prepared (reserve head before).2).1) := by
  cases found : before.assignments head with
  | some slot=>
    simp only [RegistrationNativeHiddenService.reserve,native,project_atom,reserve,found]
  | none=>
    by_cases room : before.next<n
    · simp [RegistrationNativeHiddenService.reserve,native,project_atom,reserve,found,room,project_update]
    · simp [RegistrationNativeHiddenService.reserve,native,project_atom,reserve,found,room]


/-- Genuine cold address state retains its already sampled material table and existing ordinary cache literally. -/
theorem cold_source (candidate : Secret) (materials : (RegistrationNativePairedServices.MaterialSpec n).QueryCache)
    (known : RegistrationNativeSelectiveHiddenService.KnownOracle.QueryCache) :
    native candidate (fun _=>false) ⟨fun _=>none,0,0,materials,known⟩=
      ({RegistrationNativeHiddenService.initial with materials:=materials},known) := by
  have empty : project candidate (fun _=>none : Slots n)=(fun _=>none) := by
    funext bytes
    unfold project
    cases RegistrationNativeSecretWord.decode candidate bytes with
    | none=>rfl
    | some key=>
      simp only [Option.bind_some]
      cases word : key.word <;> rfl
  simp only [native,RegistrationNativeHiddenService.initial,empty]


end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSlots
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSlots.project_atom' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSlots.project_atom
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSlots.project_update' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSlots.project_update
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSlots.reserve_source' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSlots.reserve_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSlots.cold_source' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSlots.cold_source
