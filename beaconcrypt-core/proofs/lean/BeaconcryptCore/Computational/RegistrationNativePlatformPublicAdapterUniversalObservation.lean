-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap
/-! Equal complete observation marginals transport an event under a universal implication on every supported pair sharing that observation. The proof uses an image event and never selects a compatible private receipt after observing a sample. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniversalObservation
variable {C K O :Type}

theorem bound (common :ProbComp C) (kem :ProbComp K) (left :C→O) (right :K→O)
    (same :left <$>common=right <$>kem) (sourceBad :C→Prop) (kemBad :K→Prop)
    (universal :∀c∈support common,∀k∈support kem,left c=right k→sourceBad c→kemBad k) :
    Pr{let c←common}[sourceBad c]≤Pr{let k←kem}[kemBad k] :=by
  let image :O→Prop:=fun observation=>∃c∈support common,left c=observation ∧sourceBad c
  calc
    _≤Pr{let c←common}[image (left c)]:=prEvent_mono_of_support common _ _ (fun c supported bad=>⟨c,supported,rfl,bad⟩)
    _=Pr{let observed←left <$>common}[image observed]:=(prEvent_map common left image).symm
    _=Pr{let observed←right <$>kem}[image observed]:=congrArg (fun computation=>Pr{let observed←computation}[image observed]) same
    _=Pr{let k←kem}[image (right k)]:=prEvent_map kem right image
    _≤_:=prEvent_mono_of_support kem _ _ (by
      intro k supported witness
      obtain ⟨c,reached,equal,bad⟩:=witness
      exact universal c reached k supported equal bad)

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniversalObservation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniversalObservation.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniversalObservation.bound
