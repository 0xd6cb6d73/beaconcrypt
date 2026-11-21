-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedRuntime
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogLift
/-! Opening and closing observations surround the same concrete sampled call. Its typed audit, physical source objects and source stages remain one joint execution. Erasure drops only the observation log. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCommon
open BeaconcryptCore.Refinement
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
open RegistrationNativePlatformPublicAdapterSourceEvents (Log Event)
abbrev Spec :=RegistrationNativePlatformPublicAdapterLowSpec.Spec
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations]
variable {n :Nat} {KemSK R P N Value :Type}
variable (Private :N→Type) (model :QueryImpl Spec (StateT N ProbComp))
variable (calls :∀query current,Private current→TotalStep Private ((model query).run current))
variable (basePhysical :∀current,Private current→RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P)
variable (augment :∀query (before :RegistrationNativePlatformExtractedSdkPublic.State Private),Log n KemSK R P→
  RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation (calls query before.1 before.2) (Log n KemSK R P))

abbrev State (Private :N→Type) (n :Nat) (KemSK R P :Type) :=
  RegistrationNativePlatformExtractedSdkPublic.State Private×Log n KemSK R P

def physical (before :State Private n KemSK R P) :RegistrationNativePlatformPublicAdapterSourceEvents.State n KemSK R P :=
  let stored:=basePhysical before.1.1 before.1.2
  {stored with backend:=(stored.backend.1,(stored.backend.2,before.2))}

def opened (query :Spec.Domain) (before :State Private n KemSK R P) :State Private n KemSK R P :=
  (before.1,before.2++[.opened query (basePhysical before.1.1 before.1.2)])

def closed (query :Spec.Domain) (result :Spec.Range query×State Private n KemSK R P) :Spec.Range query×State Private n KemSK R P :=
  let stored:=basePhysical result.2.1.1 result.2.1.2
  (result.1,(result.2.1,result.2.2++[.closed query (.ok (result.1,RegistrationNativePlatformPublicAdapterSourceRuntime.objects stored)) stored.backend]))

noncomputable def handler :QueryImpl Spec (StateT (State Private n KemSK R P) ProbComp) :=fun query before=>
  closed Private basePhysical query <$>
    (RegistrationNativePlatformPublicAdapterLoggedRuntime.handler Private model calls augment query).run (opened Private basePhysical query before)

theorem query_erase (query :Spec.Domain) (before :State Private n KemSK R P) :
    Prod.map id Prod.fst <$>(handler Private model calls basePhysical augment query).run before=
      (RegistrationNativePlatformExtractedSdkPublic.handler Private model calls query).run before.1 :=by
  dsimp only [handler,StateT.run]
  rw [Functor.map_map]
  exact RegistrationNativePlatformPublicAdapterLoggedRuntime.query_erase Private model calls augment query (opened Private basePhysical query before)

theorem program_erase (work :OracleComp Spec Value) (before :State Private n KemSK R P) :
    Prod.map id Prod.fst <$>(simulateQ (handler Private model calls basePhysical augment) work).run before=
      (simulateQ (RegistrationNativePlatformExtractedSdkPublic.handler Private model calls) work).run before.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (query_erase Private model calls basePhysical augment) work before

variable (stages :QueryImpl Spec (RegistrationNativePlatformPublicAdapterSourceRuntime.M n KemSK R (P×Log n KemSK R P)))
variable (stage_joint :∀query (before :State Private n KemSK R P),
  (fun result=>RegistrationNativePlatformPublicAdapterSourceRuntime.embed (result.1,physical Private basePhysical result.2)) <$>
    (RegistrationNativePlatformPublicAdapterLoggedRuntime.handler Private model calls augment query).run before=
  RegistrationNativePlatformPublicAdapterSourceRuntime.run (stages query) (physical Private basePhysical before))

include stage_joint in
theorem query_source (query :Spec.Domain) (before :State Private n KemSK R P) :
    (fun result=>RegistrationNativePlatformPublicAdapterSourceRuntime.embed (result.1,physical Private basePhysical result.2)) <$>
      (handler Private model calls basePhysical augment query).run before=
    RegistrationNativePlatformPublicAdapterSourceRuntime.run
      (RegistrationNativePlatformPublicAdapterSourceLogLift.callback query (stages query)) (physical Private basePhysical before) :=by
  rw [RegistrationNativePlatformPublicAdapterSourceLogLift.run_callback]
  dsimp only [handler,StateT.run]
  unfold RegistrationNativePlatformPublicAdapterSourceEvents.callback
  have initial :RegistrationNativePlatformPublicAdapterSourceEvents.append (physical Private basePhysical before)
      (.opened query (RegistrationNativePlatformPublicAdapterSourceEvents.store (physical Private basePhysical before)))=
    physical Private basePhysical (opened Private basePhysical query before) :=rfl
  rw [initial,←stage_joint query (opened Private basePhysical query before)]
  simp only [bind_pure_comp,Functor.map_map]
  rfl

include stage_joint in
theorem program_source (work :OracleComp Spec Value) (before :State Private n KemSK R P) :
    (fun result=>RegistrationNativePlatformPublicAdapterSourceRuntime.embed (result.1,physical Private basePhysical result.2)) <$>
      (simulateQ (handler Private model calls basePhysical augment) work).run before=
    RegistrationNativePlatformPublicAdapterSourceRuntime.run
      (simulateQ (fun query=>RegistrationNativePlatformPublicAdapterSourceLogLift.callback query (stages query)) work)
      (physical Private basePhysical before) :=
  RegistrationNativePlatformPublicAdapterSourceRuntime.program
    (handler Private model calls basePhysical augment)
    (fun query=>RegistrationNativePlatformPublicAdapterSourceLogLift.callback query (stages query))
    (physical Private basePhysical) (query_source Private model calls basePhysical augment stages stage_joint) work before

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCommon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCommon.query_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCommon.query_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCommon.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCommon.program_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCommon.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCommon.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCommon.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCommon.program_source
