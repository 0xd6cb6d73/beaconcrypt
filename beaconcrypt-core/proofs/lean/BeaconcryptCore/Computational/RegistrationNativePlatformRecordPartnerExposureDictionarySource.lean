-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootProjection
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClient
import BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureDictionarySource
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (WorldSpec)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativePlatformRecordPartnerExposureExtract (extract Image)
variable {n : Nat} {I KemSK A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (filler : PqxdhServerAuthKeySchedule.Output)
    (unused : QueryImpl RegistrationNativeSecretWordService.Combined (OracleComp (WorldSpec n)))
    (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK)
local notation "Input" => RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
local notation "inside" => RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))
local notation "operand" => RegistrationNativePlatformRecordPartnerExposureNormalize.message candidate
local notation "realize" => RegistrationNativePlatformRecordPartnerExposureRootSource.realization (n:=n) setup.source candidate filler
local notation "native" => RegistrationNativePlatformLorCtxLeaves.lower setup wire sign seed scalar candidate unused provider
local notation "proxy" => RegistrationNativePlatformRecordPartnerExposureClient.lowerWith setup wire sign seed scalar provider operand
local notation "nativeClose" => RegistrationNativePlatformLorCtxLeaves.closing setup seed scalar candidate unused
local notation "proxyClose" => RegistrationNativePlatformRecordPartnerExposureClient.closing setup.source Input inside operand
local notation "handler" => RegistrationNativePlatformLorOpenDictionary.handler setup wire sign Input inside provider

def project (before : RegistrationNativePlatformLorCtxLeaves.Symbolic n KemSK) :=
  (before.1,extract candidate before.2)

def Ready (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (before : RegistrationNativeSelectiveHiddenService.State n) : Prop :=
  match query with
  | .inl (.inr (.inl (.inl message))) =>
      (Input message).isSome=true →before.1.prepared (RegistrationNativeSecretWordMessage.eval candidate message)=true
  | _ => True

def Nonroot : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain →Prop
  | .inl (.inl _) | .inl (.inr (.inl (.inl _))) =>False
  | _ =>True

private theorem world_form (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (quiet : Nonroot query) (before : RegistrationNativeSecretWordInterpreter.State n KemSK) :
    ∃body : OracleComp (WorldSpec n) ((RegistrationNativeSecretWordInterface.Spec n KemSK).Range query ×RegistrationNativeSecretWordInterpreter.State n KemSK),
      (handler query).run before=simulateQ RegistrationNativePlatformLorOpenDictionary.embed
        (simulateQ RegistrationNativePlatformLorWorldDictionary.world body) := by
  rcases query with (prepare | (demand | common) | routed) | record
  · exact quiet.elim
  · exact quiet.elim
  · rcases common with publication | effect
    · refine ⟨(fun result => (result.1,{before with ordinary:={before.ordinary with receipts:=result.2}})) <$>
        simulateQ PqxdhRecordLiftInterface.effectLift
          ((RegistrationBoundSourceCompiler.compiler setup.source (RegistrationNativeWire.ledgerCodec wire).frameWrite sign publication).run before.ordinary.receipts),?_⟩
      simp only [RegistrationNativePlatformLorOpenDictionary.handler,QueryImpl.mapStateTBase,
        RegistrationNativePlatformLorWorldDictionary.handler,RegistrationNativePlatformLorWorldDictionary.common,
        RegistrationNativePlatformLorWorldDictionary.publication,StateT.run,simulateQ_map,←QueryImpl.simulateQ_compose]
      rfl
    · refine ⟨(fun reply => (reply,before)) <$>PqxdhRecordLiftInterface.effectLift effect,?_⟩
      simp only [RegistrationNativePlatformLorOpenDictionary.handler,QueryImpl.mapStateTBase,
        RegistrationNativePlatformLorWorldDictionary.handler,RegistrationNativePlatformLorWorldDictionary.common,
        RegistrationNativePlatformLorWorldDictionary.effect,StateT.run_mk,StateT.run_lift,bind_pure_comp,simulateQ_map,
        PqxdhRecordLiftInterface.effectLift,simulateQ_spec_query]
  · refine ⟨(fun result => (result.1,{before with kem:=result.2})) <$>
      simulateQ PqxdhRecordLiftInterface.coinLift ((provider routed).run before.kem),?_⟩
    simp only [RegistrationNativePlatformLorOpenDictionary.handler,QueryImpl.mapStateTBase,
      RegistrationNativePlatformLorWorldDictionary.handler,RegistrationNativePlatformLorWorldDictionary.routed,
      StateT.run,simulateQ_map,RegistrationNativePlatformLorWorldDictionary.coins,←QueryImpl.simulateQ_compose]
    rfl
  · refine ⟨(fun reply => (reply,before)) <$>((WorldSpec n).query (.inr (.inr record)) :OracleComp (WorldSpec n) _),?_⟩
    simp only [RegistrationNativePlatformLorOpenDictionary.handler,QueryImpl.mapStateTBase,StateT.run_mk,
      RegistrationNativePlatformLorWorldDictionary.record_run,simulateQ_map,simulateQ_spec_query]
    rfl

private theorem proxy_world (work : OracleComp (WorldSpec n) A)
    (before : RegistrationNativePlatformRecordPartnerExposureSlots.State n) :
    simulateQ realize ((simulateQ proxyClose
      (simulateQ RegistrationNativePlatformLorOpenDictionary.embed
        (simulateQ RegistrationNativePlatformLorWorldDictionary.world work))).run before)=
      (fun result => (result,before)) <$>work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativePlatformLorOpenDictionary.embed,
      RegistrationNativePlatformLorWorldDictionary.world,RegistrationNativePlatformRecordPartnerExposureClient.closing,
      StateT.run_bind,StateT.run_lift,simulateQ_spec_query,
      RegistrationNativePlatformRecordPartnerExposureRootSource.realization,map_bind,bind_assoc,pure_bind]
    apply bind_congr
    intro value
    exact ih value before

private theorem nonroot_source (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (quiet : Nonroot query) (before : RegistrationNativePlatformLorCtxLeaves.Symbolic n KemSK) :
    Prod.map id (project candidate) <$> (native query).run before=
      simulateQ realize ((proxy query).run (project candidate before)) := by
  simp only [project]
  obtain ⟨body,bodyEq⟩ := world_form setup wire sign seed scalar provider query quiet before.1
  rw [RegistrationNativePlatformLorCtxLeaves.lower,QueryImpl.flattenStateT_mapStateTBase_apply_run,
    RegistrationNativePlatformRecordPartnerExposureClient.lower_run,bodyEq]
  rw [RegistrationNativePlatformLorCtxLeaves.world_source,simulateQ_map,proxy_world]
  simp only [Functor.map_map,project,Prod.map_apply,id_eq]


/-- Each actual Word callback projects to the normalized public recovery proxy, retaining its complete Word state and original reply. Only the demanded material leaf requires its actual preparation flag. -/
theorem query (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (before : RegistrationNativePlatformLorCtxLeaves.Symbolic n KemSK) (image : Image candidate before.2)
    (ready : Ready setup seed scalar candidate query before.2) :
    Prod.map id (project candidate) <$> (native query).run before=
      simulateQ realize ((proxy query).run (project candidate before)) := by
  rcases query with (prepare | (demand | common) | routed) | record
  · rw [RegistrationNativePlatformLorCtxLeaves.lower,QueryImpl.flattenStateT_mapStateTBase_apply_run,
      RegistrationNativePlatformRecordPartnerExposureClient.lower_run]
    simp only [project,RegistrationNativePlatformLorOpenDictionary.prepare_run,simulateQ_spec_query,
      RegistrationNativePlatformLorOpenDictionary.root,RegistrationNativePlatformLorCtxLeaves.closing,
      RegistrationNativePlatformRecordPartnerExposureClient.closing,StateT.run_map,
      bind_pure_comp,simulateQ_map,Functor.map_map,Prod.map_apply,id_eq]
    have source := RegistrationNativePlatformRecordPartnerExposureRootProjection.prepare setup seed scalar candidate filler prepare before.2
    rw [←source]
    simp only [Functor.map_map]
    rfl
  · rw [RegistrationNativePlatformLorCtxLeaves.lower,QueryImpl.flattenStateT_mapStateTBase_apply_run,
      RegistrationNativePlatformRecordPartnerExposureClient.lower_run]
    simp only [project,RegistrationNativePlatformLorOpenDictionary.demand_run,simulateQ_map,
      RegistrationNativePlatformLorOpenDictionary.root,simulateQ_spec_query,
      RegistrationNativePlatformLorCtxLeaves.closing,RegistrationNativePlatformRecordPartnerExposureClient.closing,
      StateT.run_map,Functor.map_map,Prod.map_apply,id_eq]
    have source := RegistrationNativePlatformRecordPartnerExposureRootProjection.demand setup seed scalar candidate filler demand before.2 image ready
    rw [←source]
    simp only [Functor.map_map]
    rfl
  · exact nonroot_source setup wire sign seed scalar candidate filler unused provider _ (by trivial) before
  · exact nonroot_source setup wire sign seed scalar candidate filler unused provider _ (by trivial) before
  · exact nonroot_source setup wire sign seed scalar candidate filler unused provider _ (by trivial) before

private theorem nonroot_image (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (quiet : Nonroot query) (before : RegistrationNativePlatformLorCtxLeaves.Symbolic n KemSK)
    (image : Image candidate before.2)
    (result : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range query ×RegistrationNativePlatformLorCtxLeaves.Symbolic n KemSK)
    (supported : result∈support ((native query).run before)) : Image candidate result.2.2 := by
  obtain ⟨body,bodyEq⟩ := world_form setup wire sign seed scalar provider query quiet before.1
  rw [RegistrationNativePlatformLorCtxLeaves.lower,QueryImpl.flattenStateT_mapStateTBase_apply_run,bodyEq,
    RegistrationNativePlatformLorCtxLeaves.world_source,Functor.map_map,support_map] at supported
  obtain ⟨inner,_called,rfl⟩ := supported
  exact image

include filler in
/-- Every actual Word callback retains the source-derived opaque address image, including all nonroot publication/KEM/record replies. -/
theorem image (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (before : RegistrationNativePlatformLorCtxLeaves.Symbolic n KemSK) (image : Image candidate before.2)
    (ready : Ready setup seed scalar candidate query before.2)
    (result : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range query ×RegistrationNativePlatformLorCtxLeaves.Symbolic n KemSK)
    (supported : result∈support ((native query).run before)) : Image candidate result.2.2 := by
  rcases query with (prepare | (demand | common) | routed) | record
  · rw [RegistrationNativePlatformLorCtxLeaves.lower,QueryImpl.flattenStateT_mapStateTBase_apply_run] at supported
    simp only [RegistrationNativePlatformLorOpenDictionary.prepare_run,simulateQ_spec_query,
      RegistrationNativePlatformLorOpenDictionary.root,RegistrationNativePlatformLorCtxLeaves.closing,
      bind_pure_comp,simulateQ_map,StateT.run_map,Functor.map_map,support_map] at supported
    obtain ⟨inner,called,rfl⟩ := supported
    exact RegistrationNativePlatformRecordPartnerExposureRootProjection.prepare_image setup seed scalar candidate prepare before.2 image inner called
  · rw [RegistrationNativePlatformLorCtxLeaves.lower,QueryImpl.flattenStateT_mapStateTBase_apply_run] at supported
    simp only [RegistrationNativePlatformLorOpenDictionary.demand_run,simulateQ_map,
      RegistrationNativePlatformLorOpenDictionary.root,simulateQ_spec_query,
      RegistrationNativePlatformLorCtxLeaves.closing,StateT.run_map,Functor.map_map,support_map] at supported
    obtain ⟨inner,called,rfl⟩ := supported
    exact RegistrationNativePlatformRecordPartnerExposureRootProjection.demand_image setup seed scalar candidate filler demand before.2 image ready inner called
  · exact nonroot_image setup wire sign seed scalar candidate unused provider _ (by trivial) before image result supported
  · exact nonroot_image setup wire sign seed scalar candidate unused provider _ (by trivial) before image result supported
  · exact nonroot_image setup wire sign seed scalar candidate unused provider _ (by trivial) before image result supported

/-- Only the explicit root proxy may request Combined recovery; the literal open callback dictionary has no ambient Combined branch. -/
def NoAmbient : (RegistrationNativePlatformLorOpenDictionary.Spec n).Domain →Prop
  | .inl (.inl _) =>False
  | _ =>True

private theorem world_scope (work : OracleComp (WorldSpec n) A) :
    (simulateQ RegistrationNativePlatformLorOpenDictionary.embed
      (simulateQ RegistrationNativePlatformLorWorldDictionary.world work)).AllQueriesSatisfy NoAmbient := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativePlatformLorWorldDictionary.world,
      RegistrationNativePlatformLorOpenDictionary.embed,allQueriesSatisfy_query_bind_iff]
    exact ⟨by trivial,ih⟩

private theorem nonroot_scope (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (quiet : Nonroot query) (before : RegistrationNativeSecretWordInterpreter.State n KemSK) :
    ((handler query).run before).AllQueriesSatisfy NoAmbient := by
  obtain ⟨body,eq⟩ := world_form setup wire sign seed scalar provider query quiet before
  rw [eq]
  exact world_scope body

/-- Every literal open callback requests only explicit root leaves or source World leaves, with no caller source-safety premise. -/
theorem query_noAmbient (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK) :
    ((handler query).run before).AllQueriesSatisfy NoAmbient := by
  rcases query with (prepare | (demand | common) | routed) | record
  · rw [RegistrationNativePlatformLorOpenDictionary.prepare_run]
    simp only [RegistrationNativePlatformLorOpenDictionary.root,allQueriesSatisfy_query_bind_iff]
    exact ⟨by trivial,fun _ => by trivial⟩
  · rw [RegistrationNativePlatformLorOpenDictionary.demand_run]
    simp only [RegistrationNativePlatformLorOpenDictionary.root,map_eq_bind_pure_comp,allQueriesSatisfy_query_bind_iff]
    exact ⟨by trivial,fun _ => by trivial⟩
  all_goals exact nonroot_scope setup wire sign seed scalar provider _ (by trivial) before

/-- The actual adaptive open dictionary retains the same no-ambient-Combined syntax through all replies and failures. -/
theorem program_noAmbient (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK) :
    ((simulateQ handler work).run before).AllQueriesSatisfy NoAmbient := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,allQueriesSatisfy_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    exact allQueriesSatisfy_bind (query_noAmbient setup wire sign seed scalar provider query before)
      (fun result => ih result.1 result.2)
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureDictionarySource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureDictionarySource.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureDictionarySource.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureDictionarySource.image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureDictionarySource.image

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureDictionarySource.query_noAmbient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureDictionarySource.query_noAmbient

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureDictionarySource.program_noAmbient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureDictionarySource.program_noAmbient
