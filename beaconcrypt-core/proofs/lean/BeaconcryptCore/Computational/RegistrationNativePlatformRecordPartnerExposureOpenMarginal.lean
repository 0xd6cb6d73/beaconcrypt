-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureFirstHit
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureDictionarySource
/-! The actual recovery cache is unobservable on the source's root/world open tree. Only that cache is erased; both root material tables, allocator counters, complete return and physical state remain. The literal source supplies NoAmbient, rather than identifying Combined coins with World coins. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureOpenMarginal
open LazyOracleDiscard (LawEq)
open RegistrationNativeSecretWord (Cache Key)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSuffixKeyPrf (Secret)
open RegistrationNativePlatformRecordPartnerExposureSlots (State)
open RegistrationNativePlatformRecordPartnerExposureDictionarySource (NoAmbient)
variable {n : Nat} {Physical A : Type}
def drop (before : RegistrationNativePlatformRecordPartnerExposureFirstHit.Private n Physical) : State n ×Physical :=
  (before.1,before.2.2)

private theorem map_apply {S X Y : Type} {m : Type →Type} [Monad m] [LawfulMonad m]
    (f : X →Y) (work : StateT S m X) (before : S) :
    (f <$>work) before=Prod.map f id <$>work before := StateT.run_map _ _ _
private theorem lift_apply {S X : Type} {m : Type →Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (StateT.lift work : StateT S m X) before=(fun value=>(value,before)) <$>work := bind_pure_comp _ _

variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (candidate : Secret)
    (filler : PqxdhServerAuthKeySchedule.Output)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
    (input : Message →Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix →Bool) (operand : Message →Message)
local notation "original"=>RegistrationNativePlatformRecordPartnerExposureFirstHit.closing source candidate physical input inside operand
local notation "realize"=>RegistrationNativePlatformRecordPartnerExposureRootSource.realization (n := n) source candidate filler

noncomputable def direct : QueryImpl (RegistrationNativePlatformLorOpenDictionary.Spec n) (StateT (State n ×Physical) ProbComp) :=
  fun query before=>(fun result=>(result.1.1,(result.1.2,result.2))) <$>
    (simulateQ physical (simulateQ realize
      ((RegistrationNativePlatformRecordPartnerExposureClient.closing source input inside operand query).run before.1))).run before.2

/-- Each actual source root or literal World query has the same marginal after dropping only its private recovery cache. -/
theorem query (request : (RegistrationNativePlatformLorOpenDictionary.Spec n).Domain) (allowed : NoAmbient request)
    (before : RegistrationNativePlatformRecordPartnerExposureFirstHit.Private n Physical) :
    LawEq (Prod.map id drop <$> (original request).run before)
      ((direct source candidate filler physical input inside operand request).run (drop before)) := by
  rcases before with ⟨roots,cache,physicalBefore⟩
  rcases request with (combined|world)|(prepared|demanded)
  · exact allowed.elim
  · apply LawEq.of_eq
    simp only [RegistrationNativePlatformRecordPartnerExposureFirstHit.closing,direct,drop,
      RegistrationNativePlatformRecordPartnerExposureClient.closing,RegistrationNativePlatformRecordPartnerExposureRootRecovery.close,
      RegistrationNativePlatformRecordPartnerExposureRootSource.realization,StateT.run,lift_apply,
      simulateQ_map,simulateQ_spec_query,map_apply,Functor.map_map,Prod.map_def,id_eq]
    rfl
  · apply LawEq.of_eq
    rfl
  · have same := LazyOracleDiscard.LawEq.map (fun result=>(result.1.1,(result.1.2,result.2)))
      (RegistrationNativePlatformRecordPartnerExposureRootRecovery.handler_observed source candidate physical filler input inside (.inr (operand demanded)) roots cache physicalBefore)
    simpa only [RegistrationNativePlatformRecordPartnerExposureFirstHit.closing,direct,drop,
      RegistrationNativePlatformRecordPartnerExposureClient.closing,RegistrationNativePlatformRecordPartnerExposureRoot.handler,StateT.run,Functor.map_map,Prod.map_def,id_eq,
      RegistrationNativePlatformRecordPartnerExposureRoot.RootSpec,RegistrationNativePlatformLorOpenDictionary.Spec,
      RegistrationNativePlatformLorOpenDictionary.RootSpec,OracleSpec.add_apply_inr] using same

/-- Every complete actual open-source tree retains its full return, material state and physical state under ordinary recovery cache erasure. -/
theorem program (work : OracleComp (RegistrationNativePlatformLorOpenDictionary.Spec n) A)
    (allowed : work.AllQueriesSatisfy NoAmbient)
    (before : RegistrationNativePlatformRecordPartnerExposureFirstHit.Private n Physical) :
    LawEq (Prod.map id drop <$> (simulateQ original work).run before)
      ((simulateQ (direct source candidate filler physical input inside operand) work).run (drop before)) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value=>exact LawEq.of_eq (by simp only [simulateQ_pure,StateT.run_pure,map_pure,Prod.map_apply,id_eq])
  | query_bind request next ih=>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
    refine (LazyOracleDiscard.LawEq.bind (LawEq.refl _) (fun result : (RegistrationNativePlatformLorOpenDictionary.Spec n).Range request ×RegistrationNativePlatformRecordPartnerExposureFirstHit.Private n Physical=>ih result.1 (allowed.2 result.1) result.2)).trans ?_
    have first := LazyOracleDiscard.LawEq.bind (query source candidate filler physical input inside operand request allowed.1 before)
      (fun result : (RegistrationNativePlatformLorOpenDictionary.Spec n).Range request ×(State n ×Physical)=>LawEq.refl ((simulateQ (direct source candidate filler physical input inside operand) (next result.1)).run result.2))
    simpa only [bind_map_left,Prod.map_def,id_eq] using first


/-- The direct marginal closing is exactly the same nested literal source interpretation with its two states flattened. -/
theorem direct_eq : direct source candidate filler physical input inside operand=
    (QueryImpl.mapStateTBase physical
      (QueryImpl.mapStateTBase realize (RegistrationNativePlatformRecordPartnerExposureClient.closing (n := n) source input inside operand))).flattenStateT := by
  funext request before
  rcases before with ⟨roots,physicalBefore⟩
  change (direct source candidate filler physical input inside operand request).run (roots,physicalBefore)=
    ((QueryImpl.mapStateTBase physical (QueryImpl.mapStateTBase realize
      (RegistrationNativePlatformRecordPartnerExposureClient.closing source input inside operand))).flattenStateT request).run (roots,physicalBefore)
  rw [QueryImpl.flattenStateT_mapStateTBase_apply_run]
  rfl

/-- The complete direct open-source tree preserves its actual material and physical states under the explicit source hierarchy. -/
theorem program_source (work : OracleComp (RegistrationNativePlatformLorOpenDictionary.Spec n) A)
    (roots : State n) (before : Physical) :
    (simulateQ (direct source candidate filler physical input inside operand) work).run (roots,before)=
      (fun result=>(result.1.1,(result.1.2,result.2))) <$>
        (simulateQ physical (simulateQ realize
          ((simulateQ (RegistrationNativePlatformRecordPartnerExposureClient.closing source input inside operand) work).run roots))).run before := by
  have sourceEq := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT physical
    (QueryImpl.mapStateTBase realize (RegistrationNativePlatformRecordPartnerExposureClient.closing (n := n) source input inside operand)) work roots before
  rw [←QueryImpl.simulateQ_mapStateTBase_run,←direct_eq] at sourceEq
  have mapped := congrArg (Functor.map (fun result=>(result.1.1,(result.1.2,result.2)))) sourceEq
  simpa only [Functor.map_map,id_map'] using mapped.symm

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureOpenMarginal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureOpenMarginal.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureOpenMarginal.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureOpenMarginal.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureOpenMarginal.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureOpenMarginal.direct_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureOpenMarginal.direct_eq

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureOpenMarginal.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureOpenMarginal.program_source
