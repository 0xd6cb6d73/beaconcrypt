-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceTails
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheWorld
/-! Every genuine source request except hidden sealing retains the complete successful-seal histories, including failed openings and all public platform effects. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginSealRetention
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode KeyEntry ctxInterpreter onBase)
open PqxdhRecordLiftProtocol (Service ServiceSpec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {I KemSK Reader Response A : Type} {base : OracleSpec I}
variable (modes : Label n → KeyMode) (ideal : ∀label,modes label≠.real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK) (codec : Codec Reader Response)

include ideal in
/-- Actual nonsealing leaf semantics preserve every successful-seal history, while retaining all their other effects. -/
theorem query (request : Service n) (quiet : ¬RegistrationNativePlatformOriginSourceTails.Sealing request)
    (before : CtxPrivate n) (result : (ServiceSpec n).Range request × CtxPrivate n)
    (supported : result∈support ((ctxInterpreter modes replace setup codec request).run before)) :
    ∀label,(result.2.keys label).1.successfulSeals=(before.keys label).1.successfulSeals := by
  cases request
  case sealing pending=>exact False.elim (quiet ⟨pending,rfl⟩)
  case opening pending=>exact PqxdhRecordFactsOriginServices.opening_seals modes ideal replace setup codec pending before result supported
  case lookup coordinate=>
    exact fun label=>congrArg (fun keys=>(keys label).1.successfulSeals)
      (PqxdhRecordFactsOriginReceive.lookup_preserves modes replace setup codec coordinate before result supported).1
  case publish tag=>
    simp only [ctxInterpreter,onBase,PqxdhRecordLiftProtocol.interpreter,StateT.run,map_pure,
      support_pure,Set.mem_singleton_iff] at supported
    exact supported ▸ fun _=>rfl
  all_goals first
    | exact fun label=>congrArg (fun keys=>(keys label : KeyEntry).1.successfulSeals)
        (PqxdhRecordFactsOriginAmbient.environmental_kept modes replace setup codec _ (by trivial) before result supported).keys
    | (simp only [ctxInterpreter,onBase,PqxdhRecordLiftProtocol.interpreter,
        PqxdhRecordLiftProtocol.withRecord,StateT.run,bind_pure_comp,Functor.map_map,support_map] at supported
       obtain ⟨inner,_called,rfl⟩ := supported
       exact fun _=>rfl)

include ideal in
/-- Every actual adaptive source tree with no hidden sealing request preserves the exact original histories. -/
theorem program (work : OracleComp (ServiceSpec n) A)
    (quiet : work.AllQueriesSatisfy (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request))
    (before : CtxPrivate n) (result : A × CtxPrivate n)
    (supported : result∈support ((simulateQ (ctxInterpreter modes replace setup codec) work).run before)) :
    ∀label,(result.2.keys label).1.successfulSeals=(before.keys label).1.successfulSeals := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value=>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact fun _=>rfl
  | query_bind request next ih=>
    rw [allQueriesSatisfy_query_bind_iff] at quiet
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,continued⟩ := supported
    intro label
    exact (ih middle.1 (quiet.2 middle.1) middle.2 result continued label).trans
      (query modes ideal replace setup codec request quiet.1 before middle called label)
private theorem law_support {X : Type} {first second : ProbComp X}
    (law : LazyOracleDiscard.LawEq first second) : support first=support second := by
  let : MeasurableSpace X := ⊤
  ext value
  rw [mem_support_iff_evalDist_singleton_pos,mem_support_iff_evalDist_singleton_pos,law.evalDist_eq]

include ideal in
/-- The explicitly uniform-normalized private-cache service retains the same successful histories; this follows from its proved complete observation law, without identifying private instrumentation. -/
theorem erased (work : OracleComp (ServiceSpec n) A)
    (quiet : work.AllQueriesSatisfy (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request))
    (before : CtxPrivate n) (result : A × CtxPrivate n)
    (supported : result∈support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) work).run
      (PqxdhRecordFactsCounter.zeroCtx before))) :
    ∀label,(result.2.keys label).1.successfulSeals=(before.keys label).1.successfulSeals := by
  have law := PqxdhRecordFactsPrivateCacheWorld.program_observation modes replace setup codec ideal work before
  have same := law_support law
  have mapped : Prod.map id PqxdhRecordFactsPrivateCacheFamily.observeFamily result∈support
      (Prod.map id PqxdhRecordFactsPrivateCacheWorld.observe <$>
        (simulateQ (ctxInterpreter modes replace setup codec) work).run before) := by
    rw [same,support_map]
    exact ⟨result,supported,rfl⟩
  rw [support_map] at mapped
  obtain ⟨original,called,sameView⟩ := mapped
  intro label
  have entryEq : (original.2.keys label).1.successfulSeals=(result.2.keys label).1.successfulSeals :=
    congrArg (fun value=>(value.2.2 label).successfulSeals) sameView
  exact entryEq.symm.trans (program modes ideal replace setup codec work quiet before original called label)

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginSealRetention

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSealRetention.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSealRetention.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSealRetention.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSealRetention.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSealRetention.erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSealRetention.erased
