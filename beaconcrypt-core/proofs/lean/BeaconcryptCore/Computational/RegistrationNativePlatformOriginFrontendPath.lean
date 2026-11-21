-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginPathBind
import BeaconcryptCore.Computational.RegistrationNativeStageTrace
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginFrontendPath
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordFactsOriginOrdinalPath (Path Prefix)
open PqxdhRecordFactsOriginOrdinalCut (Cut)
open PqxdhRecordFactsOriginOrdinalTrace (Result)
open RegistrationNativeStageTrace (Call)
variable {n : Nat} {Q S A : Type} {spec : OracleSpec Q}
variable (front : QueryImpl spec (StateT S (OracleComp (ServiceSpec n))))
variable (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))

/-- A callback's complete source is reached in this same enclosing execution; its own completed path and following path share their exact private boundary. -/
def Located (initial : OracleComp (ServiceSpec n) (A × S)) (start : CtxPrivate n) (past : List (Label n))
    (final : (A × S) × CtxPrivate n) (wholeCuts : List (Cut n (A × S))) (call : Call spec (S × CtxPrivate n)) : Prop :=
  ∃ (next : spec.Range call.query × S → OracleComp (ServiceSpec n) (A × S))
      (history followingHistory : List (Label n))
      (earlier : List (Cut n (A × S))) (inside : List (Cut n (spec.Range call.query × S))) (later : List (Cut n (A × S))),
    Prefix service initial start past ((front call.query).run call.before.1 >>=next) call.before.2 history earlier ∧
    Prefix service ((front call.query).run call.before.1) call.before.2 history (pure (call.reply,call.after.1)) call.after.2 followingHistory inside ∧
    Path service (next (call.reply,call.after.1)) call.after.2 followingHistory (later,final) ∧
    wholeCuts=earlier++inside.map (RegistrationNativePlatformOriginPathBind.bindCut next)++later

private theorem completed (first : OracleComp (ServiceSpec n) A) (start finish : CtxPrivate n)
    (past history : List (Label n)) (value : A) (cuts : List (Cut n A))
    (path : Prefix service first start past (pure value) finish history cuts) :
    (value,finish) ∈ support ((simulateQ service first).run start) := by
  have full := PqxdhRecordFactsOriginOrdinalPath.prefix_path service path (Path.done value finish history)
  have reached := PqxdhRecordFactsOriginOrdinalPath.path_support service full
  rw [←PqxdhRecordFactsOriginOrdinalTrace.track_drop service first start past]
  simp only [support_map]
  exact ⟨(cuts++[],(value,finish)),reached,rfl⟩

/-- Expanding an arbitrary adaptive callback program yields one actual callback path. Every member is located on the same complete service path, with its literal source continuation and no replacement support run. -/
theorem extract (work : OracleComp spec A) (before : S) (start : CtxPrivate n) (past : List (Label n))
    (result : Result n (A × S))
    (path : Path service ((simulateQ front work).run before) start past result) :
    ∃ calls : List (Call spec (S × CtxPrivate n)),
      RegistrationNativeStageTrace.Path (QueryImpl.Stateful.link front service) (before,start) calls (result.2.1.2,result.2.2) ∧
      ∀call∈calls,Located front service ((simulateQ front work).run before) start past result.2 result.1 call := by
  induction work using OracleComp.inductionOn generalizing before start past result with
  | pure value =>
    simp only [simulateQ_pure,StateT.run_pure] at path
    have supported := PqxdhRecordFactsOriginOrdinalPath.path_support service path
    change result ∈ support (pure ([],((value,before),start)) : ProbComp _) at supported
    simp only [support_pure,Set.mem_singleton_iff] at supported
    subst result
    exact ⟨[],.nil _,fun _ member=>by cases member⟩
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind] at path ⊢
    let following := fun answered : spec.Range query × S => (simulateQ front (next answered.1)).run answered.2
    obtain ⟨answered,middle,history,earlier,later,first,tail,split⟩ :=
      RegistrationNativePlatformOriginPathBind.split service ((front query).run before) following start past result path
    obtain ⟨calls,actual,located⟩ := ih answered.1 answered.2 middle history (later,result.2) tail
    let head : Call spec (S × CtxPrivate n) := ⟨query,(before,start),answered.1,(answered.2,middle)⟩
    have called : RegistrationNativeStageTrace.Executed (QueryImpl.Stateful.link front service) head := by
      have supported := completed service ((front query).run before) start middle past history answered earlier first
      unfold RegistrationNativeStageTrace.Executed
      rw [QueryImpl.Stateful.link_impl_apply_run]
      simp only [support_map]
      exact ⟨(answered,middle),supported,rfl⟩
    refine ⟨head::calls,.cons head called calls _ actual,?_⟩
    intro call member
    rcases List.mem_cons.mp member with rfl|member
    · exact ⟨following,past,history,[],earlier,later,.initial,first,tail,split⟩
    · obtain ⟨callNext,callHistory,followingHistory,leading,inside,remaining,reached,completedCall,afterCall,sameCuts⟩ := located call member
      have leadingPath := RegistrationNativePlatformOriginPathBind.prefix_bind service following first
      simp only [pure_bind] at leadingPath
      refine ⟨callNext,callHistory,followingHistory,earlier.map (RegistrationNativePlatformOriginPathBind.bindCut following)++leading,
        inside,remaining,PqxdhRecordFactsOriginOrdinalPath.prefix_trans service leadingPath reached,completedCall,afterCall,?_⟩
      simpa only [List.append_assoc] using split.trans (congrArg (fun tail=>earlier.map (RegistrationNativePlatformOriginPathBind.bindCut following)++tail) sameCuts)
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginFrontendPath

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginFrontendPath.extract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginFrontendPath.extract
