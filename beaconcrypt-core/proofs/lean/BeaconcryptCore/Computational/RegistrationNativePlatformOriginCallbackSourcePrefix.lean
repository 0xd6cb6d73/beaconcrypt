-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackPrefix
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginPathBind
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackSourcePrefix
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordFactsOriginOrdinalPath (Prefix Path)
open PqxdhRecordFactsOriginOrdinalCut (Cut)
variable {n : Nat} {Q S A : Type} {spec : OracleSpec Q}
variable (front : QueryImpl spec (StateT S (OracleComp (ServiceSpec n))))
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))

/-- A genuine closed callback prefix expands to a prefix of the exact same free source tree, with every private reply/state and original seal history retained. -/
theorem lift {initial rest : OracleComp spec A} {before after : S × CtxPrivate n}
    (prefixPath : RegistrationNativePlatformOriginCallbackCut.Prefix (QueryImpl.Stateful.link front service)
      initial before rest after) (past0 : List (Label n)) :
    ∃ (past : List (Label n)) (cuts : List (Cut n (A × S))),
      Prefix service ((simulateQ front initial).run before.1) before.2 past0
        ((simulateQ front rest).run after.1) after.2 past cuts := by
  induction prefixPath with
  | initial=>exact ⟨past0,[],.initial⟩
  | @step query next state reply previous called ih=>
    obtain ⟨past,earlier,reached⟩ :=ih
    rw [QueryImpl.Stateful.link_impl_apply_run] at called
    simp only [support_map] at called
    obtain ⟨actual,called,same⟩ :=called
    cases same
    rw [←PqxdhRecordFactsOriginOrdinalTrace.track_drop service ((front query).run state.1) state.2 past] at called
    simp only [support_map] at called
    obtain ⟨decorated,supported,same⟩ :=called
    cases same
    have path := PqxdhRecordFactsOriginOrdinalPath.support_path service ((front query).run state.1) state.2 past decorated supported
    obtain ⟨history,completed⟩ :=PqxdhRecordFactsOriginOrdinalFinalPrefix.path_prefix service path
    let continuation :=fun result :spec.Range query × S=>(simulateQ front (next result.1)).run result.2
    have advanced :=RegistrationNativePlatformOriginPathBind.prefix_bind service continuation completed
    simp only [pure_bind] at advanced
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind] at reached
    exact ⟨history,earlier++decorated.1.map (RegistrationNativePlatformOriginPathBind.bindCut continuation),
      PqxdhRecordFactsOriginOrdinalPath.prefix_trans service reached advanced⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackSourcePrefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackSourcePrefix.lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackSourcePrefix.lift
