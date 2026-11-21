-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackFreeStop
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginPathBind
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackSourceStop
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordFactsOriginOrdinalPath (Prefix Path)
open PqxdhRecordFactsOriginOrdinalCut (Cut)
open RegistrationNativePlatformOriginCallbackFreeStop (stop markedResume)
variable {n : Nat} {Q S A : Type} {spec : OracleSpec Q}
variable (front : QueryImpl spec (StateT S (OracleComp (ServiceSpec n))))
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))

/-- An actually selected callback scan reaches the corresponding public certificate continuation in the exact free extended client, at the same full private prestate and before its reply. -/
theorem reached (counted : spec.Domain → Prop) (work : OracleComp spec A) (index : Nat)
    (before : S × CtxPrivate n) (past0 : List (Label n))
    (cut : RegistrationNativePlatformOriginCallbackCut.Cut spec (S × CtxPrivate n) A)
    (supported : Sum.inr cut∈support (RegistrationNativePlatformOriginCallbackCut.scan counted
      (QueryImpl.Stateful.link front service) work index before)) :
    ∃past cuts,Prefix service
      ((simulateQ front (stop counted work index >>=markedResume)).run before.1) before.2 past0
      ((simulateQ front (markedResume (.pending cut.query cut.next))).run cut.state.1) cut.state.2 past cuts := by
  rw [←RegistrationNativePlatformOriginCallbackFreeStop.scan_source] at supported
  simp only [support_map] at supported
  obtain ⟨stopped,called,same⟩ :=supported
  rcases stopped with ⟨stopped,after⟩
  cases stopped with
  | complete value=>cases same
  | pending query next=>
    simp only [RegistrationNativePlatformOriginCallbackFreeStop.attach,Sum.inr.injEq] at same
    cases same
    rw [QueryImpl.Stateful.simulateQ_link_run] at called
    simp only [support_map] at called
    obtain ⟨actual,called,same⟩ :=called
    rcases actual with ⟨⟨actualCut,actualS⟩,actualPrivate⟩
    cases same
    rw [←PqxdhRecordFactsOriginOrdinalTrace.track_drop service
      ((simulateQ front (stop counted work index)).run before.1) before.2 past0] at called
    simp only [support_map] at called
    obtain ⟨decorated,called,same⟩ :=called
    rcases decorated with ⟨earlier,⟨⟨actualCut,actualS⟩,actualPrivate⟩⟩
    cases same
    have actualPath:=PqxdhRecordFactsOriginOrdinalPath.support_path service _ _ _ (earlier,_) called
    obtain ⟨past,completed⟩ :=PqxdhRecordFactsOriginOrdinalFinalPrefix.path_prefix service actualPath
    let nextSource:=fun returned :RegistrationNativePlatformOriginCallbackFreeStop.Cut spec A × S=>(simulateQ front (markedResume returned.1)).run returned.2
    have lifted:=RegistrationNativePlatformOriginPathBind.prefix_bind service nextSource completed
    simp only [pure_bind] at lifted
    refine ⟨past,earlier.map (RegistrationNativePlatformOriginPathBind.bindCut nextSource),?_⟩
    simpa only [simulateQ_bind,StateT.run_bind,nextSource,QueryImpl.Stateful.Frame.prod,PFunctor.Lens.State.fst,PFunctor.Lens.State.snd,PFunctor.Lens.State.mk_put] using lifted
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackSourceStop
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackSourceStop.reached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackSourceStop.reached
