-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamily
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedEventProjection
/-! A public acceptance cutoff bounds the same eager-family original event while retaining the full physical and signing backend. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamilyCut
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativeIdentityUnissuedFamily (Backend backend)
open RegistrationNativeIdentityUnissuedCutEvent (At AtCut)
variable {count : Nat} {A S : Type}

/-- The original fixed-ordinal event has exactly the same probability in the closed family execution and its projected free-controller journal. -/
theorem full_event (joint : PqxdhJointIdentity.Primitives)
    (seeds : Fin count → PqxdhJointIdentity.IdentitySeed)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Spec))) (work : OracleComp TypedSpec A)
    (before : S) (privateBefore : Backend count) (accept : Nat)
    (bad : beaconcrypt_core.registration.InitPacket → S → Prop) :
    Pr{let result ← ((simulateQ (backend joint seeds)
      ((simulateQ (RegistrationNativeObservedStageTrace.handler id frontend) work).run (before,[]))).run privateBefore)}[At bad accept result.1] =
      Pr{let result ← ((simulateQ (RegistrationNativeStageTrace.handler
        (QueryImpl.Stateful.link frontend (backend joint seeds))) work).run ((before,privateBefore),[]))}[
          At (fun packet state => bad packet state.1) accept result] := by
  have law := congrArg (fun distribution => Pr{let result ← distribution}[At bad accept (result.1,result.2.1)])
    (RegistrationNativeIdentityUnissuedFamily.traced joint seeds frontend work before privateBefore)
  simp only [prEvent_map,Prod.map_def,id_eq,RegistrationNativeIdentityFreeStageTrace.projectFull] at law
  simpa only [RegistrationNativeIdentityUnissuedEventProjection.at_map] using law

/-- The fixed-cut event uses the actual reached before-state; erasing its analysis call list preserves that event exactly. -/
theorem prefix_event (joint : PqxdhJointIdentity.Primitives)
    (seeds : Fin count → PqxdhJointIdentity.IdentitySeed)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Spec))) (work : OracleComp TypedSpec A)
    (before : S) (privateBefore : Backend count) (accept : Nat)
    (bad : beaconcrypt_core.registration.InitPacket → S → Prop) :
    Pr{let result ← ((simulateQ (RegistrationNativeStageTrace.handler
      (QueryImpl.Stateful.link frontend (backend joint seeds)))
        (RegistrationNativeIdentityUnissuedAcceptCut.stop accept work 0)).run ((before,privateBefore),[]))}[
          AtCut (fun packet (state : S × Backend count) => bad packet state.1) result] =
      Pr{let result ← ((simulateQ (backend joint seeds)
        ((simulateQ frontend (RegistrationNativeIdentityUnissuedAcceptCut.stop accept work 0)).run before)).run privateBefore)}[
          AtCut bad (result.1.1,(result.1.2,[]))] := by
  have erased := congrArg (fun distribution => Pr{let result ← distribution}[
      AtCut (fun packet (state : S × Backend count) => bad packet state.1) (result.1,(result.2,[]))])
    (RegistrationNativeStageTrace.erase (QueryImpl.Stateful.link frontend (backend joint seeds))
      (RegistrationNativeIdentityUnissuedAcceptCut.stop accept work 0) ((before,privateBefore),[]))
  unfold AtCut at erased ⊢
  simpa only [prEvent_map,Prod.map_def,id_eq,QueryImpl.Stateful.simulateQ_link_run,QueryImpl.Stateful.Frame.prod,
    PFunctor.Lens.State.fst_put,PFunctor.Lens.State.snd_put] using erased

/-- An original eager-family field event is bounded by its same public acceptance prefix, with no caller cutoff law and no private stopping test. -/
theorem bound (joint : PqxdhJointIdentity.Primitives)
    (seeds : Fin count → PqxdhJointIdentity.IdentitySeed)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Spec))) (work : OracleComp TypedSpec A)
    (before : S) (privateBefore : Backend count) (accept : Nat)
    (bad : beaconcrypt_core.registration.InitPacket → S → Prop) :
    Pr{let result ← ((simulateQ (backend joint seeds)
      ((simulateQ (RegistrationNativeObservedStageTrace.handler id frontend) work).run (before,[]))).run privateBefore)}[At bad accept result.1] ≤
      Pr{let result ← ((simulateQ (backend joint seeds)
        ((simulateQ frontend (RegistrationNativeIdentityUnissuedAcceptCut.stop accept work 0)).run before)).run privateBefore)}[
          AtCut bad (result.1.1,(result.1.2,[]))] := by
  rw [full_event]
  exact (RegistrationNativeIdentityUnissuedCutEvent.bound (QueryImpl.Stateful.link frontend (backend joint seeds))
    accept work (before,privateBefore) (fun packet state => bad packet state.1)).trans_eq
      (prefix_event joint seeds frontend work before privateBefore accept bad)

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamilyCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamilyCut.full_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamilyCut.full_event
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamilyCut.prefix_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamilyCut.prefix_event
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamilyCut.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamilyCut.bound
