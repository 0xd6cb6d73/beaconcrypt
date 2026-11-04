-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityFreeStageTrace
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutEvent
/-! The same eager family factors at one fixed public accept with every original private state and callback retained. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamily
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativePlatformIdentityCtxFamily (Physical Result run)
open PqxdhJointIdentityFamily (sampleFamily familyPublic)
open PqxdhDynamicIdentityRouting (PublicState initialPublicState)
open PqxdhJointIdentityFreshness (GlobalState initialState)
variable {count : Nat} {A S : Type}
abbrev Backend (count : Nat) := Physical × (PublicState × GlobalState count)

noncomputable def backend (joint : PqxdhJointIdentity.Primitives)
    (seeds : Fin count → PqxdhJointIdentity.IdentitySeed) : QueryImpl Spec (StateT (Backend count) ProbComp) :=
  QueryImpl.Stateful.link RegistrationNativePlatformIdentityCtxIndependent.reify
    (QueryImpl.Stateful.link (RegistrationNativeIdentityIndependentRouting.routeImpl (familyPublic joint seeds))
      (PqxdhJointIdentityFreshness.sourceImpl joint seeds))

/-- Every free source program has exactly this same physical/router/history execution for its fixed eager family. -/
theorem conditional (joint : PqxdhJointIdentity.Primitives)
    (seeds : Fin count → PqxdhJointIdentity.IdentitySeed) (work : OracleComp Spec A)
    (before : Backend count) :
    (simulateQ (backend joint seeds) work).run before =
      (fun result => (result.1.1,(result.1.2,result.2))) <$>
        (simulateQ (QueryImpl.Stateful.link
          (RegistrationNativeIdentityIndependentRouting.routeImpl (familyPublic joint seeds))
          (PqxdhJointIdentityFreshness.sourceImpl joint seeds))
          ((simulateQ RegistrationNativePlatformIdentityCtxIndependent.reify work).run before.1)).run before.2 := by
  rw [backend,QueryImpl.Stateful.simulateQ_link_run]
  rfl

/-- Sampling the family once gives the literal original family execution, including all physical and signing poststate. -/
theorem family (joint : PqxdhJointIdentity.Primitives) (work : OracleComp Spec A) (physical : Physical) :
    run joint count work physical = (do
      let seeds ← sampleFamily count
      let result ← (simulateQ (backend joint seeds) work).run (physical,(initialPublicState,initialState count))
      pure (seeds,((result.1,result.2.1),result.2.2))) := by
  simp only [run,conditional,bind_map_left]

/-- The original full private journal projects to the same executable free-controller trace, retaining the entire live family backend. -/
theorem traced (joint : PqxdhJointIdentity.Primitives)
    (seeds : Fin count → PqxdhJointIdentity.IdentitySeed)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Spec))) (work : OracleComp TypedSpec A)
    (before : S) (privateBefore : Backend count) :
    (fun result => (result.1.1,(result.1.2,result.2))) <$>
      (simulateQ (backend joint seeds)
        ((simulateQ (RegistrationNativeObservedStageTrace.handler id frontend) work).run (before,[]))).run privateBefore =
      Prod.map id RegistrationNativeIdentityFreeStageTrace.projectFull <$>
        (simulateQ (RegistrationNativeStageTrace.handler (QueryImpl.Stateful.link frontend (backend joint seeds))) work).run
          ((before,privateBefore),[]) := by
  rw [RegistrationNativeIdentityFreeStageTrace.full_program,QueryImpl.Stateful.simulateQ_link_run]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamily

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamily.conditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamily.conditional
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamily.family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamily.family
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamily.traced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamily.traced
