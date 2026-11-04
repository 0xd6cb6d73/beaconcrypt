-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamilyCut
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedEventProjection
/-! A public acceptance cutoff bounds the same eager-family original event while retaining the full physical and signing backend. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamilySampled
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativeIdentityUnissuedCutEvent (At AtCut)
variable {count : Nat} {A S : Type}

/-- Sampling one eager family preserves the same fixed public cutoff bound on the complete original journal. -/
theorem bound (joint : PqxdhJointIdentity.Primitives)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Spec))) (work : OracleComp TypedSpec A)
    (before : S) (physical : RegistrationNativePlatformCtxBackend.State) (accept : Nat)
    (bad : (Fin count → PqxdhJointIdentity.IdentitySeed) → beaconcrypt_core.registration.InitPacket → S → Prop) :
    Pr{let result ← (RegistrationNativePlatformIdentityCtxFamily.run joint count
      ((simulateQ (RegistrationNativeObservedStageTrace.handler id frontend) work).run (before,[])) physical)}[
        At (bad result.1) accept result.2.1.1] ≤
      Pr{let result ← (RegistrationNativePlatformIdentityCtxFamily.run joint count
        ((simulateQ frontend (RegistrationNativeIdentityUnissuedAcceptCut.stop accept work 0)).run before) physical)}[
          AtCut (bad result.1) (result.2.1.1.1,(result.2.1.1.2,[]))] := by
  rw [RegistrationNativeIdentityUnissuedFamily.family,RegistrationNativeIdentityUnissuedFamily.family]
  simp only [bind_pure_comp]
  rw [prEvent_bind_eq_tsum,prEvent_bind_eq_tsum]
  simp only [prEvent_map]
  apply ENNReal.tsum_le_tsum
  intro seeds
  exact mul_le_mul' le_rfl (RegistrationNativeIdentityUnissuedFamilyCut.bound joint seeds frontend work before
    (physical,PqxdhDynamicIdentityRouting.initialPublicState,PqxdhJointIdentityFreshness.initialState count) accept (bad seeds))

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamilySampled

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamilySampled.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamilySampled.bound
