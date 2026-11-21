-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixHistory
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedEvents
/-! Same-prefix unissued literal fields win the ordinary joint weak-EUF game with the exact target history supplied by the actual family source. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixWins
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativePlatformIdentityCtxSigningLog (Trace)
open RegistrationNativeIdentityUnissuedAcceptCut (Cut stop packet)
open RegistrationNativeIdentityUnissuedPacketClient (field)
open RegistrationNativeIdentityUnissuedCutEvent (AtCut)
open RegistrationNativeIdentityUnissuedEvents (Field)
open RegistrationNativePlatformIdentityCtxFamily (Result run)
open PqxdhJointIdentityFamily (familyPublic)
variable {count : Nat} {A S : Type}

/-- The literal submitted field uses the exact same prefix signing history, even for aliased or uncreated reserved targets. -/
theorem wins (joint : PqxdhJointIdentity.Primitives)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Spec))) (work : OracleComp TypedSpec A)
    (before : S) (physical : RegistrationNativePlatformCtxBackend.State) (accept : Nat)
    (identity : Fin count) (tag : Fin 3) (fallback : PqxdhJointIdentity.Forgery)
    (bounded : ((simulateQ RegistrationNativePlatformIdentityCtxIndependent.reify
      ((simulateQ (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend) (stop accept work 0)).run (before,{}))).run physical).IsQueryBoundP
        RegistrationNativeIdentityIndependentSource.IsCreate count)
    (result : Result count (Cut A × (S × Trace)))
    (supported : result ∈ support (run joint count
      ((simulateQ (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend) (stop accept work 0)).run (before,{})) physical))
    (failed : AtCut (Field joint (familyPublic joint result.1) identity tag)
      (result.2.1.1.1,(result.2.1.1.2,[]))) :
    PqxdhJointIdentity.wins joint (familyPublic joint result.1 identity)
      ((field tag (packet result.2.1.1.1)).getD fallback) (result.2.2.2.histories identity) = true := by
  have history := RegistrationNativeIdentityUnissuedPrefixHistory.messages joint count frontend (stop accept work 0)
    before physical bounded result supported identity
  cases stopped : result.2.1.1.1 with
  | returned value => simp only [AtCut,stopped] at failed
  | accept current next =>
      simp only [AtCut,stopped] at failed
      obtain ⟨forgery,selected,valid,fresh⟩ := failed
      simp only [packet]
      apply RegistrationNativeIdentityUnissuedPacketClient.field_wins joint _ tag (some current) forgery fallback _ selected valid
      rw [history]
      exact fresh

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixWins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixWins.wins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixWins.wins
