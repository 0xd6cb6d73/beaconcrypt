-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamilySampled
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixWins
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixClient
/-! An original unissued field at one public acceptance ordinal is bounded by the literal ordinary-client family game. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamilySecurity
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativePlatformIdentityCtxFamily (run)
open RegistrationNativeIdentityUnissuedAcceptCut (stop packet)
open RegistrationNativeIdentityUnissuedPacketClient (field)
open RegistrationNativeIdentityUnissuedEvents (At Field)
open RegistrationNativeIdentityUnissuedCutEvent (AtCut)
open PqxdhJointIdentityFamily (familyPublic)
variable {S A : Type} {count : Nat}

/-- The same complete eager-family journal's fixed public field event reduces to ordinary message weak-EUF using its actual chronological history. The only bill supplied locally is the syntactic source-create cap. -/
theorem bound (joint : PqxdhJointIdentity.Primitives) (target : Fin (count+1))
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Spec))) (work : OracleComp TypedSpec A)
    (before : S) (physical : RegistrationNativePlatformCtxBackend.State) (accept : Nat)
    (tag : Fin 3) (fallback : PqxdhJointIdentity.Forgery)
    (bounded : ((simulateQ RegistrationNativePlatformIdentityCtxIndependent.reify
      ((simulateQ (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend) (stop accept work 0)).run (before,{}))).run physical).IsQueryBoundP
        RegistrationNativeIdentityIndependentSource.IsCreate (count+1)) :
    Pr{let result ← (run joint (count+1)
      ((simulateQ (RegistrationNativeObservedStageTrace.handler id (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend)) work).run
        ((before,{}),[])) physical)}[At joint (familyPublic joint result.1) target accept tag result.2.1.1] ≤
      Pr{let result ← (RegistrationNativeIdentityUnissuedChosenGame.familyGame joint target
        (fun _keys => RegistrationNativeIdentityUnissuedPrefixClient.client frontend work before physical accept tag) fallback)}[result=true] := by
  have cut := RegistrationNativeIdentityUnissuedFamilySampled.bound joint
    (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend) work (before,{}) physical accept
      (fun seeds => Field joint (familyPublic joint seeds) target tag)
  have prefixBound : Pr{let result ← (run joint (count+1)
      ((simulateQ (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend) (stop accept work 0)).run (before,{})) physical)}[
        AtCut (Field joint (familyPublic joint result.1) target tag) (result.2.1.1.1,(result.2.1.1.2,[]))] ≤
      Pr{let result ← (run joint (count+1)
        ((simulateQ (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend) (stop accept work 0)).run (before,{})) physical)}[
          PqxdhJointIdentity.wins joint (familyPublic joint result.1 target)
            ((field tag (packet result.2.1.1.1)).getD fallback) (result.2.2.2.histories target)=true] := by
    apply prEvent_mono_of_support
    intro result supported failed
    exact RegistrationNativeIdentityUnissuedPrefixWins.wins joint frontend work before physical accept target tag fallback bounded result supported failed
  have game := congrArg (fun distribution => Pr{let result ← distribution}[result=true])
    (RegistrationNativeIdentityUnissuedPrefixClient.game_source joint target frontend work before physical accept tag fallback)
  simp only [prEvent_map] at game
  exact cut.trans (prefixBound.trans_eq game)

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamilySecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamilySecurity.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedFamilySecurity.bound
