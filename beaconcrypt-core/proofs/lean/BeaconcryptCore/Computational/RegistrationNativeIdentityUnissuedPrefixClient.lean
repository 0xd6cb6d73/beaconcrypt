-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedChosenGame
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace
/-! The original literal field client is the exact erasure of the public stopped signing-log execution, preserving the same target primitive history. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixClient
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativeIdentityUnissuedAcceptCut (packet stop)
open RegistrationNativeIdentityUnissuedPacketClient (field visit)
open RegistrationNativePlatformIdentityCtxFamily (run)
open RegistrationNativeIdentityTemplateProtocol (PublicSpec)
open PqxdhJointIdentityFamily (familyPublic)
variable {S A : Type} {count : Nat}

/-- Removing only the signing log and final controller state yields the exact original submitted field. -/
theorem field_source (frontend : QueryImpl TypedSpec (StateT S (OracleComp Spec)))
    (work : OracleComp TypedSpec A) (before : S) (accept : Nat) (tag : Fin 3) :
    (fun result => field tag (packet result.1)) <$>
      (simulateQ (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend) (stop accept work 0)).run (before,{}) =
      field tag <$> visit accept frontend work before 0 := by
  have erased := congrArg (Functor.map (fun result => field tag (packet result.1)))
    (RegistrationNativePlatformIdentityCtxSigningTrace.program_erasure frontend (stop accept work 0) (before,{}))
  rw [RegistrationNativeIdentityUnissuedAcceptCut.packet_source]
  simpa only [Functor.map_map,Prod.map_def,id_eq] using erased

noncomputable def client (frontend : QueryImpl TypedSpec (StateT S (OracleComp Spec)))
    (work : OracleComp TypedSpec A) (before : S) (physical : RegistrationNativePlatformCtxBackend.State)
    (accept : Nat) (tag : Fin 3) : OracleComp PublicSpec (Option PqxdhJointIdentity.Forgery) :=
  (fun observed => field tag observed.1) <$>
    (simulateQ RegistrationNativeIdentityUnissuedSource.reify (visit accept frontend work before 0)).run physical

/-- The entire reserved prefix execution, including its genuine target signing history, is the literal ordinary-client family game after only analysis-state erasure. -/
theorem game_source (joint : PqxdhJointIdentity.Primitives) (target : Fin (count+1))
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Spec)))
    (work : OracleComp TypedSpec A) (before : S) (physical : RegistrationNativePlatformCtxBackend.State)
    (accept : Nat) (tag : Fin 3) (fallback : PqxdhJointIdentity.Forgery) :
    (fun result => PqxdhJointIdentity.wins joint (familyPublic joint result.1 target)
      ((field tag (packet result.2.1.1.1)).getD fallback) (result.2.2.2.histories target)) <$>
      run joint (count+1)
        ((simulateQ (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend) (stop accept work 0)).run (before,{})) physical =
      RegistrationNativeIdentityUnissuedChosenGame.familyGame joint target
        (fun _keys => client frontend work before physical accept tag) fallback := by
  unfold RegistrationNativeIdentityUnissuedChosenGame.familyGame run client
  simp only [map_bind,map_pure]
  apply bind_congr
  intro seeds
  simp only [simulateQ_map,StateT.run_map]
  rw [RegistrationNativeIdentityUnissuedSource.family_program]
  have fields := congrArg (fun code =>
    (simulateQ (QueryImpl.Stateful.link
      (RegistrationNativeIdentityIndependentRouting.routeImpl (familyPublic joint seeds))
      (PqxdhJointIdentityFreshness.sourceImpl joint seeds))
      ((simulateQ RegistrationNativePlatformIdentityCtxIndependent.reify code).run physical)).run
        (PqxdhDynamicIdentityRouting.initialPublicState,PqxdhJointIdentityFreshness.initialState (count+1)))
    (field_source frontend work before accept tag)
  have mapped := congrArg (fun distribution => (fun result =>
    PqxdhJointIdentity.wins joint (familyPublic joint seeds target) (result.1.1.getD fallback)
      (result.2.2.histories target)) <$> distribution) fields
  simpa only [simulateQ_map,StateT.run_map,Functor.map_map,map_bind,map_pure,bind_map_left,bind_pure_comp] using mapped

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixClient

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixClient.field_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixClient.field_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixClient.game_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixClient.game_source
