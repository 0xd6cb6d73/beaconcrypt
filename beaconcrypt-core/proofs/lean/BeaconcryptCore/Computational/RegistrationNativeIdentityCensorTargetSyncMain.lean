-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSync
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicSource

/-! The request-boundary target synchronization lifts through the literal Main interpretation and the public all-attempt callback entry marker. Every adaptive callback keeps the complete native/platform/private source state, including selections made after earlier callbacks. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSyncMain
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativeIdentityCensorTargetSync (lower lower_program)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {KemSK Platform A : Type} {mlSource : RegistrationNativeMldsa.Source}

/-- Main reassociation retains the same synchronized public/private target on every supported outcome. -/
theorem main (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (masked : Bool)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (prior : before.1.2.target = before.2.target) (result : A × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((interpret joint selected placeholder masked work).run before)) :
    result.2.1.2.target = result.2.2.target := by
  simp only [interpret, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨returned, called, completed⟩ := supported
  obtain rfl := eq_of_mem_support_pure _ completed
  exact lower_program joint selected placeholder masked (work.run before.1.1) before.1.2 before.2 prior returned called

/-- The public entry update counts all bundle attempts and leaves the synchronized target untouched. -/
theorem callback (joint : PqxdhJointIdentity.Primitives) (selected position : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (masked : Bool)
    (frontend : QueryImpl TypedSpec (RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource))
    (query : TypedSpec.Domain)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (prior : before.1.2.target = before.2.target)
    (result : TypedSpec.Range query × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((RegistrationNativeIdentityCensorPublicSource.callback
      (lower joint selected placeholder masked)
      (RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder frontend) query).run before)) :
    result.2.1.2.target = result.2.2.target := by
  have entered : (RegistrationNativeIdentityCensorCompiler.enter position query before.1.2).target = before.2.target := by
    rcases query with query | command
    · exact prior
    · cases command <;> exact prior
  rw [lower, RegistrationNativeIdentityCensorPublicSource.current] at supported
  exact main joint selected placeholder masked (frontend query)
    ((before.1.1, RegistrationNativeIdentityCensorCompiler.enter position query before.1.2), before.2) entered result supported

/-- The actual public callback interpreter preserves synchronization through arbitrary adaptive typed continuations. -/
theorem program (joint : PqxdhJointIdentity.Primitives) (selected position : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (masked : Bool)
    (frontend : QueryImpl TypedSpec (RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource))
    (work : OracleComp TypedSpec A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (prior : before.1.2.target = before.2.target)
    (result : A × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorPublicSource.callback
      (lower joint selected placeholder masked)
      (RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder frontend)) work).run before)) :
    result.2.1.2.target = result.2.2.target := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact prior
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨returned, called, continued⟩ := supported
    exact ih returned.1 returned.2
      (callback joint selected position placeholder masked frontend query before prior returned called) result continued

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSyncMain

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSyncMain.main' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSyncMain.main

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSyncMain.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSyncMain.callback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSyncMain.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSyncMain.program
