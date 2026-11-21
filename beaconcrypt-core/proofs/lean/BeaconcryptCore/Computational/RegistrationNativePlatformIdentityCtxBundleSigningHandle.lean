-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorExternalSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleTerminal
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashOutgoing
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSignScope
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleSigningHandle
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativePlatformIdentityCtxMain (M)
variable {n : Nat} {I KemSK Platform E A B Q : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source} {queries : OracleSpec Q}
def OnlyHandle (selected : Nat) : Spec.Domain → Prop
  | .inl (.inl (.inr (.service handle (.sign _)))) => handle = selected
  | _ => True
private theorem coin_only (handle : Nat) (query : Spec.Domain)
    (allowed : RegistrationNativePlatformIdentityCtxMldsaCoins.Coin query) : OnlyHandle handle query := by
  unfold OnlyHandle
  split
  · exact allowed.elim
  · trivial
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
/-- Every literal current outgoing leaf can sign only through its captured owner's indexed source handle. -/
theorem outgoing (request : RegistrationBeaconInitExecutor.Spec.Domain)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (RegistrationNativePlatformIdentityProgram.native
        (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
          setup source index owner request))).run before).AllQueriesSatisfy (OnlyHandle owner.identity.handle) := by
  cases request with
  | inl request => cases request with
    | hash request =>
        change ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
          (RegistrationNativePlatformIdentityProgram.native (RegistrationNativeIdentityFrontend.hash request))).run before).AllQueriesSatisfy _
        rw [RegistrationNativePlatformIdentityCtxHashOutgoing.outgoing]
        rw [allQueriesSatisfy_query_bind_iff]
        exact ⟨trivial, fun _ => trivial⟩
    | sign request payload digest =>
        exact (RegistrationNativePlatformIdentityCtxMldsaCoins.outgoing setup checks representation created index owner request payload digest before).mono
          (coin_only owner.identity.handle)
  | inr request =>
      rw [RegistrationNativePlatformIdentityCtxEdOutgoing.outgoing]
      unfold RegistrationNativePlatformIdentityCtxEdOutgoing.expected
      split
      · rw [allQueriesSatisfy_query_bind_iff]
        exact ⟨rfl, fun _ => trivial⟩
      · trivial
/-- The actual mutable writer branch introduces only its own coins, and every actual publication signing leaf retains the captured handle. -/
theorem callback
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : (RegistrationNativePlatformWriter.Spec E).Domain)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
        setup index owner writer query)).run before).AllQueriesSatisfy (OnlyHandle owner.identity.handle) := by
  cases query with
  | inl query => exact outgoing setup checks representation created index owner query before
  | inr query =>
      exact (RegistrationNativeIdentityCensorExternalSource.coin_only setup checks representation created (writer query) before).mono
        (coin_only owner.identity.handle)
private theorem program_safe (handle : Nat) (implementation : QueryImpl queries (M n KemSK Platform source))
    (safe : ∀ query before, ((implementation query).run before).AllQueriesSatisfy (OnlyHandle handle))
    (work : OracleComp queries A) (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((simulateQ implementation work).run before).AllQueriesSatisfy (OnlyHandle handle) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact allQueriesSatisfy_bind (safe query before) (fun result => ih result.1 result.2)
/-- The complete actual source publication tree has the captured indexed signing handle under all primitive and writer replies. -/
theorem publication
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (RegistrationNativePlatformWriter.Spec E) A)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (simulateQ (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
        setup index owner writer) work)).run before).AllQueriesSatisfy (OnlyHandle owner.identity.handle) := by
  rw [RegistrationNativePlatformIdentityCtxOutgoingFold.publication]
  exact program_safe owner.identity.handle _ (callback setup checks representation created index owner writer) work before
/-- The literal captured-owner bundle signs only through that owner's handle, retaining every dynamic source writer failure and terminal World effect. -/
theorem bundled (scalar : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (RegistrationNativePlatformIdentityBundle.bundled (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
        setup index owner scalar writer)).run before).AllQueriesSatisfy (OnlyHandle owner.identity.handle) := by
  rw [RegistrationNativePlatformIdentityCtxBundleScope.bundled_fold, StateT.run_bind]
  apply allQueriesSatisfy_bind
    (publication setup checks representation created index owner writer _ before)
  intro reached
  rw [RegistrationNativeIdentityCensorBundleTerminal.next_run]
  trivial
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleSigningHandle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleSigningHandle.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleSigningHandle.outgoing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleSigningHandle.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleSigningHandle.callback
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleSigningHandle.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleSigningHandle.publication
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleSigningHandle.bundled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleSigningHandle.bundled
