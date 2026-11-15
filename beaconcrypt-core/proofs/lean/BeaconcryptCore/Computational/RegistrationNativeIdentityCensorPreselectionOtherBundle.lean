-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdNonselectedSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorHashFrame
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleTerminal

/-! Every genuine publication leaf under a different opaque owner handle has identical full real and censored source behavior, before or after target selection. The dynamic writer and terminal owner update are retained. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionOtherBundle
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (placeholder : Ed25519Signature)
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "FullState" => Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "source(" censored "," work ")" => interpret setup.joint selected placeholder censored work
local notation "callback(" censored ")" => (fun query => source(censored, Main
  (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup index owner writer query)))

private def close (result : ((A × (RegistrationNativeIdentityMain.State n KemSK mlSource × Platform)) ×
    RegistrationNativeIdentityCensorCompiler.Mode) × RegistrationNativeIdentityCensorSource.State) : A × FullState :=
  (result.1.1.1, ((result.1.1.2, result.1.2), result.2))
private theorem closed (censored : Bool) (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A) (before : FullState) :
    (source(censored, work)).run before =
      close <$> RegistrationNativeIdentityCensorMldsaOutgoingSource.run setup.joint selected placeholder censored
        (work.run before.1.1) before.1.2 before.2 := by
  simp only [interpret, StateT.run, RegistrationNativeIdentityCensorMldsaOutgoingSource.run, bind_pure_comp]
  rfl

private theorem coin_equal (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A) (before : FullState)
    (allowed : (work.run before.1.1).AllQueriesSatisfy RegistrationNativePlatformIdentityCtxMldsaCoins.Coin) :
    (source(false, work)).run before = (source(true, work)).run before := by
  rw [closed, closed, RegistrationNativeIdentityCensorMldsaOutgoingSource.uniform_equal setup.joint selected placeholder _ allowed]

private theorem query_equal (different : owner.identity.handle ≠ selected)
    (query : (RegistrationNativePlatformWriter.Spec E).Domain) (before : FullState) :
    ((callback(false)) query).run before = ((callback(true)) query).run before := by
  cases query with
  | inl query => cases query with
    | inr request =>
      exact RegistrationNativeIdentityCensorEdNonselectedSource.outgoing setup checks representation created selected index owner request placeholder before different
    | inl query => cases query with
      | hash request => exact RegistrationNativeIdentityCensorHashOutgoingSource.hash_same setup checks representation created selected placeholder request before
      | sign request payload digest =>
        exact coin_equal setup selected placeholder _ before
          (RegistrationNativePlatformIdentityCtxMldsaCoins.outgoing setup checks representation created index owner request payload digest before.1.1)
  | inr query =>
    exact congrArg (fun work => work.run before)
      (RegistrationNativeIdentityCensorExternalSource.source_equal setup.joint selected placeholder setup checks representation created (writer query))

/-- Literal publication under another handle preserves every result and the full private source state. -/
theorem program (different : owner.identity.handle ≠ selected)
    (work : OracleComp (RegistrationNativePlatformWriter.Spec E) A) (before : FullState) :
    (simulateQ (callback(false)) work).run before = (simulateQ (callback(true)) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure,StateT.run_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    rw [query_equal setup checks representation created selected index owner placeholder writer different query before]
    apply bind_congr
    intro result
    exact ih result.1 result.2

/-- The actual body includes all mutable writer failures and its charged terminal owner update. -/
theorem bundled (different : owner.identity.handle ≠ selected)
    (scalar : PqxdhJointGapDh.ScalarBytes) (before : FullState) :
    (source(false, Main (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar writer))).run before =
      (source(true, Main (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar writer))).run before := by
  rw [RegistrationNativePlatformIdentityCtxBundleScope.bundled_fold,
    RegistrationNativeIdentityCensorSourceFold.bind_source,RegistrationNativeIdentityCensorSourceFold.bind_source,
    StateT.run_bind,StateT.run_bind,
    RegistrationNativeIdentityCensorSourceFold.publication,RegistrationNativeIdentityCensorSourceFold.publication]
  rw [program setup checks representation created selected index owner placeholder writer different]
  apply bind_congr
  intro result
  rw [RegistrationNativeIdentityCensorBundleTerminal.source,RegistrationNativeIdentityCensorBundleTerminal.source]

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionOtherBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionOtherBundle.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionOtherBundle.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionOtherBundle.bundled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPreselectionOtherBundle.bundled
