-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealSigning
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherOwnerSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdNonselectedSource

/-! An actual publication under a different opaque owner handle has the complete original source marginal before target selection. Inactive entry is retained by each current callback, including missing signing rows, hash cache hits and mutable writer failure. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNonselectedOriginal
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (placeholder : Ed25519Signature)
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "action(" query ")" => Main (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup index owner writer query)
local notation "callback(" censored ")" => (fun query => interpret setup.joint selected placeholder censored (action(query)))
local notation "original" => (fun query => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (action(query)))

private theorem coin_noHash (query : RegistrationNativePlatformIdentityCtxCompiler.Spec.Domain)
    (coin : RegistrationNativePlatformIdentityCtxMldsaCoins.Coin query) : RegistrationNativeIdentityCensorRealSigning.NoHash query := by
  rcases query with ((coin | request) | report) | bytes
  · trivial
  · exact False.elim coin
  · exact False.elim coin
  · exact False.elim coin

private def close (result : ((A × (RegistrationNativeIdentityMain.State n KemSK mlSource × Platform)) ×
    RegistrationNativeIdentityCensorCompiler.Mode) × RegistrationNativeIdentityCensorSource.State) : A × (Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :=
  (result.1.1.1, ((result.1.1.2, result.1.2), result.2))
private theorem closed (censored : Bool) (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A) (before : (Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))) :
    (interpret setup.joint selected placeholder censored work).run before =
      close <$> RegistrationNativeIdentityCensorMldsaOutgoingSource.run setup.joint selected placeholder censored
        (work.run before.1.1) before.1.2 before.2 := by
  simp only [interpret, StateT.run, RegistrationNativeIdentityCensorMldsaOutgoingSource.run, bind_pure_comp]
  rfl

private theorem coin_mode (censored : Bool) (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A) (before : (Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)))
    (allowed : (work.run before.1.1).AllQueriesSatisfy RegistrationNativePlatformIdentityCtxMldsaCoins.Coin)
    (result : A × (Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))) (supported : result ∈ support ((interpret setup.joint selected placeholder censored work).run before)) :
    result.2.1.2 = before.1.2 := by
  rw [closed, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have retained := RegistrationNativeIdentityCensorMldsaOutgoingSource.uniform_frame setup.joint selected placeholder censored _ allowed
    before.1.2 before.2 inner reached
  exact congrArg Prod.fst retained

private theorem query_source (query : (RegistrationNativePlatformWriter.Spec E).Domain)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (inactive : before.1.2.active = false) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> ((callback(false)) query).run before =
      (original query).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  cases query with
  | inl query => cases query with
    | inr request => exact RegistrationNativeIdentityCensorRealSigning.outgoing setup checks representation created selected index owner request placeholder before
    | inl query => cases query with
      | hash request =>
        exact RegistrationNativeIdentityCensorActualHashSource.inactive setup checks representation created selected placeholder request before inactive
      | sign request payload digest =>
        exact RegistrationNativeIdentityCensorRealSigning.main setup.joint selected placeholder _ before
          ((RegistrationNativePlatformIdentityCtxMldsaCoins.outgoing setup checks representation created index owner request payload digest before.1.1).mono coin_noHash)
  | inr query =>
    exact RegistrationNativeIdentityCensorRealSigning.main setup.joint selected placeholder _ before
      ((RegistrationNativeIdentityCensorExternalSource.coin_only setup checks representation created (writer query) before.1.1).mono coin_noHash)

private theorem query_holds (different : owner.identity.handle ≠ selected)
    (query : (RegistrationNativePlatformWriter.Spec E).Domain)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (inactive : before.1.2.active = false)
    (result : (RegistrationNativePlatformWriter.Spec E).Range query × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (reached : result ∈ support (((callback(false)) query).run before)) : result.2.1.2.active = false := by
  cases query with
  | inl query => cases query with
    | inr request =>
      have retained := RegistrationNativeIdentityCensorEdNonselectedSource.frame setup checks representation created selected index owner request placeholder
        false before different result reached
      exact (congrArg (fun value => value.1.active) retained).trans inactive
    | inl query => cases query with
      | hash request =>
        have retained := RegistrationNativeIdentityCensorHashFrame.outgoing setup checks representation created selected placeholder request false before result reached
        exact (congrArg (fun value => value.1.active) retained).trans inactive
      | sign request payload digest =>
        have retained := coin_mode setup selected placeholder false _ before
          (RegistrationNativePlatformIdentityCtxMldsaCoins.outgoing setup checks representation created index owner request payload digest before.1.1) result reached
        exact (congrArg RegistrationNativeIdentityCensorCompiler.Mode.active retained).trans inactive
  | inr query =>
    have retained := coin_mode setup selected placeholder false _ before
      (RegistrationNativeIdentityCensorExternalSource.coin_only setup checks representation created (writer query) before.1.1) result reached
    exact (congrArg RegistrationNativeIdentityCensorCompiler.Mode.active retained).trans inactive

/-- The complete adaptive publication tree under another opaque handle preserves the original native source marginal from inactive entry. -/
theorem program (different : owner.identity.handle ≠ selected) (work : OracleComp (RegistrationNativePlatformWriter.Spec E) A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (inactive : before.1.2.active = false) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> (simulateQ (callback(false)) work).run before =
      (simulateQ original work).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [← query_source setup checks representation created selected index owner placeholder writer query before inactive, bind_map_left]
    apply bind_congr_of_forall_mem_support
    intro result reached
    exact ih result.1 result.2
      (query_holds setup checks representation created selected index owner placeholder writer different query before inactive result reached)


end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNonselectedOriginal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNonselectedOriginal.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNonselectedOriginal.program
