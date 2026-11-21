-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealSigning
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherOwnerSource

/-! A complete source publication that uses only genuine current Ed calls retains its literal original source marginal. The actual source dictionary and reached inactive-target invariant discharge the transport; arbitrary mutable writer state sees the same current bytes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorGenuineOriginal
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativeIdentityCensorOtherOwnerSource (Genuine Holds)
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

private theorem query_source (target : Pqxdh.Bytes) (query : (RegistrationNativePlatformWriter.Spec E).Domain)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (held : Holds target before) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> ((callback(false)) query).run before =
      (original query).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  cases query with
  | inl query => cases query with
    | inr request => exact RegistrationNativeIdentityCensorRealSigning.outgoing setup checks representation created selected index owner request placeholder before
    | inl query => cases query with
      | hash request =>
        exact RegistrationNativeIdentityCensorActualHashSource.inactive setup checks representation created selected placeholder request before held.2
      | sign request payload digest =>
        exact RegistrationNativeIdentityCensorRealSigning.main setup.joint selected placeholder _ before
          ((RegistrationNativePlatformIdentityCtxMldsaCoins.outgoing setup checks representation created index owner request payload digest before.1.1).mono coin_noHash)
  | inr query =>
    exact RegistrationNativeIdentityCensorRealSigning.main setup.joint selected placeholder _ before
      ((RegistrationNativeIdentityCensorExternalSource.coin_only setup checks representation created (writer query) before.1.1).mono coin_noHash)

private theorem query_holds (target : Pqxdh.Bytes) (query : (RegistrationNativePlatformWriter.Spec E).Domain)
    (allowed : Genuine (E := E) selected owner target query)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (held : Holds target before)
    (result : (RegistrationNativePlatformWriter.Spec E).Range query × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (reached : result ∈ support (((callback(false)) query).run before)) : Holds target result.2 := by
  exact RegistrationNativeIdentityCensorOtherOwnerSource.genuine_frame setup checks representation created selected index owner placeholder writer
    target false ((RegistrationNativePlatformWriter.Spec E).query query : OracleComp (RegistrationNativePlatformWriter.Spec E) ((RegistrationNativePlatformWriter.Spec E).Range query))
    ((allQueriesSatisfy_query_iff _ _).mpr allowed) before held result (by simpa only [simulateQ_spec_query] using reached)

private theorem real_program (target : Pqxdh.Bytes) (work : OracleComp (RegistrationNativePlatformWriter.Spec E) A)
    (allowed : work.AllQueriesSatisfy (Genuine (E := E) selected owner target))
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (held : Holds target before) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> (simulateQ (callback(false)) work).run before =
      (simulateQ original work).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [← query_source setup checks representation created selected index owner placeholder writer target query before held, bind_map_left]
    apply bind_congr_of_forall_mem_support
    intro result reached
    exact ih result.1 (allowed.2 result.1) result.2
      (query_holds setup checks representation created selected index owner placeholder writer target query allowed.1 before held result reached)

/-- Actual source request scope proves both canonical and private-censored genuine publication marginals, retaining every failed writer and full shared/private source state. -/
theorem program (censored : Bool) (target : Pqxdh.Bytes) (work : OracleComp (RegistrationNativePlatformWriter.Spec E) A)
    (allowed : work.AllQueriesSatisfy (Genuine (E := E) selected owner target))
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (held : Holds target before) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> (simulateQ (callback(censored)) work).run before =
      (simulateQ original work).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  cases censored with
  | false => exact real_program setup checks representation created selected index owner placeholder writer target work allowed before held
  | true =>
    rw [← RegistrationNativeIdentityCensorOtherOwnerSource.genuine_program setup checks representation created selected index owner placeholder writer target work allowed before held]
    exact real_program setup checks representation created selected index owner placeholder writer target work allowed before held

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorGenuineOriginal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorGenuineOriginal.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorGenuineOriginal.program
