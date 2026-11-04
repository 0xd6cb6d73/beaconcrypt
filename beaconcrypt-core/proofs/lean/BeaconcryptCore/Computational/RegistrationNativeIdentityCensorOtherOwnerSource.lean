-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOtherSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorHashFrame
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleTerminal

/-! Publications under a different opaque owner handle forward every genuine current request. The actual source dictionary preserves the fixed selected target and inactive flag through all Ed/hash/ML/writer outcomes, so the complete original publication and charged terminal body agree exactly in both private interpretations. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherOwnerSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
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

private theorem coin_mode (censored : Bool) (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A) (before : FullState)
    (allowed : (work.run before.1.1).AllQueriesSatisfy RegistrationNativePlatformIdentityCtxMldsaCoins.Coin)
    (result : A × FullState) (supported : result ∈ support ((source(censored, work)).run before)) :
    result.2.1.2 = before.1.2 := by
  rw [closed, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have retained := RegistrationNativeIdentityCensorMldsaOutgoingSource.uniform_frame setup.joint selected placeholder censored _ allowed
    before.1.2 before.2 inner reached
  exact congrArg Prod.fst retained

def Genuine (target : Pqxdh.Bytes) : (RegistrationNativePlatformWriter.Spec E).Domain → Prop
  | .inl (.inr request) => owner.identity.handle ≠ selected ∨ target ≠ TranscriptAuthParts.absSlice request.message
  | _ => True

private theorem other_genuine (target : Pqxdh.Bytes) (different : owner.identity.handle ≠ selected)
    (query : (RegistrationNativePlatformWriter.Spec E).Domain) : Genuine (E := E) selected owner target query := by
  cases query with
  | inr query => trivial
  | inl query => cases query with
    | inr request => exact Or.inl different
    | inl query => trivial

def Holds (target : Pqxdh.Bytes) (before : FullState) : Prop :=
  before.1.2.target = some target ∧ before.1.2.active = false

private theorem query_equal (target : Pqxdh.Bytes)
    (query : (RegistrationNativePlatformWriter.Spec E).Domain) (allowed : Genuine (E := E) selected owner target query) (before : FullState) (held : Holds target before) :
    ((callback(false)) query).run before = ((callback(true)) query).run before := by
  cases query with
  | inl query => cases query with
    | inr request =>
      exact RegistrationNativeIdentityCensorEdOtherSource.outgoing setup checks representation created selected index owner request placeholder
        before target held.1 allowed
    | inl query => cases query with
      | hash request =>
        exact RegistrationNativeIdentityCensorHashOutgoingSource.hash_same setup checks representation created selected placeholder request before
      | sign request payload digest =>
        exact coin_equal setup selected placeholder _ before
          (RegistrationNativePlatformIdentityCtxMldsaCoins.outgoing setup checks representation created index owner request payload digest before.1.1)
  | inr query =>
    exact congrArg (fun work => work.run before)
      (RegistrationNativeIdentityCensorExternalSource.source_equal setup.joint selected placeholder setup checks representation created (writer query))

private theorem query_holds (target : Pqxdh.Bytes)
    (censored : Bool) (query : (RegistrationNativePlatformWriter.Spec E).Domain) (allowed : Genuine (E := E) selected owner target query) (before : FullState) (held : Holds target before)
    (result : (RegistrationNativePlatformWriter.Spec E).Range query × FullState)
    (supported : result ∈ support (((callback(censored)) query).run before)) : Holds target result.2 := by
  cases query with
  | inl query => cases query with
    | inr request =>
      have retained := RegistrationNativeIdentityCensorEdOtherSource.frame setup checks representation created selected index owner request placeholder
        censored before target held.1 allowed result supported
      have targetEq : result.2.1.2.target = before.1.2.target := congrArg (fun value => value.1.target) retained
      exact ⟨targetEq.trans held.1,
        RegistrationNativeIdentityCensorEdOtherSource.inactive setup checks representation created selected index owner request placeholder
          censored before target held.1 allowed held.2 result supported⟩
    | inl query => cases query with
      | hash request =>
        have retained := RegistrationNativeIdentityCensorHashFrame.outgoing setup checks representation created selected placeholder request censored before result supported
        have targetEq : result.2.1.2.target = before.1.2.target := congrArg (fun value => value.1.target) retained
        have activeEq : result.2.1.2.active = before.1.2.active := congrArg (fun value => value.1.active) retained
        exact ⟨targetEq.trans held.1, activeEq.trans held.2⟩
      | sign request payload digest =>
        have retained := coin_mode setup selected placeholder censored _ before
          (RegistrationNativePlatformIdentityCtxMldsaCoins.outgoing setup checks representation created index owner request payload digest before.1.1) result supported
        change result.2.1.2.target = some target ∧ result.2.1.2.active = false
        rw [retained]
        exact held
  | inr query =>
    have retained := coin_mode setup selected placeholder censored _ before
      (RegistrationNativeIdentityCensorExternalSource.coin_only setup checks representation created (writer query) before.1.1) result supported
    change result.2.1.2.target = some target ∧ result.2.1.2.active = false
    rw [retained]
    exact held

/-- An actual request tree with only genuine current Ed calls has exact real/censored behavior under the fixed target, including all shared writer state. -/
theorem genuine_program (target : Pqxdh.Bytes) (work : OracleComp (RegistrationNativePlatformWriter.Spec E) A)
    (allowed : work.AllQueriesSatisfy (Genuine (E := E) selected owner target)) (before : FullState) (held : Holds target before) :
    (simulateQ (callback(false)) work).run before = (simulateQ (callback(true)) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [query_equal setup checks representation created selected index owner placeholder writer target query allowed.1 before held]
    apply bind_congr_of_forall_mem_support
    intro result reached
    exact ih result.1 (allowed.2 result.1) result.2
      (query_holds setup checks representation created selected index owner placeholder writer target true query allowed.1 before held result reached)

/-- The same syntactically genuine source trees preserve both the selected target and the inactive public stop flag through all failures. -/
theorem genuine_frame (target : Pqxdh.Bytes) (censored : Bool) (work : OracleComp (RegistrationNativePlatformWriter.Spec E) A)
    (allowed : work.AllQueriesSatisfy (Genuine (E := E) selected owner target)) (before : FullState) (held : Holds target before)
    (result : A × FullState) (supported : result ∈ support ((simulateQ (callback(censored)) work).run before)) :
    Holds target result.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact held
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, continued⟩ := supported
    exact ih middle.1 (allowed.2 middle.1) middle.2
      (query_holds setup checks representation created selected index owner placeholder writer target censored query allowed.1 before held middle called)
      result continued

/-- The complete original publication request tree under another handle has identical full private source semantics, including optional failures and dynamic writer state. -/
theorem program (target : Pqxdh.Bytes) (different : owner.identity.handle ≠ selected)
    (work : OracleComp (RegistrationNativePlatformWriter.Spec E) A) (before : FullState) (held : Holds target before) :
    (simulateQ (callback(false)) work).run before = (simulateQ (callback(true)) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [query_equal setup checks representation created selected index owner placeholder writer target query (other_genuine selected owner target different query) before held]
    apply bind_congr_of_forall_mem_support
    intro result reached
    exact ih result.1 result.2
      (query_holds setup checks representation created selected index owner placeholder writer target true query (other_genuine selected owner target different query) before held result reached)

private theorem program_holds (target : Pqxdh.Bytes) (different : owner.identity.handle ≠ selected)
    (censored : Bool) (work : OracleComp (RegistrationNativePlatformWriter.Spec E) A) (before : FullState) (held : Holds target before)
    (result : A × FullState) (supported : result ∈ support ((simulateQ (callback(censored)) work).run before)) :
    Holds target result.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact held
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, continued⟩ := supported
    exact ih middle.1 middle.2
      (query_holds setup checks representation created selected index owner placeholder writer target censored query (other_genuine selected owner target different query) before held middle called)
      result continued

/-- The generic source-dictionary fold is the actual Main publication, not an alternative controller or a supplied callback equation. -/
theorem publication (target : Pqxdh.Bytes) (different : owner.identity.handle ≠ selected)
    (work : OracleComp (RegistrationNativePlatformWriter.Spec E) A) (before : FullState) (held : Holds target before) :
    (source(false, Main (simulateQ (RegistrationNativePlatformIdentityPublication.callback setup index owner writer) work))).run before =
      (source(true, Main (simulateQ (RegistrationNativePlatformIdentityPublication.callback setup index owner writer) work))).run before := by
  rw [RegistrationNativeIdentityCensorSourceFold.publication setup.joint selected placeholder false,
    RegistrationNativeIdentityCensorSourceFold.publication setup.joint selected placeholder true]
  exact program setup checks representation created selected index owner placeholder writer target different work before held

local notation "body(" scalar ")" => Main (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar writer)

/-- Every actual bundled body under another handle retains its exact public result, complete private source state, charged native phase update and P in both interpretations. -/
theorem bundled (target : Pqxdh.Bytes) (different : owner.identity.handle ≠ selected)
    (scalar : PqxdhJointGapDh.ScalarBytes) (before : FullState) (held : Holds target before) :
    (source(false, body(scalar))).run before = (source(true, body(scalar))).run before := by
  rw [RegistrationNativePlatformIdentityCtxBundleScope.bundled_fold,
    RegistrationNativeIdentityCensorSourceFold.bind_source, RegistrationNativeIdentityCensorSourceFold.bind_source,
    StateT.run_bind, StateT.run_bind]
  rw [publication setup checks representation created selected index owner placeholder writer target different _ before held]
  apply bind_congr
  intro result
  rw [RegistrationNativeIdentityCensorBundleTerminal.source, RegistrationNativeIdentityCensorBundleTerminal.source]

/-- A successful publication by another handle remains unselected: it cannot trigger the selected message's public stop. -/
theorem inactive (target : Pqxdh.Bytes) (different : owner.identity.handle ≠ selected)
    (censored : Bool) (scalar : PqxdhJointGapDh.ScalarBytes) (before : FullState) (held : Holds target before)
    (result : RustM (Option (alloc.vec.Vec U8)) × FullState)
    (supported : result ∈ support ((source(censored, body(scalar))).run before)) :
    result.2.1.2.active = false := by
  rw [RegistrationNativePlatformIdentityCtxBundleScope.bundled_fold,
    RegistrationNativeIdentityCensorSourceFold.bind_source, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, published, terminal⟩ := supported
  rw [RegistrationNativeIdentityCensorSourceFold.publication] at published
  have current := program_holds setup checks representation created selected index owner placeholder writer target different censored _ before held middle published
  have unchanged := RegistrationNativeIdentityCensorBundleTerminal.frame setup checks representation created index owner scalar middle.1 selected placeholder censored
    middle.2 result terminal
  exact (congrArg (fun mode => mode.active) unchanged.2.1).trans current.2

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherOwnerSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherOwnerSource.genuine_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherOwnerSource.genuine_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherOwnerSource.genuine_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherOwnerSource.genuine_frame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherOwnerSource.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherOwnerSource.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherOwnerSource.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherOwnerSource.publication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherOwnerSource.bundled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherOwnerSource.bundled

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherOwnerSource.inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherOwnerSource.inactive
