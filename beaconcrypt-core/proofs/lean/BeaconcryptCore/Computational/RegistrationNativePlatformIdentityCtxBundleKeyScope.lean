-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformWriterKeyPolicy
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyHistory
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleSigningHandle
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleKeyScope
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativePlatformIdentityCtxMain (M)
open RegistrationNativePlatformIdentityCtxKeyHistory (Legal)
open RegistrationNativePlatformWriterKeyPolicy (AllowedQuery)
open PqxdhEd25519EufCma (X25519PublicKey)
variable {n : Nat} {I KemSK Platform E A B Q : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source} {queries : OracleSpec Q}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
local notation "prekey" => PqxdhPhase2InputBytes.word owner.prekeyPublic
local notation "pq" => owner.kemPublic
private theorem coin_legal (handle : Nat) (pre : X25519PublicKey) (kem : PqxdhKemIndCca.MlKem768PublicKey)
    (query : Spec.Domain) (coin : RegistrationNativePlatformIdentityCtxMldsaCoins.Coin query) : Legal handle pre kem query := by
  unfold Legal
  split
  · exact coin.elim
  · trivial

/-- The actual outgoing dictionary forwards exactly its source message family to the captured generated handle. -/
theorem outgoing (request : RegistrationBeaconInitExecutor.Spec.Domain)
    (allowed : AllowedQuery (E := E) prekey pq (.inl request))
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (RegistrationNativePlatformIdentityProgram.native
        (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
          setup source index owner request))).run before).AllQueriesSatisfy (Legal owner.identity.handle prekey pq) := by
  cases request with
  | inl request => cases request with
    | hash request =>
      change ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
        (RegistrationNativePlatformIdentityProgram.native (RegistrationNativeIdentityFrontend.hash request))).run before).AllQueriesSatisfy _
      rw [RegistrationNativePlatformIdentityCtxHashOutgoing.outgoing, allQueriesSatisfy_query_bind_iff]
      exact ⟨trivial, fun _ => trivial⟩
    | sign request payload digest =>
      exact (RegistrationNativePlatformIdentityCtxMldsaCoins.outgoing setup checks representation created index owner request payload digest before).mono
        (coin_legal owner.identity.handle prekey pq)
  | inr request =>
    rw [RegistrationNativePlatformIdentityCtxEdOutgoing.outgoing]
    unfold RegistrationNativePlatformIdentityCtxEdOutgoing.expected
    split
    · rw [allQueriesSatisfy_query_bind_iff]
      exact ⟨fun _ => allowed, fun _ => trivial⟩
    · trivial

/-- Dynamic source writer callbacks preserve the exact fixed-key signing scope, including all allocator failures. -/
theorem callback (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (request : (RegistrationNativePlatformWriter.Spec E).Domain) (allowed : AllowedQuery (E := E) prekey pq request)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
        setup index owner writer request)).run before).AllQueriesSatisfy (Legal owner.identity.handle prekey pq) := by
  cases request with
  | inl request => exact outgoing setup checks representation created index owner request allowed before
  | inr request =>
    exact (RegistrationNativeIdentityCensorExternalSource.coin_only setup checks representation created (writer request) before).mono
      (coin_legal owner.identity.handle prekey pq)

private theorem program_safe (handle : Nat) (pre : X25519PublicKey) (kem : PqxdhKemIndCca.MlKem768PublicKey)
    (input : queries.Domain → Prop) (implementation : QueryImpl queries (M n KemSK Platform source))
    (safe : ∀ query, input query → ∀ before, ((implementation query).run before).AllQueriesSatisfy (Legal handle pre kem))
    (work : OracleComp queries A) (allowed : work.AllQueriesSatisfy input)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((simulateQ implementation work).run before).AllQueriesSatisfy (Legal handle pre kem) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact allQueriesSatisfy_bind (safe query allowed.1 before) (fun result => ih result.1 (allowed.2 result.1) result.2)

/-- Lowering the literal source publication keeps the exact allowed prekey/PQ message family under every reached primitive and writer reply. -/
theorem publication (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (RegistrationNativePlatformWriter.Spec E) A)
    (allowed : work.AllQueriesSatisfy (AllowedQuery (E := E) prekey pq))
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (simulateQ (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
        setup index owner writer) work)).run before).AllQueriesSatisfy (Legal owner.identity.handle prekey pq) := by
  rw [RegistrationNativePlatformIdentityCtxOutgoingFold.publication]
  exact program_safe owner.identity.handle prekey pq _ _ (callback setup checks representation created index owner writer) work allowed before

/-- The actual captured bundle's fixed keys are derived from its own immutable source inputs, with all failed publication prefixes and complete platform state retained. -/
theorem bundled (scalar : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (RegistrationNativePlatformIdentityBundle.bundled (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
        setup index owner scalar writer)).run before).AllQueriesSatisfy (Legal owner.identity.handle prekey pq) := by
  rw [RegistrationNativePlatformIdentityCtxBundleScope.bundled_fold, StateT.run_bind]
  apply allQueriesSatisfy_bind (publication setup checks representation created index owner writer _ ?_ before)
  · intro reached
    rw [RegistrationNativeIdentityCensorBundleTerminal.next_run]
    trivial
  · apply RegistrationNativePlatformWriterKeyPolicy.begin_all prekey pq _ _ _ _ (setup.dh.publicKey scalar)
    · rfl
    · exact PqxdhRootTableInitialization.rootArray_bytes _
    · simp [RegistrationNativeIdentityFrontend.inputs, RegistrationNativeBeaconFrontend.pqArray, PqxdhRefinement.absBytes, List.map_map, Function.comp_def]

/-- A genuinely new source signing message identifies its exact captured handle and both fixed source keys, before any writer or later publication outcome. -/
theorem new_message (scalar : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (before : RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (result : RustM (Option (alloc.vec.Vec U8)) × RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (supported : result ∈ support ((RegistrationNativePlatformIdentityCtxMain.interpret setup.joint
      (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
        (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar writer))).run before))
    (identity : Nat) (message : Pqxdh.Bytes)
    (fresh : message ∉ RegistrationNativePlatformIdentityCtxSigningHistoryFrame.messages identity before.2)
    (signed : message ∈ RegistrationNativePlatformIdentityCtxSigningHistoryFrame.messages identity result.2.2) :
    owner.identity.handle = identity ∧ RegistrationNativeEdKeyPolicy.Allowed prekey pq message := by
  have matching := RegistrationNativePlatformIdentityCtxSigningHistoryFrame.owner setup checks representation created
    index owner scalar writer before result supported identity message fresh signed
  refine ⟨matching, ?_⟩
  subst identity
  simp only [RegistrationNativePlatformIdentityCtxMain.interpret, StateT.run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  rcases RegistrationNativePlatformIdentityCtxKeyHistory.program setup.joint owner.identity.handle prekey pq
    ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar writer)).run before.1)
    (bundled setup checks representation created index owner scalar writer before.1) before.2 inner reached message signed with earlier | allowed
  · exact False.elim (fresh earlier)
  · exact allowed
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleKeyScope

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleKeyScope.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleKeyScope.outgoing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleKeyScope.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleKeyScope.callback
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleKeyScope.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleKeyScope.publication
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleKeyScope.bundled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleKeyScope.bundled
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleKeyScope.new_message' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleKeyScope.new_message
