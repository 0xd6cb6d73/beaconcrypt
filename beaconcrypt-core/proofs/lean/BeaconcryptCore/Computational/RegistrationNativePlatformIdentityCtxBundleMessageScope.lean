-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleSigningHandle
import BeaconcryptCore.Computational.RegistrationNativePlatformOneTimeOperandLineage
/-! Actual source publication requests retain the one-time message of their original captured tuple. Primitive replies, key gates, writer failures and final owner effects remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleMessageScope
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativePlatformIdentityCtxMain (M)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def UsesSourceMessage (message : Pqxdh.Bytes) : Spec.Domain → Prop
  | .inl (.inl (.inr (.service _ (.sign current)))) =>
      RegistrationNativeIdentitySigningRole.oneTime current = true → current = message
  | _ => True

def UsesRequestMessage (message : Pqxdh.Bytes) : RegistrationBeaconInitExecutor.Spec.Domain → Prop
  | .inr request => RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = true →
      TranscriptAuthParts.absSlice request.message = message
  | _ => True

private theorem coin_only (message : Pqxdh.Bytes) (query : Spec.Domain)
    (allowed : RegistrationNativePlatformIdentityCtxMldsaCoins.Coin query) : UsesSourceMessage message query := by
  unfold UsesSourceMessage
  split
  · exact allowed.elim
  · trivial

variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)

/-- Every actual outgoing Ed leaf preserves its current source message, with both public-key gate outcomes retained. -/
theorem outgoing (message : Pqxdh.Bytes) (request : RegistrationBeaconInitExecutor.Spec.Domain)
    (allowed : UsesRequestMessage message request)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (RegistrationNativePlatformIdentityProgram.native
        (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
          setup source index owner request))).run before).AllQueriesSatisfy (UsesSourceMessage message) := by
  cases request with
  | inl request => cases request with
    | hash request =>
      change ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
        (RegistrationNativePlatformIdentityProgram.native (RegistrationNativeIdentityFrontend.hash request))).run before).AllQueriesSatisfy _
      rw [RegistrationNativePlatformIdentityCtxHashOutgoing.outgoing, allQueriesSatisfy_query_bind_iff]
      exact ⟨trivial, fun _ => trivial⟩
    | sign request payload digest =>
      exact (RegistrationNativePlatformIdentityCtxMldsaCoins.outgoing setup checks representation created index owner request payload digest before).mono
        (coin_only message)
  | inr request =>
    rw [RegistrationNativePlatformIdentityCtxEdOutgoing.outgoing]
    unfold RegistrationNativePlatformIdentityCtxEdOutgoing.expected
    split
    · rw [allQueriesSatisfy_query_bind_iff]
      exact ⟨allowed, fun _ => trivial⟩
    · trivial

/-- The actual stateful publication dictionary forwards this same message and gives the mutable writer only its own coins. -/
theorem callback
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (message : Pqxdh.Bytes) (query : (RegistrationNativePlatformWriter.Spec E).Domain)
    (allowed : RegistrationNativePlatformOneTimeOperandLineage.UsesMessage (E := E) message query)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
        setup index owner writer query)).run before).AllQueriesSatisfy (UsesSourceMessage message) := by
  cases query with
  | inl query => exact outgoing setup checks representation created index owner message query (by cases query <;> exact allowed) before
  | inr query =>
    exact (RegistrationNativeIdentityCensorExternalSource.coin_only setup checks representation created (writer query) before).mono
      (coin_only message)

/-- Literal source publication preserves role-one-time operands through all adaptive reply and mutable-writer branches. -/
theorem publication
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (message : Pqxdh.Bytes) (work : OracleComp (RegistrationNativePlatformWriter.Spec E) A)
    (allowed : work.AllQueriesSatisfy (RegistrationNativePlatformOneTimeOperandLineage.UsesMessage (E := E) message))
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (simulateQ (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
        setup index owner writer) work)).run before).AllQueriesSatisfy (UsesSourceMessage message) := by
  rw [RegistrationNativePlatformIdentityCtxOutgoingFold.publication]
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact allQueriesSatisfy_bind
      (callback setup checks representation created index owner writer message query allowed.1 before)
      (fun result => ih result.1 (allowed.2 result.1) result.2)

/-- Every actual captured body has only the original tuple's one-time message at role-one-time source signing leaves, even when publication fails. -/
theorem bundled (scalar : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))) = .ok started)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged started)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (RegistrationNativePlatformIdentityBundle.bundled (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
        setup index owner scalar writer)).run before).AllQueriesSatisfy
          (UsesSourceMessage (PqxdhRefinement.absBytes started.message.one_time_key)) := by
  rw [RegistrationNativePlatformIdentityCtxBundleScope.bundled_fold, StateT.run_bind]
  apply allQueriesSatisfy_bind
    (publication setup checks representation created index owner writer _ _
      (RegistrationNativePlatformOneTimeOperandLineage.begin_allowed _ _ _ _ _ started built tagged) before)
  intro reached
  rw [RegistrationNativeIdentityCensorBundleTerminal.next_run]
  trivial

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleMessageScope

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleMessageScope.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleMessageScope.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleMessageScope.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleMessageScope.callback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleMessageScope.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleMessageScope.publication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleMessageScope.bundled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleMessageScope.bundled
