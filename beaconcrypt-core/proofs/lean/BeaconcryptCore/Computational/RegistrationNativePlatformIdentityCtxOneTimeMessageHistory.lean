-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleMessageScope
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningHistoryFrame
/-! A newly successful one-time source signing message is the actual operand fixed by its source tree. The proof follows literal request/reply history updates, including absent replies, arbitrary handles and failed publication. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOneTimeMessageHistory
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativePlatformIdentityCtxSource (State implementation)
open PqxdhDynamicIdentityPool (SourceState DynamicSpec record)
open RegistrationNativePlatformIdentityCtxSigningHistoryFrame (messages poolMessages)
open RegistrationNativePlatformIdentityCtxBundleMessageScope (UsesSourceMessage)
variable {A : Type}

private theorem record_sign (identity handle : Nat) (message : Pqxdh.Bytes)
    (reply : Option PqxdhEd25519EufCma.Ed25519Signature) (before : SourceState) :
    poolMessages identity (record (.inr (.service handle (.sign message))) reply before) =
      poolMessages identity before ++
        (if handle=identity then match reply with | none => [] | some _ => [message] else []) := by
  by_cases same : handle=identity
  · cases reply <;> simp only [poolMessages,record,RegistrationNativeIdentityHistory.history,List.filterMap_append,
      List.filterMap_cons,RegistrationNativeIdentityHistory.entry,same,ite_true,List.filterMap_nil,
      PqxdhJointIdentity.signedMessages,PqxdhJointIdentity.requestEvent,List.append_nil]
  · cases reply <;> simp only [poolMessages,record,RegistrationNativeIdentityHistory.history,List.filterMap_append,
      List.filterMap_cons,RegistrationNativeIdentityHistory.entry,same,ite_false,List.filterMap_nil,List.append_nil]

private theorem record_keeps (identity handle : Nat) (fixed message : Pqxdh.Bytes)
    (reply : Option PqxdhEd25519EufCma.Ed25519Signature) (before : SourceState)
    (allowed : RegistrationNativeIdentitySigningRole.oneTime message=true → message=fixed)
    (wanted : Pqxdh.Bytes)
    (member : wanted ∈ poolMessages identity (record (.inr (.service handle (.sign message))) reply before))
    (oneTime : RegistrationNativeIdentitySigningRole.oneTime wanted=true) :
    wanted ∈ poolMessages identity before ∨ wanted=fixed := by
  rw [record_sign,List.mem_append] at member
  rcases member with earlier | added
  · exact Or.inl earlier
  · split at added
    · cases reply with
      | none => cases added
      | some signature =>
          simp only [List.mem_singleton] at added
          subst wanted
          exact Or.inr (allowed oneTime)
    · cases added

private theorem unchanged (joint : PqxdhJointIdentity.Primitives) (identity : Nat) (fixed : Pqxdh.Bytes)
    (request : Spec.Domain) (allowed : RegistrationNativePlatformIdentityCtxSigningHistoryFrame.NoSignFor identity request)
    (before : State) (result : Spec.Range request × State)
    (supported : result ∈ support ((implementation joint request).run before))
    (wanted : Pqxdh.Bytes) (member : wanted ∈ messages identity result.2)
    (_oneTime : RegistrationNativeIdentitySigningRole.oneTime wanted=true) :
    wanted ∈ messages identity before ∨ wanted=fixed := by
  rw [RegistrationNativePlatformIdentityCtxSigningHistoryFrame.query joint identity request allowed before result supported] at member
  exact Or.inl member

/-- Each actual source reply adds only its literal signing operand to the corresponding successful history. -/
theorem query (joint : PqxdhJointIdentity.Primitives) (identity : Nat) (fixed : Pqxdh.Bytes)
    (request : Spec.Domain) (allowed : UsesSourceMessage fixed request)
    (before : State) (result : Spec.Range request × State)
    (supported : result ∈ support ((implementation joint request).run before))
    (wanted : Pqxdh.Bytes) (member : wanted ∈ messages identity result.2)
    (oneTime : RegistrationNativeIdentitySigningRole.oneTime wanted=true) :
    wanted ∈ messages identity before ∨ wanted=fixed := by
  rcases request with ((coin | request) | report) | bytes
  · exact unchanged joint identity fixed (.inl (.inl (.inl coin))) trivial before result supported wanted member oneTime
  · cases request with
    | create => exact unchanged joint identity fixed (.inl (.inl (.inr .create))) trivial before result supported wanted member oneTime
    | reveal handle => exact unchanged joint identity fixed (.inl (.inl (.inr (.reveal handle)))) trivial before result supported wanted member oneTime
    | service handle request => cases request with
      | staticDh peer => exact unchanged joint identity fixed (.inl (.inl (.inr (.service handle (.staticDh peer))))) trivial before result supported wanted member oneTime
      | sign message =>
          simp only [implementation,StateT.run,support_map] at supported
          obtain ⟨returned,called,rfl⟩ := supported
          simp only [RegistrationNativeIdentityMainSource.implementation,PqxdhDynamicIdentityPool.lazyImpl,
            PqxdhDynamicIdentityPool.poolImpl,mem_support_pure_iff] at called
          cases called
          exact record_keeps identity handle fixed message _ before.1 allowed wanted member oneTime
  · exact unchanged joint identity fixed (.inl (.inr report)) trivial before result supported wanted member oneTime
  · exact unchanged joint identity fixed (.inr bytes) trivial before result supported wanted member oneTime

/-- Every adaptive source continuation retains the same one-time operand restriction in its successful history. -/
theorem program (joint : PqxdhJointIdentity.Primitives) (identity : Nat) (fixed : Pqxdh.Bytes)
    (work : OracleComp Spec A) (allowed : work.AllQueriesSatisfy (UsesSourceMessage fixed))
    (before : State) (result : A × State)
    (supported : result ∈ support ((simulateQ (implementation joint) work).run before))
    (wanted : Pqxdh.Bytes) (member : wanted ∈ messages identity result.2)
    (oneTime : RegistrationNativeIdentitySigningRole.oneTime wanted=true) :
    wanted ∈ messages identity before ∨ wanted=fixed := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      exact Or.inl member
  | query_bind request next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at allowed
      rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
      obtain ⟨middle,called,continued⟩ := supported
      rcases ih middle.1 (allowed.2 middle.1) middle.2 result continued member with earlier | same
      · exact query joint identity fixed request allowed.1 before middle called wanted earlier oneTime
      · exact Or.inr same

/-- A genuine first history crossing identifies the exact one-time source message without guessing within the callback. -/
theorem crossing (joint : PqxdhJointIdentity.Primitives) (identity : Nat) (fixed : Pqxdh.Bytes)
    (work : OracleComp Spec A) (allowed : work.AllQueriesSatisfy (UsesSourceMessage fixed))
    (before : State) (result : A × State)
    (supported : result ∈ support ((simulateQ (implementation joint) work).run before))
    (wanted : Pqxdh.Bytes) (fresh : wanted ∉ messages identity before)
    (member : wanted ∈ messages identity result.2)
    (oneTime : RegistrationNativeIdentitySigningRole.oneTime wanted=true) : wanted=fixed :=
  (program joint identity fixed work allowed before result supported wanted member oneTime).resolve_left fresh

section Actual
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

/-- A captured bundle's newly signed one-time message is its original source tuple operand, regardless of public writer success. -/
theorem bundled (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))) = .ok started)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged started)
    (before : RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (result : RustM (Option (alloc.vec.Vec U8)) × RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (supported : result ∈ support ((RegistrationNativePlatformIdentityCtxMain.interpret setup.joint
      (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
        (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar writer))).run before))
    (identity : Nat) (wanted : Pqxdh.Bytes) (fresh : wanted ∉ messages identity before.2)
    (member : wanted ∈ messages identity result.2.2)
    (oneTime : RegistrationNativeIdentitySigningRole.oneTime wanted=true) :
    wanted=PqxdhRefinement.absBytes started.message.one_time_key := by
  simp only [RegistrationNativePlatformIdentityCtxMain.interpret,StateT.run,support_map] at supported
  obtain ⟨inner,reached,rfl⟩ := supported
  exact crossing setup.joint identity _ _
    (RegistrationNativePlatformIdentityCtxBundleMessageScope.bundled setup checks representation created index owner scalar writer started built tagged before.1)
    before.2 inner reached wanted fresh member oneTime

end Actual
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOneTimeMessageHistory

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOneTimeMessageHistory.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOneTimeMessageHistory.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOneTimeMessageHistory.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOneTimeMessageHistory.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOneTimeMessageHistory.crossing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOneTimeMessageHistory.crossing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOneTimeMessageHistory.bundled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOneTimeMessageHistory.bundled
