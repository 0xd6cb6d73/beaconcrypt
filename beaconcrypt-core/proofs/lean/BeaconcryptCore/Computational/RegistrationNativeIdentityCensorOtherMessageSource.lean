-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherOwnerSource
import BeaconcryptCore.Computational.RegistrationNativePlatformOneTimeOperandLineage

/-! A later source bundle with a different one-time message performs only genuine current Ed calls, even under the selected owner. Actual message lineage supplies that fact from the literal source tree. Full replies, source state, failed writers and terminal phase effects agree; the selected public stop remains inactive. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherMessageSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativeIdentityCensorOtherOwnerSource (Genuine Holds)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}

private theorem genuine_query (selected : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource)
    (target message : Pqxdh.Bytes) (different : target ≠ message)
    (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true)
    (query : (RegistrationNativePlatformWriter.Spec E).Domain)
    (allowed : RegistrationNativePlatformOneTimeOperandLineage.UsesMessage (E := E) message query) :
    Genuine (E := E) selected owner target query := by
  cases query with
  | inr query => trivial
  | inl query => cases query with
    | inl query => trivial
    | inr request =>
      apply Or.inr
      intro same
      have currentRole : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = true := by
        rw [← same]
        exact targetRole
      exact different (same.trans (allowed currentRole))

private theorem genuine_tree (selected : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource)
    (target message : Pqxdh.Bytes) (different : target ≠ message)
    (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true)
    (work : OracleComp (RegistrationNativePlatformWriter.Spec E) A)
    (allowed : work.AllQueriesSatisfy (RegistrationNativePlatformOneTimeOperandLineage.UsesMessage (E := E) message)) :
    work.AllQueriesSatisfy (Genuine (E := E) selected owner target) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed ⊢
    exact ⟨genuine_query selected owner target message different targetRole query allowed.1,
      fun reply => ih reply (allowed.2 reply)⟩

variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (placeholder : Ed25519Signature)
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "FullState" => Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "source(" censored "," work ")" => interpret setup.joint selected placeholder censored work
local notation "tree(" scalar ")" => RegistrationNativePlatformWriter.begin E (pqxdh.BeaconFresh.mk owner.pin.binding)
  (RegistrationNativeIdentityFrontend.inputs owner) (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)))
  owner.pin
local notation "published(" scalar ")" => Main (simulateQ (RegistrationNativePlatformIdentityPublication.callback setup index owner writer) (tree(scalar)))
local notation "body(" scalar ")" => Main (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar writer)

private theorem genuine_source (target : Pqxdh.Bytes) (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true)
    (scalar : PqxdhJointGapDh.ScalarBytes) (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))) = .ok started)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged started)
    (different : target ≠ PqxdhRefinement.absBytes started.message.one_time_key) :
    (tree(scalar)).AllQueriesSatisfy (Genuine (E := E) selected owner target) :=
  genuine_tree selected owner target _ different targetRole _
    (RegistrationNativePlatformOneTimeOperandLineage.begin_allowed _ _ _ _ started built tagged)

/-- The actual source message lineage rules out every omitted signing request for a different one-time message; no private row, success or ownership condition is supplied. -/
theorem publication (target : Pqxdh.Bytes) (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true)
    (scalar : PqxdhJointGapDh.ScalarBytes) (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))) = .ok started)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged started)
    (different : target ≠ PqxdhRefinement.absBytes started.message.one_time_key)
    (before : FullState) (held : Holds target before) :
    (source(false, published(scalar))).run before = (source(true, published(scalar))).run before := by
  rw [RegistrationNativeIdentityCensorSourceFold.publication, RegistrationNativeIdentityCensorSourceFold.publication]
  exact RegistrationNativeIdentityCensorOtherOwnerSource.genuine_program setup checks representation created selected index owner placeholder writer
    target _ (genuine_source setup selected owner target targetRole scalar started built tagged different) before held

/-- The same complete actual bundled body and charged native terminal step agree under both interpretations for every unselected one-time message. -/
theorem bundled (target : Pqxdh.Bytes) (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true)
    (scalar : PqxdhJointGapDh.ScalarBytes) (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))) = .ok started)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged started)
    (different : target ≠ PqxdhRefinement.absBytes started.message.one_time_key)
    (before : FullState) (held : Holds target before) :
    (source(false, body(scalar))).run before = (source(true, body(scalar))).run before := by
  rw [RegistrationNativePlatformIdentityCtxBundleScope.bundled_fold,
    RegistrationNativeIdentityCensorSourceFold.bind_source, RegistrationNativeIdentityCensorSourceFold.bind_source,
    StateT.run_bind, StateT.run_bind]
  rw [publication setup checks representation created selected index owner placeholder writer target targetRole scalar started built tagged different before held]
  apply bind_congr
  intro result
  rw [RegistrationNativeIdentityCensorBundleTerminal.source, RegistrationNativeIdentityCensorBundleTerminal.source]

/-- Different one-time material leaves a previously inactive selected-publication observer inactive, including actual successful writes. -/
theorem inactive (target : Pqxdh.Bytes) (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true)
    (censored : Bool) (scalar : PqxdhJointGapDh.ScalarBytes) (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))) = .ok started)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged started)
    (different : target ≠ PqxdhRefinement.absBytes started.message.one_time_key)
    (before : FullState) (held : Holds target before) (result : RustM (Option (alloc.vec.Vec U8)) × FullState)
    (supported : result ∈ support ((source(censored, body(scalar))).run before)) : result.2.1.2.active = false := by
  rw [RegistrationNativePlatformIdentityCtxBundleScope.bundled_fold, RegistrationNativeIdentityCensorSourceFold.bind_source,
    StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, published, terminal⟩ := supported
  rw [RegistrationNativeIdentityCensorSourceFold.publication] at published
  have current := RegistrationNativeIdentityCensorOtherOwnerSource.genuine_frame setup checks representation created selected index owner placeholder writer
    target censored _ (genuine_source setup selected owner target targetRole scalar started built tagged different) before held middle published
  have unchanged := RegistrationNativeIdentityCensorBundleTerminal.frame setup checks representation created index owner scalar middle.1 selected placeholder censored
    middle.2 result terminal
  exact (congrArg (fun mode => mode.active) unchanged.2.1).trans current.2

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherMessageSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherMessageSource.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherMessageSource.publication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherMessageSource.bundled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherMessageSource.bundled

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherMessageSource.inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherMessageSource.inactive
