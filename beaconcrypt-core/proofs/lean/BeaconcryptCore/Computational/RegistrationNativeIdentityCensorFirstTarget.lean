-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleDispatchSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetOperand
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSampleSource

/-! The literal outer bundle lookup and fresh/supplied scalar dispatch close through the same private source interpretation. Every nontrivial supported outcome has an actual captured owner and an actual supplied or sampled scalar before the original bundled body. No generated-row, freshness or success condition is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstTarget
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {A B : Type}
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
local notation "FullState" => Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "Outcome" => RustM (Option (alloc.vec.Vec U8)) × FullState

variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (selected index : Nat) (placeholder : Ed25519Signature)
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "source(" censored "," work ")" => interpret setup.joint selected placeholder censored work
local notation "body(" owner "," scalar ")" => Main (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar writer)
local notation "draw" => Main (RegistrationNativePlatformIdentityProgram.native
  (RegistrationNativeIdentityFrontend.sample (n := n) (KemSK := KemSK) (Auxiliary := RegistrationServerRoleBackend.State)
    (source := mlSource) PqxdhJointGapDh.sampleScalar))

/-- The armed actual first-signing bundle selects the literal newly signed wanted message, even when later writer or signing paths fail. -/
theorem bundle (wanted : Pqxdh.Bytes) (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (before : FullState) (result : Outcome)
    (armed : before.1.2.armed=true) (missing : before.1.2.target=none) (synced : before.1.2.target=before.2.target)
    (fresh : wanted∉RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages selected before.2.pool)
    (member : wanted∈RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages selected result.2.2.pool)
    (supported : result∈support ((source(false,Main (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer))).run before)) :
    result.2.1.2.target=some wanted ∧ result.2.2.target=some wanted := by
  have held : RegistrationNativeIdentityCensorArmedFresh.Holds selected wanted (before.1.2,before.2) :=
    ⟨armed,synced,fun _=>fresh⟩
  obtain ⟨message,publicTarget,privateTarget⟩ := RegistrationNativeIdentityCensorArmedFresh.main_target setup.joint selected placeholder wanted role
    (Main (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer)) before held result supported member
  rcases RegistrationNativeIdentityCensorBundleDispatchSource.cut setup checks representation created selected index placeholder writer false before result supported with rejected|captured
  · cases rejected
    exact False.elim (fresh member)
  · obtain ⟨owner,scalar,middle,_found,picked,called⟩ := captured
    have framed : middle.1.2=before.1.2 ∧ middle.2.target=before.2.target ∧
        RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages selected middle.2.pool=
          RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages selected before.2.pool := by
      rcases picked with ⟨_phase,sampled⟩|⟨_phase,rfl⟩
      · have same := RegistrationNativeIdentityCensorSampleSource.frame setup checks representation created selected placeholder false
          PqxdhJointGapDh.sampleScalar before (scalar,middle) sampled
        have history := RegistrationNativeIdentityCensorSampleSource.history setup checks representation created selected placeholder false
          PqxdhJointGapDh.sampleScalar before (scalar,middle) sampled
        exact ⟨history.1,congrArg (fun state=>state.2.target) same,
          congrArg PqxdhJointIdentity.signedMessages (history.2.2 selected)⟩
      · exact ⟨rfl,rfl,rfl⟩
    obtain ⟨started,built,tagged⟩ := RegistrationNativeIdentitySigningRole.initial
      ⟨owner.pin.binding⟩ (RegistrationNativeIdentityFrontend.inputs owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩
    have wantedEq := RegistrationNativeIdentityCensorArmedFresh.message_crossing setup.joint selected placeholder
      (PqxdhRefinement.absBytes started.message.one_time_key) wanted role
      (body(owner,scalar)) middle
      (RegistrationNativePlatformIdentityCtxBundleMessageScope.bundled setup checks representation created index owner scalar writer started built tagged middle.1.1)
      (fun old=>fresh (framed.2.2 ▸ old)) result called member
    have middleMissing : middle.1.2.target=none := (congrArg (fun mode=>mode.target) framed.1).trans missing
    have middleSynced : middle.1.2.target=middle.2.target := by rw [framed.1,framed.2.1]; exact synced
    obtain ⟨_messageEq,targets⟩ := RegistrationNativeIdentityCensorTargetOperand.bundled setup checks representation created index owner scalar writer
      started built tagged selected placeholder false middle middleMissing middleSynced result called message privateTarget
    rw [←wantedEq] at targets
    exact targets
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$> work) before=Prod.map change id <$> work before := StateT.run_map change work before

private theorem interpret_map (change : A → B)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A) (before : FullState) :
    (source(false,change <$> work)).run before=Prod.map change id <$> (source(false,work)).run before := by
  simp only [interpret,StateT.run,map_apply,simulateQ_map,bind_pure_comp,Functor.map_map]
  rfl

/-- The same forced first target survives the literal public lifecycle byte conversion. -/
theorem lifecycle (wanted : Pqxdh.Bytes) (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (before : FullState) (result : RustM (Option Pqxdh.Bytes) × FullState)
    (armed : before.1.2.armed=true) (missing : before.1.2.target=none) (synced : before.1.2.target=before.2.target)
    (fresh : wanted∉RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages selected before.2.pool)
    (member : wanted∈RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages selected result.2.2.pool)
    (supported : result∈support ((source(false,RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index)).run before)) :
    result.2.1.2.target=some wanted ∧ result.2.2.target=some wanted := by
  rw [RegistrationNativePlatformIdentityCtxLifecycle.bundle,interpret_map,support_map] at supported
  obtain ⟨⟨raw,after⟩,called,same⟩ := supported
  have afterEq : after=result.2 := congrArg Prod.snd same
  subst after
  exact bundle setup checks representation created selected index placeholder writer wanted role before (raw,result.2)
    armed missing synced fresh member called

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstTarget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstTarget.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstTarget.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstTarget.lifecycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstTarget.lifecycle
