-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleReceipt
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixOwned
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleTypedKeyCapture
/-! The first-issued branch of the original final-owner cover supplies the same public bundle cutoff, genuine source history freshness and generated row in the actual normalized marked interpreter. This is a source support join, not an initialized security bound. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedPrefix
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxMain (Full interpret)
open RegistrationNativePlatformIdentityCtxLifecycle (Owned)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reserve
local notation "actual" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "current(" placeholder ")" => RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve placeholder

local notation "signed" => RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint actual
local notation "WholeState" => RegistrationNativePlatformIdentityCtxKeyJournal.Whole n KemSK Platform source
local notation "drop" => RegistrationNativePlatformIdentityCtxKeyJournal.drop
local notation "FullState" => RegistrationNativeIdentityCensorEdOutgoingSource.Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source)
local notation "Cut" => RegistrationNativeIdentityCensorBundlePrefix.Cut
local notation "stop" => RegistrationNativeIdentityCensorBundlePrefix.stop
local notation "Mode" => RegistrationNativeIdentityCensorCompiler.Mode

def initialMode (before : WholeState) : Mode := {knownInputs := before.2.2.2}

private theorem erase_signing (work : OracleComp TypedSpec A) (before : WholeState) :
    Prod.map id drop <$> (simulateQ signed work).run before =
      (interpret setup.joint (simulateQ actual work)).run (drop before) := by
  rw [RegistrationNativePlatformIdentityCtxProgram.interpret_program]
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query currentState
  simpa only [RegistrationNativePlatformIdentityCtxKeyJournal.drop,interpret,StateT.run,Prod.map_def,id_eq] using
    RegistrationNativePlatformIdentityCtxKeyJournal.query_erasure setup.joint actual query currentState

/-- The original bundle receipt's exact before-state lifts to the real or censored marked prefix, with its entire original continuation and source pool unchanged. -/
theorem receipt (placeholder : Ed25519Signature) (masked : Bool) (selected : Nat)
    (work : OracleComp TypedSpec A) (before : WholeState) (zero : before.1.2.nextBundle = 0)
    (result : A × (WholeState × List (RegistrationNativeStageTrace.Call TypedSpec WholeState)))
    (reached : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler signed) work).run (before,[])))
    (call : RegistrationNativeStageTrace.Call TypedSpec WholeState) (member : call ∈ result.2.2)
    (index : Nat) (queryEq : call.query = .inr (.bundle index)) :
    ∃ next markedResult,
      markedResult ∈ support ((simulateQ (RegistrationNativeIdentityCensorBundlePrefix.marked setup.joint selected call.before.1.2.nextBundle placeholder masked current(placeholder))
        (stop call.before.1.2.nextBundle work 0)).run
          (RegistrationNativeIdentityCensorPrefixOwned.lift placeholder (initialMode before) (drop before))) ∧
      markedResult.1 = RegistrationNativeIdentityCensorBundlePrefix.Cut.bundle index next ∧
      RegistrationNativeIdentityCensorActualHashSource.project markedResult.2 =
        RegistrationNativeIdentityCensorPrefixOwned.view placeholder (drop call.before) := by
  obtain ⟨next,leading,prefixReached,_continued⟩ := RegistrationNativeIdentityCensorBundleReceipt.signed setup.joint actual work before zero result reached
    call member index call.before.1.2.nextBundle queryEq rfl
  have erasedJournal := Set.mem_image_of_mem (Prod.map id Prod.fst) prefixReached
  rw [←support_map,RegistrationNativeStageTrace.erase] at erasedJournal
  have erasedSigning := Set.mem_image_of_mem (Prod.map id drop) erasedJournal
  rw [←support_map,erase_signing setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
    erased helper reserve (stop call.before.1.2.nextBundle work 0) before] at erasedSigning
  obtain ⟨markedResult,called,sameCut,sameState⟩ := RegistrationNativeIdentityCensorPrefixOwned.from_original setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve selected call.before.1.2.nextBundle placeholder masked work 0 (initialMode before)
      (drop before) (Nat.zero_le _) rfl rfl (RegistrationNativeIdentityCensorBundlePrefix.Cut.bundle index next,drop call.before) erasedSigning
  exact ⟨next,markedResult,called,sameCut,sameState⟩


private theorem call_owner (call : RegistrationNativeStageTrace.Call TypedSpec WholeState)
    (executed : RegistrationNativeStageTrace.Executed signed call) (index : Nat)
    (queryEq : call.query = .inr (.bundle index)) (identity : Nat) (message : Pqxdh.Bytes)
    (fresh : message ∉ RegistrationNativePlatformIdentityCtxFirstBundleCut.messages identity call.before)
    (newMessage : message ∈ RegistrationNativePlatformIdentityCtxFirstBundleCut.messages identity call.after) :
    ∃ owner, call.before.1.1.1.beacons[index]? = some owner ∧ owner.identity.handle = identity := by
  rcases call with ⟨query,before,reply,after⟩
  change query = .inr (.bundle index) at queryEq
  subst query
  have native := RegistrationNativePlatformIdentityCtxKeyJournal.query_support setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.bundle index)) before (reply,after) executed
  obtain ⟨owner,found,same,_policy⟩ := RegistrationNativePlatformIdentityCtxBundleTypedKeyCapture.typed_new setup checks wire route representation created credential keys
    failure allocation reserveRegistration reservePeer reserveFrame erased helper writer index (drop before) (reply,drop after) native identity message fresh newMessage
  exact ⟨owner,found,same⟩

variable {V : Type}
/-- The original finite first-issued branch supplies its fresh one-time message at the very same public bundle cutoff. Its exact pool, full warm hash journal and generated row are derived from the actual source execution; no chosen private bad-event stop is introduced. -/
theorem issued (placeholder : Ed25519Signature) (masked : Bool)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (kind : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec kind) V)
    (budget : PqxdhDeploymentInterface.Budget) (before : WholeState)
    (zero : before.1.2.nextBundle = 0) (owned : Owned setup.joint (drop before))
    (result : V × (RegistrationNativeLedger.State × (WholeState × List (RegistrationNativeStageTrace.Call TypedSpec WholeState))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler signed) kind work (before,[])))
    (attempt : RegistrationNativePlatformIdentityCtxCausalAttempt.Attempt setup.joint wire budget result.2.2.2 result.2.2.1)
    (cut : RegistrationNativePlatformIdentityCtxFiniteCover.FirstCut attempt) :
    ∃ next, ∃ (markedResult : Cut (V × RegistrationNativeLedger.State) × FullState),
      markedResult ∈ support ((simulateQ (RegistrationNativeIdentityCensorBundlePrefix.marked setup.joint attempt.finalOwner.identity.handle
          cut.call.before.1.2.nextBundle placeholder masked current(placeholder))
        (stop cut.call.before.1.2.nextBundle (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds kind work) 0)).run
          (RegistrationNativeIdentityCensorPrefixOwned.lift placeholder (initialMode before) (drop before))) ∧
      markedResult.1 = RegistrationNativeIdentityCensorBundlePrefix.Cut.bundle cut.index next ∧
      RegistrationNativeIdentityCensorActualHashSource.project markedResult.2 =
        RegistrationNativeIdentityCensorPrefixOwned.view placeholder (drop cut.call.before) ∧
      markedResult.2.1.2.bundles = cut.call.before.1.2.nextBundle ∧ markedResult.2.1.2.target = none ∧
      RegistrationNativeIdentityCensorPrefixJournal.Aligned markedResult.2.1.2 markedResult.2.2 ∧
      PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime ∉
        PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history attempt.finalOwner.identity.handle markedResult.2.2.pool.transcript) ∧
      (∀ (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source), markedResult.2.1.1.1.beacons[index]? = some owner →
        ∃ seed, markedResult.2.2.pool.seeds[owner.identity.handle]? = some seed ∧ owner.identity.publicIdentity = setup.joint.publicKeys seed) ∧
      (∃ seed, markedResult.2.2.pool.seeds[attempt.finalOwner.identity.handle]? = some seed) := by
  have compiled : ((result.1,result.2.1),result.2.2) ∈ support ((simulateQ (RegistrationNativeStageTrace.handler signed)
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds kind work)).run (before,[])) := by
    rw [RegistrationNativeFullCompiler.compile_run,support_map] at reached
    obtain ⟨packed,called,same⟩ := reached
    have exactState := congrArg (fun after => ((after.1,after.2.1),after.2.2)) same
    change packed = ((result.1,result.2.1),result.2.2) at exactState
    exact exactState ▸ called
  have split : result.2.2.2 = cut.leading ++ cut.call :: (cut.trailing ++ attempt.call :: attempt.trailing) := by
    calc
      result.2.2.2 = attempt.leading ++ attempt.call :: attempt.trailing := attempt.split
      _ = (cut.leading ++ cut.call :: cut.trailing) ++ attempt.call :: attempt.trailing :=
        congrArg (fun leading => leading ++ attempt.call :: attempt.trailing) cut.split
      _ = _ := by rw [List.append_assoc]; rfl
  have member : cut.call ∈ result.2.2.2 := by
    apply (congrArg (fun calls => cut.call ∈ calls) split).mpr
    exact List.mem_append_right _ (List.mem_cons_self)
  obtain ⟨next,markedResult,called,sameCut,sameState⟩ := receipt setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve placeholder masked attempt.finalOwner.identity.handle _ before zero _ compiled cut.call member cut.index cut.queryEq
  have status := RegistrationNativeIdentityCensorBundlePrefix.status setup.joint attempt.finalOwner.identity.handle cut.call.before.1.2.nextBundle placeholder masked
    current(placeholder) (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds kind work) 0
    (RegistrationNativeIdentityCensorPrefixOwned.lift placeholder (initialMode before) (drop before)) (Nat.zero_le _) rfl rfl rfl markedResult called
  rw [sameCut] at status
  have poolEq := congrArg (fun after => after.2.1) sameState
  change markedResult.2.2.pool = cut.call.before.2.1 at poolEq
  have rows (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (found : markedResult.2.1.1.1.beacons[index]? = some owner) :
      ∃ seed, markedResult.2.2.pool.seeds[owner.identity.handle]? = some seed ∧ owner.identity.publicIdentity = setup.joint.publicKeys seed :=
    RegistrationNativeIdentityCensorPrefixOwned.row setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve attempt.finalOwner.identity.handle cut.call.before.1.2.nextBundle placeholder masked
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds kind work) 0 (initialMode before) (drop before) owned
      (Nat.zero_le _) rfl rfl markedResult called index owner found
  have paths := RegistrationNativePlatformIdentityCtxFiniteCover.full_cut_paths setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds kind work budget before result reached attempt cut
  obtain ⟨captured,found,handle⟩ := call_owner setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
    erased helper reserve cut.call paths.2.1 cut.index cut.queryEq attempt.finalOwner.identity.handle _ cut.fresh cut.signed
  have foundCurrent : markedResult.2.1.1.1.beacons[cut.index]? = some (RegistrationNativeIdentityHistoryView.owner placeholder captured) := by
    have ownersEq := congrArg (fun after => after.1.1.beacons) sameState
    change markedResult.2.1.1.1.beacons = RegistrationNativeIdentityHistoryView.owners placeholder cut.call.before.1.1.1.beacons at ownersEq
    rw [ownersEq,RegistrationNativeIdentityHistoryView.owners,List.getElem?_map,found,Option.map_some]
  obtain ⟨seed,stored,_public⟩ := rows cut.index (RegistrationNativeIdentityHistoryView.owner placeholder captured) foundCurrent
  refine ⟨next,markedResult,called,sameCut,sameState,status.1,status.2.1,status.2.2,?_,rows,seed,?_⟩
  · rw [poolEq]
    exact cut.fresh
  · simpa only [RegistrationNativeIdentityHistoryView.owner,handle] using stored

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedPrefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedPrefix.receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedPrefix.receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedPrefix.issued' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedPrefix.issued
