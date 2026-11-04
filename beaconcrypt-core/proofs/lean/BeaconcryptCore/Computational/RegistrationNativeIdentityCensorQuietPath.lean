-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietCallback
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCanonicalSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorFold
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorCanonicalJournal
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTuple
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedOwner
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover
import BeaconcryptCore.Computational.RegistrationNativeStageTraceCut
import BeaconcryptCore.Computational.RegistrationNativeRegistrationMarkCausal
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal
/-! Actual canonical active publication at a projected original callback contradicts the original strict earlier-publication failure through concrete unsigned-tuple readback. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietPath
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxKeyJournal (Whole drop owners)
open RegistrationNativeStageTrace (Call Path Executed)
open RegistrationNativeIdentityBundlePhase (Keeps Closed)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reserve
local notation "wire" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "actual" => RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint frontend


variable {V : Type}
local notation "FullState" => RegistrationNativeIdentityCensorEdOutgoingSource.Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source)

local notation "canonical" => RegistrationNativeIdentityCensorCanonicalSource.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve

/-- Every exact selected-source callback path preserves its target and its original source row. -/
theorem targets (selected position : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (target : Pqxdh.Bytes) (seed : PqxdhJointIdentity.IdentitySeed)
    {before after : FullState} {calls : List (Call TypedSpec FullState)}
    (path : Path (canonical selected position placeholder) before calls after)
    (prior : RegistrationNativeIdentityCensorAdaptivePostselection.Selected selected target seed before) :
    RegistrationNativeIdentityCensorAdaptivePostselection.Selected selected target seed after := by
  induction path with
  | nil => exact prior
  | cons call called rest last following ih =>
      exact ih (RegistrationNativeIdentityCensorAdaptivePostselection.call_selected setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder false call.query target seed
        call.before prior (call.reply,call.after) called)

/-- Equal projected journal entries retain the same public stop decision through their actual selected callback. -/
theorem matched (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (before : Whole n KemSK Platform source) (empty : owners before=[])
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (before,[])))
    (attempt : RegistrationNativePlatformIdentityCtxCausalAttempt.Attempt setup.joint wire budget result.2.2.2 result.2.2.1)
    (issued : RegistrationNativePlatformIdentityCtxFiniteCover.Issued attempt)
    (leading trailing : List (Call TypedSpec (Whole n KemSK Platform source)))
    (original : Call TypedSpec (Whole n KemSK Platform source)) (split : attempt.leading=leading++original::trailing)
    (position : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (current : Call TypedSpec FullState)
    (same : RegistrationNativeObservedStageTrace.mapCall RegistrationNativeIdentityCensorActualHashSource.project current=
      RegistrationNativeObservedStageTrace.mapCall (RegistrationNativeIdentityCensorNormalizedJournal.project placeholder) original)
    (seed : PqxdhJointIdentity.IdentitySeed)
    (selected : RegistrationNativeIdentityCensorAdaptivePostselection.Selected attempt.finalOwner.identity.handle
      (PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime) seed current.before)
    (called : Executed (canonical attempt.finalOwner.identity.handle position placeholder) current) :
    RegistrationNativeIdentityCensorAdaptivePostselection.published current.query current.reply current.after=false := by
  rcases original with ⟨originalQuery,originalBefore,originalReply,originalAfter⟩
  rcases current with ⟨currentQuery,currentBefore,currentReply,currentAfter⟩
  simp only [RegistrationNativeObservedStageTrace.mapCall,Call.mk.injEq] at same
  obtain ⟨queries,beforeSame,replies,_afterSame⟩ := same
  subst currentQuery
  have repliesEq : currentReply=originalReply := eq_of_heq replies
  subst currentReply
  exact RegistrationNativeIdentityCensorQuietCallback.quiet setup checks route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve serverKeyId bounds mode work budget before empty result reached attempt issued
      leading trailing originalQuery originalReply originalBefore originalAfter split position placeholder currentBefore currentAfter beforeSame seed selected called

/-- Every selected canonical source prefix corresponding to original earlier callbacks survives the actual public publication stop. -/
theorem quiet (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (before : Whole n KemSK Platform source) (empty : owners before=[])
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (before,[])))
    (attempt : RegistrationNativePlatformIdentityCtxCausalAttempt.Attempt setup.joint wire budget result.2.2.2 result.2.2.1)
    (issued : RegistrationNativePlatformIdentityCtxFiniteCover.Issued attempt)
    (position : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (seed : PqxdhJointIdentity.IdentitySeed)
    {first last : FullState} {calls : List (Call TypedSpec FullState)}
    (path : Path (canonical attempt.finalOwner.identity.handle position placeholder) first calls last)
    (selected : RegistrationNativeIdentityCensorAdaptivePostselection.Selected attempt.finalOwner.identity.handle
      (PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime) seed first)
    (originals : List (Call TypedSpec (Whole n KemSK Platform source)))
    (aligned : calls.map (RegistrationNativeObservedStageTrace.mapCall RegistrationNativeIdentityCensorActualHashSource.project)=
      originals.map (RegistrationNativeObservedStageTrace.mapCall (RegistrationNativeIdentityCensorNormalizedJournal.project placeholder)))
    (earlier : ∀ original∈originals,original∈attempt.leading) :
    ∀ current∈calls,RegistrationNativeIdentityCensorAdaptivePostselection.published current.query current.reply current.after=false := by
  intro current member
  obtain ⟨_prefix,_suffix,_split,prior,called,_later⟩ := path.member current member
  have selectedAt := targets setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper reserve attempt.finalOwner.identity.handle position placeholder _ seed prior selected
  have mapped : RegistrationNativeObservedStageTrace.mapCall RegistrationNativeIdentityCensorActualHashSource.project current ∈
      originals.map (RegistrationNativeObservedStageTrace.mapCall (RegistrationNativeIdentityCensorNormalizedJournal.project placeholder)) := by
    rw [←aligned]
    exact List.mem_map.mpr ⟨current,member,rfl⟩
  obtain ⟨original,originalMember,same⟩ := List.mem_map.mp mapped
  obtain ⟨leading,trailing,split⟩ := List.mem_iff_append.mp (earlier original originalMember)
  exact matched setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    serverKeyId bounds mode work budget before empty result reached attempt issued leading trailing original split position placeholder current same.symm seed selectedAt called

/-- The same original submitted packet is reached at its actual all-attempt acceptance ordinal after the entire original nonpublishing selected prefix. -/
theorem survives (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (before : Whole n KemSK Platform source) (empty : owners before=[])
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (before,[])))
    (attempt : RegistrationNativePlatformIdentityCtxCausalAttempt.Attempt setup.joint wire budget result.2.2.2 result.2.2.1)
    (issued : RegistrationNativePlatformIdentityCtxFiniteCover.Issued attempt)
    (position : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (seed : PqxdhJointIdentity.IdentitySeed)
    {first last : FullState} {calls : List (Call TypedSpec FullState)}
    (path : Path (canonical attempt.finalOwner.identity.handle position placeholder) first calls last)
    (selected : RegistrationNativeIdentityCensorAdaptivePostselection.Selected attempt.finalOwner.identity.handle
      (PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime) seed first)
    (leading trailing : List (Call TypedSpec FullState)) (call : Call TypedSpec FullState)
    (split : calls=leading++call::trailing)
    (originals : List (Call TypedSpec (Whole n KemSK Platform source)))
    (aligned : leading.map (RegistrationNativeObservedStageTrace.mapCall RegistrationNativeIdentityCensorActualHashSource.project)=
      originals.map (RegistrationNativeObservedStageTrace.mapCall (RegistrationNativeIdentityCensorNormalizedJournal.project placeholder)))
    (earlier : ∀ original∈originals,original∈attempt.leading)
    (accept cursor : Nat) (ordinal : cursor+RegistrationNativeIdentityCensorVisitorFold.count leading=accept)
    (queryEq : call.query=.inr (.accept attempt.packet)) :
    RegistrationNativeIdentityCensorVisitorJournal.fold RegistrationNativeIdentityCensorVisitorCanonicalJournal.getTarget
      RegistrationNativeIdentityCensorAdaptivePostselection.published accept cursor calls=
        some (PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime,attempt.packet) := by
  have fullPath := path
  rw [split] at fullPath
  obtain ⟨beforeAccept,_called,_afterAccept⟩ := RegistrationNativeStageTraceCut.split
    (canonical attempt.finalOwner.identity.handle position placeholder) leading trailing call fullPath
  have selectedAt := targets setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    attempt.finalOwner.identity.handle position placeholder _ seed beforeAccept selected
  have quietAt := quiet setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    serverKeyId bounds mode work budget before empty result reached attempt issued position placeholder seed beforeAccept selected originals aligned earlier
  rw [split]
  exact RegistrationNativeIdentityCensorVisitorFold.survives RegistrationNativeIdentityCensorVisitorCanonicalJournal.getTarget
    RegistrationNativeIdentityCensorAdaptivePostselection.published accept cursor leading trailing call attempt.packet _ ordinal quietAt queryEq selectedAt.1

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietPath

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietPath.targets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietPath.targets

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietPath.matched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietPath.matched

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietPath.quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietPath.quiet

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietPath.survives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietPath.survives
