-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstTarget
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstUnpublished
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
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstCallback
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
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
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

local notation "normalized(" placeholder "," query ")" => RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation created credential view
  failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve placeholder query

omit primitives in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$> work) before=Prod.map change id <$> work before := StateT.run_map change work before

private theorem normalized_source (selected : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (query : TypedSpec.Domain) (before : FullState) :
    (RegistrationNativeIdentityCensorEdOutgoingSource.interpret setup.joint selected placeholder false (normalized(placeholder,query))).run before=
      Prod.map id (RegistrationNativeIdentityCensorOutgoingView.view placeholder) <$>
        (RegistrationNativeIdentityCensorEdOutgoingSource.interpret setup.joint selected placeholder false (frontend query)).run before := by
  simp only [RegistrationNativeIdentityCensorAdaptivePostselection.normalized,RegistrationNativeIdentityCensorEdOutgoingSource.interpret,
    StateT.run,simulateQ_map,map_apply,bind_pure_comp,Functor.map_map,RegistrationNativeIdentityCensorOutgoingView.view,Prod.map_def,id_eq]

/-- The actual marked, online-normalized first callback selects its newly signed wanted message in both targets at the literal original bundle ordinal. -/
theorem target (selected index position : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (wanted : Pqxdh.Bytes) (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (before after : FullState) (reply : RustM (Option Pqxdh.Bytes))
    (ordinal : before.1.2.bundles=position) (missing : before.1.2.target=none) (synced : before.1.2.target=before.2.target)
    (fresh : wanted∉RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages selected before.2.pool)
    (member : wanted∈RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages selected after.2.pool)
    (supported : (reply,after)∈support (RegistrationNativeIdentityCensorAdaptivePostselection.call setup checks wire route representation created credential view
      failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder false (.inr (.bundle index)) before)) :
    after.1.2.target=some wanted ∧ after.2.target=some wanted := by
  rw [RegistrationNativeIdentityCensorAdaptivePostselection.call,normalized_source,support_map] at supported
  obtain ⟨⟨raw,finished⟩,called,same⟩ := supported
  cases same
  have armed : (RegistrationNativeIdentityCensorAdaptivePostselection.entered position (.inr (.bundle index)) before).1.2.armed=true := by
    simp only [RegistrationNativeIdentityCensorAdaptivePostselection.entered,RegistrationNativeIdentityCensorCompiler.enter,ordinal,beq_self_eq_true]
  exact RegistrationNativeIdentityCensorFirstTarget.lifecycle setup checks representation created selected index placeholder writer wanted role
    (RegistrationNativeIdentityCensorAdaptivePostselection.entered position (.inr (.bundle index)) before)
    (raw,finished) armed missing synced fresh member called

/-- The same original first callback cannot trigger a publication stop, regardless of its canonical normalized poststate. -/
theorem quiet (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (before : Whole n KemSK Platform source) (empty : owners before=[])
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (before,[])))
    (attempt : RegistrationNativePlatformIdentityCtxCausalAttempt.Attempt setup.joint wire budget result.2.2.2 result.2.2.1)
    (issued : RegistrationNativePlatformIdentityCtxFiniteCover.Issued attempt)
    (leading trailing : List (Call TypedSpec (Whole n KemSK Platform source)))
    (index : Nat) (reply : RustM (Option Pqxdh.Bytes)) (first last : Whole n KemSK Platform source)
    (split : attempt.leading=leading++⟨.inr (.bundle index),first,reply,last⟩::trailing)
    (called : (reply,last)∈support ((actual (.inr (.bundle index))).run first))
    (fresh : PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime∉RegistrationNativePlatformIdentityCtxSigningHistoryFrame.messages attempt.finalOwner.identity.handle first.2)
    (signed : PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime∈RegistrationNativePlatformIdentityCtxSigningHistoryFrame.messages attempt.finalOwner.identity.handle last.2)
    (after : FullState) : RegistrationNativeIdentityCensorAdaptivePostselection.published (.inr (.bundle index)) reply after=false := by
  cases reply with
  | fail error | div => simp [RegistrationNativeIdentityCensorAdaptivePostselection.published,RegistrationNativeRawAdapter.resultOption]
  | ok optional => cases optional with
    | none => simp [RegistrationNativeIdentityCensorAdaptivePostselection.published,RegistrationNativeRawAdapter.resultOption]
    | some bytes => exact False.elim (RegistrationNativeIdentityCensorFirstUnpublished.success setup checks route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper reserve serverKeyId bounds mode work budget before empty result reached attempt issued
          leading trailing index bytes first last split called fresh signed)
end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstCallback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstCallback.target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstCallback.target

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstCallback.quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstCallback.quiet
