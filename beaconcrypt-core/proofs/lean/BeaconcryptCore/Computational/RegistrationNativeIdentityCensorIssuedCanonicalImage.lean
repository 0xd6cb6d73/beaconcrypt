-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedPrefixImage
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedPrefix
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSyncMain
/-! Original issued image events supply their own selected row at the same actual marked prefix. The remaining plain source suffix is then the exact image of a complete canonical source suffix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCanonicalImage
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeStageTrace (Call Path Executed)
open RegistrationNativeObservedStageTrace (mapCall)
open RegistrationNativePlatformIdentityCtxKeyJournal (Whole drop Good)
open RegistrationNativeIdentityCensorBundlePrefix (Cut stop resume)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
variable (selected position : Nat) (placeholder : Ed25519Signature)

local notation "actual" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper (RegistrationNativePlatformConcreteSource.writer reserve)
local notation "signed" => RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint actual
local notation "FullState" => RegistrationNativeIdentityCensorEdOutgoingSource.Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "WholeState" => Whole n KemSK Platform mlSource
local notation "PlainState" => RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform mlSource
local notation "normalized" => RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve placeholder
local notation "plain" => (fun query => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (normalized query))
local notation "canonical" => RegistrationNativeIdentityCensorCanonicalSource.handler setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder
local notation "project" => RegistrationNativeIdentityCensorActualHashSource.project
local notation "originalProject" => RegistrationNativeIdentityCensorNormalizedJournal.project placeholder


local notation "originalMap" => RegistrationNativeIdentityCensorIssuedImageProbability.originalMap placeholder
local notation "marked" => RegistrationNativeIdentityCensorBundlePrefix.marked setup.joint selected position placeholder true normalized


local notation "writer" => RegistrationNativePlatformConcreteSource.writer reserve
local notation "markedPrefix" => RegistrationNativeIdentityCensorIssuedPrefixImage.markedPrefix setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder
local notation "originalJointMap" => RegistrationNativeIdentityCensorIssuedPrefixImage.originalJointMap placeholder
local notation "markedJointMap" => RegistrationNativeIdentityCensorIssuedPrefixImage.markedJointMap
local notation "markedMap" => RegistrationNativeIdentityCensorIssuedPrefixImage.markedMap

private theorem call_owner (call : Call TypedSpec WholeState) (executed : Executed signed call) (index : Nat)
    (queryEq : call.query=.inr (.bundle index)) (identity : Nat) (message : Pqxdh.Bytes)
    (fresh : message∉RegistrationNativePlatformIdentityCtxFirstBundleCut.messages identity call.before)
    (newMessage : message∈RegistrationNativePlatformIdentityCtxFirstBundleCut.messages identity call.after) :
    ∃ owner,call.before.1.1.1.beacons[index]?=some owner ∧owner.identity.handle=identity := by
  rcases call with ⟨query,before,reply,after⟩
  change query=.inr (.bundle index) at queryEq
  subst query
  have native := RegistrationNativePlatformIdentityCtxKeyJournal.query_support setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.bundle index)) before (reply,after) executed
  obtain ⟨owner,found,same,_policy⟩ := RegistrationNativePlatformIdentityCtxBundleTypedKeyCapture.typed_new setup checks wire route representation created credential keys
    failure allocation reserveRegistration reservePeer reserveFrame erased helper writer index (drop before) (reply,drop after) native identity message fresh newMessage
  exact ⟨owner,found,same⟩

/-- The original matched first-signing cut itself supplies a generated selected row, from actual source ownership and the same executed callback. -/
theorem original_row (work : OracleComp TypedSpec A) (before : WholeState) (good : Good setup.joint before)
    (budget : PqxdhDeploymentInterface.Budget) (accept : Nat)
    (result : (Cut A × (WholeState × List (Call TypedSpec WholeState))) × (A × (WholeState × List (Call TypedSpec WholeState))))
    (reached : result∈support (RegistrationNativeIdentityCensorIssuedCutProbability.coupled setup.joint actual position work before))
    (matched : RegistrationNativeIdentityCensorIssuedCutProbability.Matched setup.joint wire budget selected accept position result) :
    ∃ seed,result.1.2.1.2.1.seeds[selected]?=some seed := by
  have full := Set.mem_image_of_mem Prod.snd reached
  rw [←support_map,RegistrationNativeIdentityCensorIssuedCutProbability.full_marginal] at full
  have path := RegistrationNativeStageTrace.path signed work before result.2 full
  obtain ⟨attempt,sameHandle,_sameAccept,issued,_sameBundle,_next,_sameKind,sameBefore⟩ := matched
  have memberLeading : issued.cut.call∈attempt.leading :=
    (congrArg (fun calls=>issued.cut.call∈calls) issued.cut.split).mpr (List.mem_append_right _ (List.mem_cons_self))
  have member : issued.cut.call∈result.2.2.2 :=
    (congrArg (fun calls=>issued.cut.call∈calls) attempt.split).mpr (List.mem_append_left _ memberLeading)
  obtain ⟨_leading,_trailing,_split,prior,called,_following⟩ := path.member issued.cut.call member
  have owned := (RegistrationNativePlatformIdentityCtxKeyJournal.path_good setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer prior good).1
  obtain ⟨owner,found,handle⟩ := call_owner setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    issued.cut.call called issued.cut.index issued.cut.queryEq attempt.finalOwner.identity.handle _ issued.cut.fresh issued.cut.signed
  change RegistrationNativeIdentityRealization.Owned setup.joint issued.cut.call.before.2.1 issued.cut.call.before.1.1.1.beacons at owned
  obtain ⟨seed,row,_public⟩ := owned owner (List.mem_of_getElem? found)
  have selectedRow : issued.cut.call.before.2.1.seeds[selected]?=some seed := by
    simpa only [handle,sameHandle] using row
  exact ⟨seed,(congrArg (fun state=>state.2.1.seeds[selected]?) sameBefore).trans selectedRow⟩

private theorem marked_support (work : OracleComp TypedSpec A) (before : WholeState)
    (result : Cut A × (FullState × List (Call TypedSpec PlainState)))
    (reached : result∈support (markedPrefix work before)) :
    (result.1,result.2.1)∈support ((simulateQ marked (stop position work 0)).run
      (RegistrationNativeIdentityCensorPrefixOwned.lift placeholder
        ({knownInputs:=before.2.2.2} : RegistrationNativeIdentityCensorCompiler.Mode) (drop before))) := by
  have image := Set.mem_image_of_mem (Prod.map id Prod.fst) reached
  rw [←support_map,RegistrationNativeIdentityCensorIssuedPrefixImage.markedPrefix,RegistrationNativeObservedStageTrace.erase] at image
  exact image

/-- All target coherence needed by the canonical source is derived from the actual before-b prefix; its only row input is the literal lookup at that same reached state. -/
theorem ready (work : OracleComp TypedSpec A) (before : WholeState)
    (result : Cut A × (FullState × List (Call TypedSpec PlainState)))
    (reached : result∈support (markedPrefix work before)) (seed : PqxdhJointIdentity.IdentitySeed)
    (row : result.2.1.2.pool.seeds[selected]?=some seed) :
    RegistrationNativeIdentityCensorCanonicalSource.Ready selected seed result.2.1 := by
  have called := marked_support setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    selected position placeholder work before result reached
  have status := RegistrationNativeIdentityCensorBundlePrefix.status setup.joint selected position placeholder true normalized work 0
    (RegistrationNativeIdentityCensorPrefixOwned.lift placeholder
      ({knownInputs:=before.2.2.2} : RegistrationNativeIdentityCensorCompiler.Mode) (drop before)) (Nat.zero_le position) rfl rfl rfl
      (result.1,result.2.1) called
  have synced := RegistrationNativeIdentityCensorTargetSyncMain.program setup.joint selected position placeholder true normalized (stop position work 0)
    (RegistrationNativeIdentityCensorPrefixOwned.lift placeholder
      ({knownInputs:=before.2.2.2} : RegistrationNativeIdentityCensorCompiler.Mode) (drop before)) rfl (result.1,result.2.1) called
  refine ⟨?_,synced,row⟩
  intro message held
  rw [status.2.1] at held
  cases held

noncomputable def canonicalJoint (work : OracleComp TypedSpec A) (before : WholeState) := do
  let cut ← markedPrefix work before
  match cut.2.1.2.pool.seeds[selected]? with
  | none => pure none
  | some _seed => do
      let final ← (simulateQ (RegistrationNativeStageTrace.handler canonical) (resume cut.1)).run (cut.2.1,[])
      pure (some (cut,final))

def Event (budget : PqxdhDeploymentInterface.Budget) (accept : Nat) (work : OracleComp TypedSpec A) (before : WholeState)
    (result : Option ((Cut A × (FullState × List (Call TypedSpec PlainState))) ×
      (A × (FullState × List (Call TypedSpec FullState))))) : Prop :=
  result.elim False (fun result =>
    ∃ original∈support (RegistrationNativeIdentityCensorIssuedCutProbability.coupled setup.joint actual position work before),
      RegistrationNativeIdentityCensorIssuedCutProbability.Matched setup.joint wire budget selected accept position original ∧
      originalJointMap original=(markedMap result.1,RegistrationNativeIdentityCensorIssuedImageProbability.canonicalImage result.1.2.2 result.2))

private theorem image_row (work : OracleComp TypedSpec A) (before : WholeState) (good : Good setup.joint before)
    (budget : PqxdhDeploymentInterface.Budget) (accept : Nat)
    (markedResult : Cut A × (FullState × List (Call TypedSpec PlainState)))
    (plainResult : A × (PlainState × List (Call TypedSpec PlainState)))
    (failed : ∃ original∈support (RegistrationNativeIdentityCensorIssuedCutProbability.coupled setup.joint actual position work before),
      RegistrationNativeIdentityCensorIssuedCutProbability.Matched setup.joint wire budget selected accept position original ∧
      originalJointMap original=markedJointMap (markedResult,plainResult)) :
    ∃ seed,markedResult.2.1.2.pool.seeds[selected]?=some seed := by
  obtain ⟨original,reached,matched,same⟩ := failed
  obtain ⟨seed,row⟩ := original_row setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    selected position work before good budget accept original reached matched
  have poolSame := congrArg (fun shared => shared.1.2.1.2.1.seeds[selected]?) same
  change original.1.2.1.2.1.seeds[selected]?=markedResult.2.1.2.pool.seeds[selected]? at poolSame
  exact ⟨seed,poolSame.symm.trans row⟩

/-- The whole original issued cutoff event is bounded by the actual full canonical suffix image. Its generated row and target coherence are derived internally from the same prefix; uncreated-row branches cannot contain the original event. -/
theorem bound (work : OracleComp TypedSpec A) (before : WholeState) (good : Good setup.joint before)
    (budget : PqxdhDeploymentInterface.Budget) (accept : Nat) :
    Pr{let result ← (RegistrationNativeIdentityCensorIssuedCutProbability.coupled setup.joint actual position work before)}[
      RegistrationNativeIdentityCensorIssuedCutProbability.Matched setup.joint wire budget selected accept position result] ≤
    Pr{let result ← (canonicalJoint setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position placeholder work before)}[
        Event setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
          selected position placeholder budget accept work before result] := by
  classical
  apply (RegistrationNativeIdentityCensorIssuedPrefixImage.bound setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder work before
      (RegistrationNativeIdentityCensorIssuedCutProbability.Matched setup.joint wire budget selected accept position)).trans
  unfold RegistrationNativeIdentityCensorIssuedPrefixImage.markedPlainJoint canonicalJoint
  apply prEvent_bind_mono_of_forall_le_of_support
  intro cut cutReached
  cases row : cut.2.1.2.pool.seeds[selected]? with
  | none =>
    simp only [bind_pure_comp,prEvent_map,Event,Option.elim_none,prEvent_pure,ite_false]
    apply le_trans (b := Pr{let result ← ((simulateQ (RegistrationNativeStageTrace.handler plain) (resume cut.1)).run (project cut.2.1,cut.2.2))}[False])
    · apply prEvent_mono_of_support
      intro result _reached failed
      obtain ⟨seed,found⟩ := image_row setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        selected position placeholder work before good budget accept cut result failed
      rw [row] at found
      cases found
    · simp only [prEvent_false]
      exact le_rfl
  | some seed =>
    simp only [bind_pure_comp,prEvent_map,Event,Option.elim_some]
    have coherence := ready setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position placeholder work before cut cutReached seed row
    have sourceLaw := RegistrationNativeIdentityCensorIssuedImageProbability.canonical_source setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder (resume cut.1) cut.2.1 cut.2.2 seed coherence
    rw [←sourceLaw,prEvent_map]
    exact le_rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCanonicalImage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCanonicalImage.original_row' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCanonicalImage.original_row
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCanonicalImage.ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCanonicalImage.ready

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCanonicalImage.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCanonicalImage.bound
