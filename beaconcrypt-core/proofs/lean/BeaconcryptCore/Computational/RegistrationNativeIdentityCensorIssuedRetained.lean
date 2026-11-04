-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedImageSurvival
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleRetainedJournal
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedJournalSurvival
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleReceipt
/-! The exact canonical issued image bounds a retained observation of the same first-bundle poststate and later packet. The real/censored distribution comparison keeps their source-history crossing jointly. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedRetained
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxKeyJournal (Whole drop owners)
open RegistrationNativeStageTrace (Call Path Executed)
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


local notation "project" => RegistrationNativeIdentityCensorActualHashSource.project
local notation "originalProject(" placeholder ")" => RegistrationNativeIdentityCensorNormalizedJournal.project placeholder
local notation "typed(" serverKeyId "," bounds "," mode "," work ")" =>
  RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work
local notation "markedPrefix(" selected "," position "," placeholder ")" =>
  RegistrationNativeIdentityCensorIssuedPrefixImage.markedPrefix setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder


local notation "target" => RegistrationNativeIdentityCensorVisitorCanonicalJournal.getTarget (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source)
local notation "published" => RegistrationNativeIdentityCensorAdaptivePostselection.published (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source)
local notation "retained(" selected "," position "," placeholder "," masked ")" =>
  RegistrationNativeIdentityCensorBundleBoundaryPair.retained setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder masked

omit primitives in
def Good (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (seed : PqxdhJointIdentity.IdentitySeed) (before : FullState)
    (result : Option ((RustM (Option Pqxdh.Bytes) × FullState) × Option RegistrationNativeIdentityCensorPacketClient.Found)) : Prop :=
  result.elim False (fun result=>∃ wanted packet,result.2=some (wanted,packet) ∧
    RegistrationNativeIdentitySigningRole.oneTime wanted=true ∧
    wanted∉RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages selected before.2.pool ∧
    wanted∈RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages selected result.1.2.2.pool ∧
    (RegistrationNativeIdentityCensorPacketClient.candidate joint (joint.publicKeys seed) (some (wanted,packet))).isSome=true)

private theorem retained_source (selected position : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (accept cursor index : Nat) (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec V) (before : FullState) :
    RegistrationNativeIdentityCensorBundleRetainedJournal.retained (canonical selected position placeholder) target published accept cursor index next before=
      retained(selected,position,placeholder,false) accept index next (before,cursor) := by
  unfold RegistrationNativeIdentityCensorBundleRetainedJournal.retained RegistrationNativeIdentityCensorBundleBoundaryPair.retained
  simp only [RegistrationNativeIdentityCensorCanonicalSource.handler,StateT.run,bind_map_left]
  apply bind_congr
  intro kept
  unfold RegistrationNativeIdentityCensorAdaptivePostselection.cut
  split
  · rfl
  · exact congrArg (Functor.map (fun found=>some (kept,found)))
      (RegistrationNativeIdentityCensorVisitorCanonicalJournal.visit_eq setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder accept (next kept.1) kept.2 cursor)

/-- The original canonical image mass is bounded by a retained real-source bundle observation with the same newly signed wanted message and publicly valid packet field. -/
theorem suffix_bound (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (before : Whole n KemSK Platform source) (empty : owners before=[])
    (zero : before.1.2.nextBundle=0) (good : RegistrationNativePlatformIdentityCtxKeyJournal.Good setup.joint before)
    (selected position accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (mark : RegistrationNativeIdentityCensorBundlePrefix.Cut (V × RegistrationNativeLedger.State) ×
      (FullState × List (Call TypedSpec (RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source))))
    (markedReached : mark∈support (markedPrefix(selected,position,placeholder) (typed(serverKeyId,bounds,mode,work)) before))
    (seed : PqxdhJointIdentity.IdentitySeed) (row : mark.2.1.2.pool.seeds[selected]?=some seed)
    (index : Nat) (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec (V × RegistrationNativeLedger.State))
    (cutKind : mark.1=RegistrationNativeIdentityCensorBundlePrefix.Cut.bundle index next) :
    Pr{let result ← (RegistrationNativeIdentityCensorVisitorJournal.full (canonical selected position placeholder)
      (RegistrationNativeIdentityCensorBundlePrefix.resume mark.1) mark.2.1)}[
        RegistrationNativeIdentityCensorIssuedCanonicalImage.Event setup checks wire route representation created credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder budget accept (typed(serverKeyId,bounds,mode,work)) before (some (mark,result))] ≤
    Pr{let result ← (retained(selected,position,placeholder,false) accept index next
      (mark.2.1,RegistrationNativeIdentityCensorVisitorFold.count mark.2.2))}[Good setup.joint selected seed mark.2.1 result] := by
  classical
  let implementation : QueryImpl TypedSpec (StateT FullState ProbComp) := canonical selected position placeholder
  let cursor := RegistrationNativeIdentityCensorVisitorFold.count mark.2.2
  let glue := fun result : (TypedSpec.Range (.inr (.bundle index)) × FullState) ×
      ((V × RegistrationNativeLedger.State) × (FullState × List (Call TypedSpec FullState)))=>
    (result.2.1,(result.2.2.1,(⟨.inr (.bundle index),mark.2.1,result.1.1,result.1.2⟩ : Call TypedSpec FullState)::result.2.2.2))
  have fullLaw : RegistrationNativeIdentityCensorVisitorJournal.full implementation
      (RegistrationNativeIdentityCensorBundlePrefix.resume mark.1) mark.2.1=
      glue <$>RegistrationNativeIdentityCensorBundleRetainedJournal.complete implementation index next mark.2.1 := by
    rw [cutKind,RegistrationNativeIdentityCensorBundlePrefix.resume,RegistrationNativeIdentityCensorBundleRetainedJournal.full_step]
    simp only [RegistrationNativeIdentityCensorBundleRetainedJournal.complete,map_bind,bind_pure_comp,Functor.map_map]
    rfl
  rw [fullLaw,prEvent_map,←retained_source setup checks route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder accept cursor index next mark.2.1]
  have observation := RegistrationNativeIdentityCensorBundleRetainedJournal.source implementation target published accept cursor index next mark.2.1
  rw [←observation (Good setup.joint selected seed mark.2.1),prEvent_map]
  apply prEvent_mono_of_support
  intro result reached failed
  have fullReached : glue result∈support (RegistrationNativeIdentityCensorVisitorJournal.full implementation
      (RegistrationNativeIdentityCensorBundlePrefix.resume mark.1) mark.2.1) := by
    rw [fullLaw,support_map]
    exact ⟨result,reached,rfl⟩
  obtain ⟨wanted,packet,found,role,fresh,valid,newly⟩ := RegistrationNativeIdentityCensorIssuedImageSurvival.fold setup checks route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve serverKeyId bounds mode work budget before empty zero good selected position accept placeholder mark markedReached
      (glue result) fullReached seed row failed
  have member := newly (⟨.inr (.bundle index),mark.2.1,result.1.1,result.1.2⟩ : Call TypedSpec FullState) result.2.2.2 rfl
  change RegistrationNativeIdentityCensorVisitorJournal.fold target published accept cursor
    ((⟨.inr (.bundle index),mark.2.1,result.1.1,result.1.2⟩ : Call TypedSpec FullState)::result.2.2.2)=some (wanted,packet) at found
  simp only [RegistrationNativeIdentityCensorVisitorJournal.fold,RegistrationNativeIdentityCensorAdaptivePostselection.attempt,
    RegistrationNativeIdentityCensorPublicClient.IsAccept,ite_false,Nat.add_zero] at found
  cases stopped : published (.inr (.bundle index)) result.1.1 result.1.2 with
  | true=>simp only [stopped,ite_true] at found;cases found
  | false=>
    simp only [stopped,Bool.false_eq_true,ite_false] at found
    simp only [RegistrationNativeIdentityCensorBundleRetainedJournal.observe,stopped,Bool.false_eq_true,ite_false,Good,Option.elim_some]
    exact ⟨wanted,packet,found,role,fresh,member,valid⟩

/-- The same original image pays the censored retained observation with its full first-bundle poststate unchanged. -/
theorem censored_suffix_bound (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (before : Whole n KemSK Platform source) (empty : owners before=[])
    (zero : before.1.2.nextBundle=0) (good : RegistrationNativePlatformIdentityCtxKeyJournal.Good setup.joint before)
    (selected position accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (mark : RegistrationNativeIdentityCensorBundlePrefix.Cut (V × RegistrationNativeLedger.State) ×
      (FullState × List (Call TypedSpec (RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source))))
    (markedReached : mark∈support (markedPrefix(selected,position,placeholder) (typed(serverKeyId,bounds,mode,work)) before))
    (seed : PqxdhJointIdentity.IdentitySeed) (row : mark.2.1.2.pool.seeds[selected]?=some seed)
    (index : Nat) (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec (V × RegistrationNativeLedger.State))
    (cutKind : mark.1=RegistrationNativeIdentityCensorBundlePrefix.Cut.bundle index next) :
    Pr{let result ← (RegistrationNativeIdentityCensorVisitorJournal.full (canonical selected position placeholder)
      (RegistrationNativeIdentityCensorBundlePrefix.resume mark.1) mark.2.1)}[
        RegistrationNativeIdentityCensorIssuedCanonicalImage.Event setup checks wire route representation created credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder budget accept (typed(serverKeyId,bounds,mode,work)) before (some (mark,result))] ≤
    Pr{let result ← (retained(selected,position,placeholder,true) accept index next
      (mark.2.1,RegistrationNativeIdentityCensorVisitorFold.count mark.2.2))}[Good setup.joint selected seed mark.2.1 result] := by
  have result := suffix_bound setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper reserve serverKeyId bounds mode work budget before empty zero good selected position accept placeholder mark markedReached seed row index next cutKind
  have underlying := Set.mem_image_of_mem (Prod.map id Prod.fst) markedReached
  rw [←support_map,RegistrationNativeIdentityCensorIssuedPrefixImage.markedPrefix,RegistrationNativeObservedStageTrace.erase] at underlying
  have status := RegistrationNativeIdentityCensorBundlePrefix.status setup.joint selected position placeholder true
    (RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve placeholder)
    (typed(serverKeyId,bounds,mode,work)) 0
    (RegistrationNativeIdentityCensorPrefixOwned.lift placeholder
      ({knownInputs:=before.2.2.2} : RegistrationNativeIdentityCensorCompiler.Mode) (drop before)) (Nat.zero_le position) rfl rfl rfl (mark.1,mark.2.1) underlying
  have ordinal : mark.2.1.1.2.bundles=position := by simpa only [cutKind,RegistrationNativeIdentityCensorBundlePrefix.Status] using status.1
  have coherence := RegistrationNativeIdentityCensorIssuedCanonicalImage.ready setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder (typed(serverKeyId,bounds,mode,work)) before mark markedReached seed row
  rw [RegistrationNativeIdentityCensorBundleBoundaryPair.paired_joint setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder accept index next
      (mark.2.1,RegistrationNativeIdentityCensorVisitorFold.count mark.2.2) ordinal status.2.1
        (coherence.2.1.symm.trans status.2.1) seed row] at result
  exact result

abbrev Mark (A : Type) := RegistrationNativeIdentityCensorBundlePrefix.Cut A ×
  (FullState × List (Call TypedSpec (RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)))
abbrev Kept := Option ((RustM (Option Pqxdh.Bytes) × FullState) × Option RegistrationNativeIdentityCensorPacketClient.Found)

noncomputable def run (selected position accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (masked : Bool) {A : Type} (work : OracleComp TypedSpec A) (before : Whole n KemSK Platform source) :
    ProbComp (Option (Mark (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) A × PqxdhJointIdentity.IdentitySeed × Kept (n := n) (KemSK := KemSK) (Platform := Platform) (source := source))) := do
  let mark←markedPrefix(selected,position,placeholder) work before
  match mark.2.1.2.pool.seeds[selected]? with
  | none=>pure none
  | some seed=>match mark.1 with
    | .returned _=>pure none
    | .bundle index next=>do
      let kept←retained(selected,position,placeholder,masked) accept index next
        (mark.2.1,RegistrationNativeIdentityCensorVisitorFold.count mark.2.2)
      pure (some (mark,seed,kept))

omit primitives in
def Event (joint : PqxdhJointIdentity.Primitives) (selected : Nat) {A : Type}
    (result : Option (Mark (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) A × PqxdhJointIdentity.IdentitySeed × Kept (n := n) (KemSK := KemSK) (Platform := Platform) (source := source))) : Prop :=
  result.elim False (fun result=>Good joint selected result.2.1 result.1.2.1 result.2.2)

/-- The whole actual original first-issued cutoff event is bounded by a censored retained observation. Every selected row, before-b history and first-bundle poststate is taken from that same execution. -/
theorem bound (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (before : Whole n KemSK Platform source) (empty : owners before=[])
    (zero : before.1.2.nextBundle=0) (good : RegistrationNativePlatformIdentityCtxKeyJournal.Good setup.joint before)
    (selected position accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature) :
    Pr{let result←(RegistrationNativeIdentityCensorIssuedCutProbability.coupled setup.joint frontend position (typed(serverKeyId,bounds,mode,work)) before)}[
      RegistrationNativeIdentityCensorIssuedCutProbability.Matched setup.joint wire budget selected accept position result] ≤
    Pr{let result←(run setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position accept placeholder true (typed(serverKeyId,bounds,mode,work)) before)}[Event setup.joint selected result] := by
  classical
  apply (RegistrationNativeIdentityCensorIssuedCanonicalImage.bound setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder (typed(serverKeyId,bounds,mode,work)) before good budget accept).trans
  unfold RegistrationNativeIdentityCensorIssuedCanonicalImage.canonicalJoint run
  apply prEvent_bind_mono_of_forall_le_of_support
  intro mark markedReached
  cases row : mark.2.1.2.pool.seeds[selected]? with
  | none=>simp only [Event,Option.elim_none,prEvent_pure,RegistrationNativeIdentityCensorIssuedCanonicalImage.Event,ite_false];exact le_rfl
  | some seed=>
    cases cutKind : mark.1 with
    | returned value=>
      simp only [RegistrationNativeIdentityCensorBundlePrefix.resume,simulateQ_pure,StateT.run_pure,bind_pure_comp,
        map_pure,Event,Option.elim_none]
      apply prEvent_pure_mono
      intro failed
      obtain ⟨original,_reached,matched,same⟩ := failed
      obtain ⟨_attempt,_handle,_accept,_issued,_bundle,next,kind,_before⟩ := matched
      have kinds := congrArg (fun shared=>shared.1.1) same
      change original.1.1=mark.1 at kinds
      rw [kind,cutKind] at kinds
      cases kinds
    | bundle index next=>
      simp only [bind_pure_comp,prEvent_map,Event,Option.elim_some]
      have branch := censored_suffix_bound setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        serverKeyId bounds mode work budget before empty zero good selected position accept placeholder mark markedReached seed row index next cutKind
      simpa only [RegistrationNativeIdentityCensorVisitorJournal.full,cutKind,RegistrationNativeIdentityCensorBundlePrefix.resume] using branch

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedRetained
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedRetained.suffix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedRetained.suffix_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedRetained.censored_suffix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedRetained.censored_suffix_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedRetained.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedRetained.bound
