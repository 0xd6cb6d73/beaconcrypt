-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCanonicalImage
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedJournalSurvival
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleReceipt
/-! The actual canonical source-image event reaches the original packet at the same public acceptance ordinal. Every suffix split and cursor is derived from its original cutoff and chronological image. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedImageSurvival
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

omit primitives in
private theorem count_map (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (calls : List (Call TypedSpec (Whole n KemSK Platform source))) :
    RegistrationNativeIdentityCensorVisitorFold.count (calls.map (RegistrationNativeObservedStageTrace.mapCall (RegistrationNativeIdentityCensorNormalizedJournal.project placeholder)))=
      RegistrationNativeIdentityCensorVisitorFold.count calls := by
  simp only [RegistrationNativeIdentityCensorVisitorFold.count,RegistrationNativeIdentityUnissuedCutTrace.count,List.map_map]
  rfl

omit primitives in
private theorem packet_complete (joint : PqxdhJointIdentity.Primitives) (identity : PqxdhJointIdentity.PublicIdentity)
    (packet : registration.InitPacket) (decoded : PqxdhEd25519EufCma.Phase1KeyTuple)
    (accepted : PqxdhEd25519EufCma.acceptPhase1Candidate joint.verify (RegistrationRootInput.candidate packet)=some (identity.ed25519,decoded)) :
    (RegistrationNativeIdentityCensorPacketClient.candidate joint identity (some (PqxdhEd25519EufCma.oneTimeMessage decoded.oneTime,packet))).isSome=true := by
  obtain ⟨_,pq,pre,ot,pqAttached,_pqValid,preAttached,_preValid,otAttached,otValid⟩ :=
    PqxdhEd25519EufCma.acceptPhase1Candidate_some_witness joint.verify (RegistrationRootInput.candidate packet) identity.ed25519 decoded accepted
  have member : (⟨PqxdhEd25519EufCma.oneTimeMessage decoded.oneTime,ot⟩ : PqxdhJointIdentity.Forgery)∈
      PqxdhJointPhase1Reports.candidateFields (RegistrationRootInput.candidate packet) := by
    simp only [PqxdhJointPhase1Reports.candidateFields,pqAttached,preAttached,otAttached,List.filterMap_cons,
      PqxdhEd25519EufCma.splitAttachedSignature_attach,Option.map_some,List.filterMap_nil,List.mem_cons,List.not_mem_nil,or_false]
    exact Or.inr (Or.inr trivial)
  obtain ⟨candidate,chosen,_⟩ := RegistrationNativeIdentityCensorStoppedReduction.choose_complete joint identity
    (PqxdhEd25519EufCma.oneTimeMessage decoded.oneTime) _ _ member rfl otValid
  simp only [RegistrationNativeIdentityCensorPacketClient.candidate,RegistrationNativeIdentityCensorStoppedReduction.packet,
    Option.bind_some,chosen,Option.isSome_some]


/-- Exact original/canonical journal images derive the SAME original accepted packet and public all-attempt acceptance cursor. -/
theorem fold (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (before : Whole n KemSK Platform source) (empty : owners before=[])
    (zero : before.1.2.nextBundle=0) (good : RegistrationNativePlatformIdentityCtxKeyJournal.Good setup.joint before)
    (selected position accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (mark : RegistrationNativeIdentityCensorBundlePrefix.Cut (V × RegistrationNativeLedger.State) ×
      (FullState × List (Call TypedSpec (RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source))))
    (markedReached : mark∈support (markedPrefix(selected,position,placeholder) (typed(serverKeyId,bounds,mode,work)) before))
    (finished : (V × RegistrationNativeLedger.State) × (FullState × List (Call TypedSpec FullState)))
    (called : finished∈support ((simulateQ (RegistrationNativeStageTrace.handler (canonical selected position placeholder))
      (RegistrationNativeIdentityCensorBundlePrefix.resume mark.1)).run (mark.2.1,[])))
    (seed : PqxdhJointIdentity.IdentitySeed) (row : mark.2.1.2.pool.seeds[selected]?=some seed)
    (failed : RegistrationNativeIdentityCensorIssuedCanonicalImage.Event setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder budget accept (typed(serverKeyId,bounds,mode,work)) before (some (mark,finished))) :
    ∃ target packet,
      RegistrationNativeIdentityCensorVisitorJournal.fold RegistrationNativeIdentityCensorVisitorCanonicalJournal.getTarget
        RegistrationNativeIdentityCensorAdaptivePostselection.published accept
        (RegistrationNativeIdentityCensorVisitorFold.count mark.2.2) finished.2.2=some (target,packet) ∧
      RegistrationNativeIdentitySigningRole.oneTime target=true ∧
        target∉RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages selected mark.2.1.2.pool ∧
      (RegistrationNativeIdentityCensorPacketClient.candidate setup.joint (setup.joint.publicKeys seed) (some (target,packet))).isSome=true ∧
      ∀ first rest,finished.2.2=first::rest→
        target∈RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages selected first.after.2.pool := by
  obtain ⟨original,reached,matched,same⟩ := failed
  have full := Set.mem_image_of_mem Prod.snd reached
  rw [←support_map,RegistrationNativeIdentityCensorIssuedCutProbability.full_marginal] at full
  simp only [RegistrationNativeIdentityCensorIssuedCutProbability.coupled,mem_support_bind_iff,mem_support_pure_iff] at reached
  obtain ⟨cut,cutReached,final,continued,rfl⟩ := reached
  obtain ⟨attempt,handle,acceptOrdinal,issued,bundleOrdinal,_oldNext,_oldKind,_oldBefore⟩ := matched
  have split : final.2.2=issued.cut.leading++issued.cut.call::(issued.cut.trailing++attempt.call::attempt.trailing) := by
    calc
      final.2.2=attempt.leading++attempt.call::attempt.trailing := attempt.split
      _=(issued.cut.leading++issued.cut.call::issued.cut.trailing)++attempt.call::attempt.trailing :=
        congrArg (fun leading=>leading++attempt.call::attempt.trailing) issued.cut.split
      _=_ := by rw [List.append_assoc];rfl
  obtain ⟨next,kind,beforeEq,prefixEq⟩ := RegistrationNativeIdentityCensorBundleReceipt.signed_at_cut_journal setup.joint frontend position
    (typed(serverKeyId,bounds,mode,work)) before zero cut cutReached final continued issued.cut.call issued.cut.leading
      (issued.cut.trailing++attempt.call::attempt.trailing) split issued.cut.index issued.cut.queryEq bundleOrdinal
  have prefixImage := congrArg Prod.fst same
  have kindImage := congrArg Prod.fst prefixImage
  have markKind : mark.1=RegistrationNativeIdentityCensorBundlePrefix.Cut.bundle issued.cut.index next := kindImage.symm.trans kind
  have logImage := congrArg (fun prefixState=>prefixState.2.2) prefixImage
  change cut.2.2.map (RegistrationNativeObservedStageTrace.mapCall originalProject(placeholder))=mark.2.2 at logImage
  have markLog : mark.2.2=issued.cut.leading.map (RegistrationNativeObservedStageTrace.mapCall originalProject(placeholder)) :=
    logImage.symm.trans (congrArg (List.map (RegistrationNativeObservedStageTrace.mapCall originalProject(placeholder))) prefixEq)
  have tailImage := congrArg (fun joint=>joint.2.2.2) same
  change final.2.2.map (RegistrationNativeObservedStageTrace.mapCall originalProject(placeholder))=
    mark.2.2++finished.2.2.map (RegistrationNativeObservedStageTrace.mapCall project) at tailImage
  rw [markLog] at tailImage
  have mappedSplit := congrArg (List.map (RegistrationNativeObservedStageTrace.mapCall originalProject(placeholder))) split
  simp only [List.map_append,List.map_cons] at mappedSplit
  have suffixImage : finished.2.2.map (RegistrationNativeObservedStageTrace.mapCall project)=
      (issued.cut.call::(issued.cut.trailing++attempt.call::attempt.trailing)).map (RegistrationNativeObservedStageTrace.mapCall originalProject(placeholder)) :=
    by simpa only [List.map_cons,List.map_append] using (List.append_cancel_left (mappedSplit.symm.trans tailImage)).symm
  have rawReached : (final.1.1,(final.1.2,final.2))∈support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (before,[])) := by
    rw [RegistrationNativeFullCompiler.compile_run,support_map]
    exact ⟨final,full,rfl⟩
  have underlying := Set.mem_image_of_mem (Prod.map id Prod.fst) markedReached
  rw [←support_map,RegistrationNativeIdentityCensorIssuedPrefixImage.markedPrefix,RegistrationNativeObservedStageTrace.erase] at underlying
  have status := RegistrationNativeIdentityCensorBundlePrefix.status setup.joint selected position placeholder true
    (RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve placeholder)
    (typed(serverKeyId,bounds,mode,work)) 0
    (RegistrationNativeIdentityCensorPrefixOwned.lift placeholder
      ({knownInputs:=before.2.2.2} : RegistrationNativeIdentityCensorCompiler.Mode) (drop before)) (Nat.zero_le position) rfl rfl rfl (mark.1,mark.2.1) underlying
  have ordinal : mark.2.1.1.2.bundles=position := by simpa only [markKind,RegistrationNativeIdentityCensorBundlePrefix.Status] using status.1
  have coherence := RegistrationNativeIdentityCensorIssuedCanonicalImage.ready setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder (typed(serverKeyId,bounds,mode,work)) before mark markedReached seed row
  have path := RegistrationNativeStageTrace.path (canonical selected position placeholder)
    (RegistrationNativeIdentityCensorBundlePrefix.resume mark.1) mark.2.1 finished called
  have packet := RegistrationNativeIdentityCensorIssuedJournalSurvival.survives setup checks route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve serverKeyId bounds mode work budget before empty
    (final.1.1,(final.1.2,final.2)) rawReached attempt issued position placeholder seed
    (by simpa only [handle] using path) suffixImage ordinal status.2.1 coherence.2.1 (by simpa only [handle] using row)
  have cursor : RegistrationNativeIdentityCensorVisitorFold.count mark.2.2=RegistrationNativeIdentityCensorVisitorFold.count issued.cut.leading := by
    rw [markLog]
    exact count_map placeholder _
  have poolImage := congrArg (fun prefixState=>prefixState.2.1.2.1) prefixImage
  change cut.2.1.2.1=mark.2.1.2.pool at poolImage
  have fresh : PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime∉RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages selected mark.2.1.2.pool := by
    rw [←poolImage]
    have samePool := congrArg (fun state=>state.2.1) beforeEq
    rw [samePool]
    simpa only [handle,RegistrationNativePlatformIdentityCtxFirstBundleCut.messages,RegistrationNativePlatformIdentityCtxSigningHistoryFrame.messages,RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages] using issued.cut.fresh
  have path := RegistrationNativeStageTrace.path actual (typed(serverKeyId,bounds,mode,work)) before final full
  have memberLeading : issued.cut.call∈attempt.leading :=
    (congrArg (fun calls=>issued.cut.call∈calls) issued.cut.split).mpr (List.mem_append_right _ List.mem_cons_self)
  have member : issued.cut.call∈final.2.2 :=
    (congrArg (fun calls=>issued.cut.call∈calls) attempt.split).mpr (List.mem_append_left _ memberLeading)
  obtain ⟨_leading,_trailing,_split,prior,called,_following⟩ := path.member issued.cut.call member
  have owned := (RegistrationNativePlatformIdentityCtxKeyJournal.path_good setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer prior good).1
  have captured : ∃ owner,(owners issued.cut.call.before)[issued.cut.index]?=some owner ∧owner.identity.handle=attempt.finalOwner.identity.handle := by
    generalize callEq : issued.cut.call=call at called
    have queryEq := issued.cut.queryEq
    rw [callEq] at queryEq
    rcases call with ⟨query,callBefore,reply,callAfter⟩
    change query=.inr (.bundle issued.cut.index) at queryEq
    subst query
    have native := RegistrationNativePlatformIdentityCtxKeyJournal.query_support setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.bundle issued.cut.index)) callBefore (reply,callAfter) called
    have fresh := issued.cut.fresh
    have signed := issued.cut.signed
    rw [callEq] at fresh signed
    obtain ⟨owner,found,sameHandle,_⟩ := RegistrationNativePlatformIdentityCtxBundleTypedKeyCapture.typed_new setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer issued.cut.index (drop callBefore) (reply,drop callAfter) native attempt.finalOwner.identity.handle _ fresh signed
    exact ⟨owner,by simpa only [callEq,owners,drop] using found,sameHandle⟩
  obtain ⟨owner,found,sameHandle⟩ := captured
  change RegistrationNativeIdentityRealization.Owned setup.joint issued.cut.call.before.2.1 (owners issued.cut.call.before) at owned
  obtain ⟨stored,atStored,publicStored⟩ := owned owner (List.mem_of_getElem? found)
  have poolImage := congrArg (fun shared=>shared.1.2.1.2.1) same
  change cut.2.1.2.1=mark.2.1.2.pool at poolImage
  have samePool := congrArg (fun state=>state.2.1) beforeEq
  have rowAt : issued.cut.call.before.2.1.seeds[selected]?=some seed := by
    rw [←samePool,poolImage]
    exact row
  have sameSeed : stored=seed := by
    have storedRow : issued.cut.call.before.2.1.seeds[selected]?=some stored := by simpa only [sameHandle,handle] using atStored
    exact Option.some.inj (storedRow.symm.trans rowAt)
  subst stored
  have keyEq := RegistrationNativePlatformIdentityCtxKeyJournal.full_same_handle setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before empty _ rawReached
      issued.cut.call member issued.cut.index owner found attempt.finalOwner (List.mem_of_getElem? attempt.finalFound) sameHandle.symm
  have identityEq : attempt.finalOwner.identity.publicIdentity=setup.joint.publicKeys seed :=
    (congrArg (fun key=>key.1.publicIdentity) keyEq).trans publicStored
  have accepted := attempt.accepted
  rw [identityEq] at accepted
  have newly : ∀ first rest,finished.2.2=first::rest→
      PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime∈RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages selected first.after.2.pool := by
    intro first rest splitFirst
    have atFirst := suffixImage
    rw [splitFirst] at atFirst
    simp only [List.map_cons,List.cons.injEq] at atFirst
    have afterPool := congrArg (fun call=>call.after.2.1) atFirst.1
    change first.after.2.pool=issued.cut.call.after.2.1 at afterPool
    rw [afterPool]
    simpa only [handle,RegistrationNativePlatformIdentityCtxFirstBundleCut.messages,RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages] using issued.cut.signed
  refine ⟨PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime,attempt.packet,?_,?_,fresh,
    packet_complete setup.joint (setup.joint.publicKeys seed) attempt.packet attempt.decoded accepted,newly⟩
  · simpa only [acceptOrdinal,cursor] using packet
  · simp [RegistrationNativeIdentitySigningRole.oneTime,PqxdhEd25519EufCma.oneTimeMessage]


end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedImageSurvival
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedImageSurvival.fold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedImageSurvival.fold
