-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementGame
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceCommonReceipt
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceEarlierBuild
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishGivenSourceCut
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedCallReadback
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningOrigin
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceFinishIssuedSign
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCausalGivenStage
import BeaconcryptCore.Computational.RegistrationNativeResponseStageContents
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementCoverage
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n :Nat} {I KemSK P E R Error :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitives :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto :CryptoOperations (RustT ProbComp)]
variable [originalLocal :LocalOperations (RustT (StateT P ProbComp))]
variable [originalContainers :ContainerOperations (RustT (StateT P ProbComp))]
variable {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
variable (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)
variable [AdapterServerConstructorPrimitive.Standard]
variable {Value AD PT CT :Type}
variable (objects :AdapterServerConstructorObjects.Leaves configuration.views)
variable (ensureInit :StateT Unit ProbComp Bool)
variable (serverEd :AdapterServerConstructorJoint.EdContract configuration.generator configuration.view setup.joint (AdapterServerConstructorStartup.edCore ensureInit))
variable (identityIndex :Nat) (identifier :U64) (rng :R)
variable (bounds :PqxdhDeploymentInterface.FreshBounds) (mode :PqxdhDeploymentInterface.Mode)
variable (adversary :RegistrationNativeExperiment.Public→OracleComp (RegistrationNativePlatformPublicAdapterInterface.ModeSpec mode) Value)
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "AuditState"=>RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source
local notation "wire"=>RegistrationNativeConcreteCodec.wire
local notation "canonical"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "codec"=>RegistrationNativeWire.ledgerCodec canonical

local notation "route"=>RegistrationNativePlatformPublicAdapterRouting.route
local notation "allocation"=>RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin
local notation "helper"=>RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer configuration.reservePackets
local notation "rawAllocation"=>RegistrationNativePlatformConcreteSource.rawAllocation configuration.reserveFrame
local notation "serializer"=>RegistrationNativePlatformConcreteSource.serializer (Platform:=P)
local notation "compiled"=>fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile mode (adversary publication)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
open RegistrationNativePlatformPublicAdapterSourceEvents (Event)
open RegistrationNativeStageTrace (Call Path Executed)
local notation "physical"=>RegistrationNativePlatformPublicAdapterAuditLowModel.physical
local notation "stages"=>RegistrationNativePlatformPublicAdapterSourceAuthentication.stages
local notation "historyFor"=>RegistrationNativePlatformPublicAdapterSourceSigningHistory.history

include objects serverEd in
theorem coverage_with_session_ad (crypto :Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (correct :configuration.keyView.Correct) (previous :P) (budget :PqxdhDeploymentInterface.Budget)
    (bounded :∀publication,RegistrationNativePlatformPublicAdapterInterface.Respects mode budget (adversary publication))
    (functional :PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (result :RegistrationNativeKemRecipientLogSource.Result KemSK
      (Option (RegistrationNativePlatformKemInitializedJournal.History n source Value P)×P) budget.create)
    (supported :result∈support (RegistrationNativePlatformPublicAdapterSourceAgreementGame.experiment (n:=n) configuration ensureInit identityIndex identifier bounds mode adversary previous budget functional))
    (origin :¬RegistrationNativePlatformOrdinaryKemExceptions.OriginCollision source (result.2.1.1.1,result.2.1.2))
    (marker :result.2.2≠true) :
    RegistrationNativePlatformPublicAdapterSourceAgreementGame.HoldsWithSessionAd configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary crypto previous
      (result.2.1.1.1,result.2.1.2) :=by
  classical
  intro outcome sourceSupported compatible
  cases outcome with
  | none=>trivial
  | some selected=>
    obtain ⟨initial,finished⟩:=selected
    let currentHistory:=RegistrationNativePlatformPublicAdapterSourceCommonReceipt.history configuration initial finished
    have returned :result.2.1.1.1.1=some currentHistory:=(congrArg (fun observed=>observed.1.1) compatible).symm
    have platformEq:finished.2.1.1.1.2=result.2.1.1.1.2:=congrArg (fun observed=>observed.1.2) compatible
    have poolEq:finished.2.1.1.1.1.pool=result.2.1.2:=congrArg Prod.snd compatible
    have actualReceipt :∃execution :RegistrationNativePlatformOrdinaryKemHistoryPath.Receipt setup checks wire route configuration.agreement.representation source ensureInit identityIndex identifier
        configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer previous
        currentHistory result.2.1.1.1.2 result.2.1.2,
        execution.initial=initial ∧execution.calls=finished.2.1.1.2.calls ∧execution.finalNative=finished.2.1.1.1.1:=by
      rw [←platformEq,←poolEq]
      exact RegistrationNativePlatformPublicAdapterSourceCommonReceipt.exact_receipt configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary previous initial finished sourceSupported
    obtain ⟨execution,initialEq,callsEq,finalEq⟩:=actualReceipt
    have clean :¬(RegistrationNativeKemClientObservation.BadCalls (KemSK:=KemSK) initial.credential currentHistory.calls ∨
        CacheHasCollision (RegistrationNativeWorldCache.cache finished.2.1.1.1.1)):=by
      simpa only [RegistrationNativePlatformOrdinaryKemExceptions.OriginCollision,returned,currentHistory,
        RegistrationNativePlatformPublicAdapterSourceCommonReceipt.history,RegistrationNativePlatformKemCountedProfile.ofInitial,
        RegistrationNativeKemServerState.toNative,RegistrationNativeKemServerState.ofNative,RegistrationNativeWorldCache.cache] using origin
    have good :¬RegistrationNativePlatformOrdinaryMldsaOriginJournal.BadCalls initial.credential finished.2.1.1.2.calls:=by
      intro bad
      exact clean (Or.inl ((RegistrationNativeKemClientObservation.bad_calls initial.credential finished.2.1.1.2.calls).mpr bad))
    have collisionFree :¬CacheHasCollision (RegistrationNativeWorldCache.cache execution.finalNative):=by
      rw [finalEq]
      exact fun collision=>clean (Or.inr collision)
    obtain ⟨stored,sourceCalls,initialHeld,sourcePath⟩:=RegistrationNativePlatformPublicAdapterSourceCommonReceipt.source_path
      configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary previous initial finished sourceSupported
    intro index input packet application sourceBefore leading finishStages trailing afterObjects afterBackend self pending prekey oneTime kem observed decoded found phase protectedKey
    obtain ⟨prior,later,finishCall,sourceSplit,beforePath,finishedCall,afterPath,beforeLog,queryEq,sourceBeforeEq,sourceReplyEq,sourceBackendEq,openedEq,closedEq,blockEq⟩:=
      RegistrationNativePlatformPublicAdapterLoggedCallbackSpan.span configuration initial.created initial.credential sourcePath
        leading finishStages trailing (.inl (.inr (.finish index input))) sourceBefore (.ok (some application,afterObjects)) afterBackend
        (by simpa only [List.nil_append] using observed)
    rcases finishCall with ⟨query,beforeFinish,reply,afterFinish⟩
    dsimp only at queryEq
    subst query
    have actualReply:=eq_of_heq sourceReplyEq
    have replyEq:reply=some application:=congrArg Prod.fst (RustM.ok.inj actualReply)
    subst reply
    have sourceSelected:beforeFinish.1.2.base.objects.beacons index=some self:=by
      change (physical configuration initial.created initial.credential beforeFinish.1.1 beforeFinish.1.2).beacons index=some self
      rw [sourceBeforeEq]
      exact found
    have finishMember:=RegistrationNativePlatformPublicAdapterTypedCallReadback.finish configuration initial.created initial.credential
      beforeFinish afterFinish index input packet application decoded finishedCall
    have finishMemberFinal:=RegistrationNativePlatformPublicAdapterTypedCallReadback.path_keep configuration initial.created initial.credential afterPath _ finishMember
    have nativeFinishMember :(⟨.inr (.finish index (some packet)),beforeFinish.1.1.1,.ok (some application),afterFinish.1.1.1⟩:
        Call RegistrationNativeRawAdapter.TypedSpec (Native×P))∈execution.calls:=by
      rw [callsEq]
      exact finishMemberFinal
    have beforeHeld:=RegistrationNativePlatformPublicAdapterSourceCommonReceipt.invariant_path configuration initial.created initial.credential beforePath initialHeld
    have logBefore:beforeFinish.2=leading:=by simpa only [List.nil_append] using beforeLog
    obtain ⟨packetWitness,packetOutput⟩:=RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.query_cut configuration initial.created initial.credential
      (.inl (.inr (.finish index input))) beforeFinish (some application,afterFinish) finishedCall
    let incoming:=beforeFinish.2++[Event.opened (.inl (.inr (.finish index input))) (physical configuration initial.created initial.credential beforeFinish.1.1 beforeFinish.1.2)]
    let call:=RegistrationNativePlatformPublicAdapterDispatcher.calls configuration initial.created initial.credential (.inl (.inr (.finish index input))) beforeFinish.1.1 beforeFinish.1.2
    let augmented:=RegistrationNativePlatformPublicAdapterLoggedJoint.augmentation configuration initial.created initial.credential (.inl (.inr (.finish index input))) beforeFinish.1 incoming
    let original:=RegistrationNativePlatformPublicAdapterLoggedRuntime.project call augmented packetWitness
    let answered:=RegistrationNativePlatformPublicAdapterLoggedRuntime.answer call original
    change (some application,afterFinish)=(answered.1,(answered.2,packetWitness.val.2++[Event.closed (.inl (.inr (.finish index input)))
      (.ok (answered.1,RegistrationNativePlatformPublicAdapterSourceRuntime.objects (physical configuration initial.created initial.credential answered.2.1 answered.2.2)))
      (physical configuration initial.created initial.credential answered.2.1 answered.2.2).backend])) at packetOutput
    have packetReply:answered.1=some application:=(congrArg Prod.fst packetOutput).symm
    have actualPublic:=call.reply original.val original.property (RegistrationNativePlatformExtractedSdkPublic.returned call original)
      (RegistrationNativePlatformExtractedSdkPublic.returned_exact call original)
    have nativeReply:(call.step.native packetWitness.val.1).1=some application:=actualPublic.symm.trans packetReply
    have packetPrivate:answered.2=afterFinish.1:=(congrArg (fun value=>value.2.1) packetOutput).symm
    have packetNativeAfter:answered.2.1=afterFinish.1.1:=congrArg
      (fun state:RegistrationNativePlatformExtractedSdkPublic.State (RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration initial.created initial.credential)=>state.1) packetPrivate
    obtain ⟨owner,scalar,reached,beaconInitial,completed,adDigest,middle,agreed,recorded,ownerFound,ownerPhase,
      rawSample,samePacket,singleton,authenticated,agreementRun,recordRun,started,applicationEq,recordExtension⟩:=
      RegistrationNativePlatformPublicAdapterFinishGivenSourceCut.cut configuration initial.created initial.credential beforeFinish.1 index input self pending prekey oneTime kem sourceSelected phase
        packet decoded incoming packetWitness.val packetWitness.property application nativeReply
    have cacheEq:=congrArg (fun state:RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source=>RegistrationNativeWorldCache.cache state.1.1) packetNativeAfter
    have recordAtCall:RegistrationNativeWorldCache.cache recorded.2.2≤RegistrationNativeWorldCache.cache afterFinish.1.1.1.1:=cacheEq ▸recordExtension
    have sameStore:physical configuration initial.created initial.credential answered.2.1 answered.2.2=
        physical configuration initial.created initial.credential afterFinish.1.1 afterFinish.1.2:=
      congrArg (fun state:RegistrationNativePlatformExtractedSdkPublic.State (RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration initial.created initial.credential)=>
        physical configuration initial.created initial.credential state.1 state.2) packetPrivate
    have packetBlock:=congrArg (fun value=>value.2.2) packetOutput
    rw [singleton,sameStore,packetReply] at packetBlock
    have oldBlock:afterFinish.2=incoming++finishStages.map Event.stage++[Event.closed (.inl (.inr (.finish index input)))
        (.ok (some application,afterObjects)) afterBackend]:=by
      simpa only [incoming,sourceBeforeEq,logBefore,List.nil_append,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append]
        using blockEq
    have newBlock:afterFinish.2=incoming++[Event.stage (Stage.beaconFirstRecord beaconInitial (.ok (.Ok completed)))]++
        [Event.closed (.inl (.inr (.finish index input))) (.ok (some application,afterObjects)) afterBackend]:=by
      have actualObjects:=congrArg (fun raw:RustM (Option Pqxdh.Bytes×RegistrationNativePlatformPublicAdapterSourceRuntime.Objects R)=>raw) actualReply
      have objectsEq:RegistrationNativePlatformPublicAdapterSourceRuntime.objects (physical configuration initial.created initial.credential afterFinish.1.1 afterFinish.1.2)=afterObjects:=
        congrArg Prod.snd (RustM.ok.inj actualObjects)
      simpa only [objectsEq,sourceBackendEq,List.append_assoc] using packetBlock
    have stageEq:finishStages.map Event.stage=[Event.stage (Stage.beaconFirstRecord beaconInitial (.ok (.Ok completed)))]:=
      List.append_cancel_left (List.append_cancel_right (oldBlock.symm.trans newBlock))
    have finishedStage:Stage.beaconFirstRecord beaconInitial (.ok (.Ok completed))∈finishStages:=by
      have mapped :(Event.stage (Stage.beaconFirstRecord beaconInitial (.ok (.Ok completed))) :RegistrationNativePlatformPublicAdapterSourceEvents.Event n KemSK R P)∈
          finishStages.map Event.stage:=by rw [stageEq];exact List.mem_cons_self
      obtain ⟨selected,member,same⟩:=List.mem_map.mp mapped
      cases Event.stage.inj same
      exact member

    obtain ⟨request,digest,signature,sourceSigned,keyEq⟩:=RegistrationNativePlatformPublicAdapterSourceFinishIssuedSign.sign
      configuration initial.created initial.credential beforeFinish beforeHeld finished.2.1.1.2.calls good
      index packet application afterFinish.1.1.1 finishMemberFinal owner pending scalar ownerFound ownerPhase protectedKey
    obtain ⟨buildPrior,buildLater,buildCall,buildSourceSplit,buildBeforePath,buildCalled,buildLaterPath,tailEvents,buildAfterLog,⟨responseStage⟩⟩:=
      RegistrationNativePlatformPublicAdapterSourceEarlierBuild.stage configuration initial.created initial.credential beforePath rfl initialHeld
        request (RegistrationResponseExecutor.payload pending packet) digest signature sourceSigned rfl
    rcases responseStage with ⟨handle,data,buildQueryEq,buildStages,buildBlock,token,nativeCurrent,serverInitial,hashed,pin,availability,serverApplication,
      tokenFound,taken,admitted,recordPath,recordCut,firstRecorded,signed,payloadEq,signKey,adCut⟩
    rcases buildCall with ⟨buildQuery,beforeBuild,buildReply,afterBuild⟩
    dsimp only at buildQueryEq
    subst buildQuery
    obtain ⟨nativeBuildReply,_publicBuildReply,_nativeBuildRun,buildMember⟩:=RegistrationNativePlatformPublicAdapterTypedCallReadback.build
      configuration initial.created initial.credential beforeBuild afterBuild handle data buildReply buildCalled
    let nativeBuildCall :Call RegistrationNativeRawAdapter.TypedSpec (Native×P):=
      ⟨.inr (.build handle (RegistrationNativeRawAdapter.application (data.map TranscriptAuthParts.absSlice))),
        beforeBuild.1.1.1,nativeBuildReply,afterBuild.1.1.1⟩
    have sourceSuffix :Path (RegistrationNativePlatformPublicAdapterLoggedJoint.handler configuration initial.created initial.credential)
        afterBuild (buildLater++(⟨.inl (.inr (.finish index input)),beforeFinish,some application,afterFinish⟩::later)) finished.2:=
      buildLaterPath.append (.cons (⟨.inl (.inr (.finish index input)),beforeFinish,some application,afterFinish⟩:Call RegistrationNativePlatformPublicAdapterLowSpec.Spec
        (RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration initial.created initial.credential)) finishedCall _ _ afterPath)
    have buildMemberFinal:=RegistrationNativePlatformPublicAdapterTypedCallReadback.path_keep configuration initial.created initial.credential sourceSuffix nativeBuildCall buildMember
    have nativeBuildMember:nativeBuildCall∈execution.calls:=by rw [callsEq];exact buildMemberFinal
    obtain ⟨_buildLeading,_buildTrailing,_buildSplit,_nativeBeforeBuild,_nativeBuildCall,nativeAfterBuild⟩:=execution.reached.member nativeBuildCall nativeBuildMember
    have buildExtension:RegistrationNativeWorldCache.cache afterBuild.1.1.1.1≤RegistrationNativeWorldCache.cache execution.finalNative:=
      (RegistrationNativePlatformOrdinaryPathState.path setup checks wire route configuration.agreement.representation execution.initial.created execution.initial.credential
        configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer nativeAfterBuild).1
    obtain ⟨recordBefore,recordAfter,recordCalled,recordAnchor⟩:=recordCut
    have recordAtFinal:RegistrationNativePlatformSourceFinishContents.RecordCut (n:=n) RegistrationNativePlatformMldsaProgram.coins setup canonical configuration.keyView configuration.sealFailure
        allocation configuration.erased rawAllocation serializer serverInitial hashed (RegistrationNativeWorldCache.cache execution.finalNative):=
      ⟨recordBefore,recordAfter,recordCalled,recordAnchor.trans buildExtension⟩
    let nativeFinishCall :Call RegistrationNativeRawAdapter.TypedSpec (Native×P):=
      ⟨.inr (.finish index (some packet)),beforeFinish.1.1.1,.ok (some application),afterFinish.1.1.1⟩
    obtain ⟨_finishLeading,_finishTrailing,_finishSplit,_nativeBeforeFinish,_nativeFinishCall,nativeAfterFinish⟩:=execution.reached.member nativeFinishCall nativeFinishMember
    have finishExtension:RegistrationNativeWorldCache.cache afterFinish.1.1.1.1≤RegistrationNativeWorldCache.cache execution.finalNative:=
      (RegistrationNativePlatformOrdinaryPathState.path setup checks wire route configuration.agreement.representation execution.initial.created execution.initial.credential
        configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer nativeAfterFinish).1
    obtain ⟨identity,ephemeral,encapsulated,ciphertext,assigned,initHash⟩:=RegistrationNativeResponseStageContents.native_fields serverInitial hashed recordPath pending packet payloadEq.symm
    let physicalAd := RegistrationNativePlatformPublicAdapterBuildAdCut.extend RegistrationNativePlatformMldsaProgram.coins
      token.registration nativeCurrent.control pin availability serverApplication serverInitial _ _ adCut buildExtension
    have authenticatedAt :(.ok (.Ok (RegistrationResponseExecutor.acceptedResponse pending packet adDigest)),middle)∈support
        ((RegistrationNativeMldsaShared.lower setup checks configuration.agreement.representation execution.initial.created
          (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source)
            (RegistrationResponseExecutor.begin pending (.Some packet)))).run
              (RegistrationNativePlatformCompletionReceipt.consumed (RegistrationNativePlatformInitializedAgreement.opened beforeFinish.1.1.1.1) index (RegistrationResponse.abortedState pending))) := by
      simpa only [initialEq] using authenticated
    have authToAgreement := RegistrationNativePlatformAdAgreement.lower_cache setup checks configuration.agreement.representation execution.initial.created
      (simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner scalar)
        (RegistrationAgreementExecutor.beacon (RegistrationResponseExecutor.acceptedResponse pending packet adDigest)))
      middle agreed _ (by simpa only [initialEq] using agreementRun)
    have agreementToRecord := RegistrationNativePlatformAdAgreement.lower_cache setup checks configuration.agreement.representation execution.initial.created
      (simulateQ (RegistrationNativeBeaconFrontend.record setup canonical)
        (RegistrationBeaconRecordExecutor.fromInitial beaconInitial))
      agreed recorded _ (by simpa only [initialEq] using recordRun)
    have authAtFinal := authToAgreement.trans (agreementToRecord.trans (recordAtCall.trans finishExtension))
    have adBeforeOpening := RegistrationNativePlatformPublicAdapterCausalGivenStage.session_ad_from_stage setup checks wire route configuration.agreement.representation source ensureInit identityIndex identifier
      configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased rawAllocation serializer writer
      bounds mode compiled previous budget
      (fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile_bound mode budget _ (bounded publication)) functional result supported currentHistory returned execution
      index pending packet owner scalar beforeFinish.1.1.1 afterFinish.1.1.1 application nativeFinishMember ownerFound ownerPhase collisionFree marker
      nativeBuildCall nativeBuildMember handle token.registration nativeCurrent taken pin availability serverApplication serverInitial hashed admitted recordPath
      identity ephemeral encapsulated initHash ciphertext assigned physicalAd _ middle _ authenticatedAt authAtFinal
    have selectedDigest : serverInitial.binding.session_transcript_hash = RegistrationAuthenticationShared.digestArray adDigest := by
      simpa only [RegistrationResponseExecutor.acceptedResponse, RegistrationResponseExecutor.completedBinding_digest] using adBeforeOpening.1
    have compared:=RegistrationNativePlatformPublicAdapterCausalGivenStage.given_stage (adDigest := adDigest) setup checks wire route configuration.agreement.representation source ensureInit identityIndex identifier
      configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased rawAllocation serializer writer
      bounds mode compiled previous crypto correct budget
      (fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile_bound mode budget _ (bounded publication)) functional result supported currentHistory returned execution
      index pending packet owner scalar beforeFinish.1.1.1 afterFinish.1.1.1 application nativeFinishMember ownerFound ownerPhase collisionFree marker
      nativeBuildCall nativeBuildMember handle token.registration nativeCurrent taken pin availability serverApplication serverInitial hashed admitted recordPath
      identity ephemeral encapsulated initHash ciphertext recordAtFinal (RegistrationResponse.abortedState pending) middle agreed recorded beaconInitial.agreement completed beaconInitial
      (by simpa only [initialEq] using authenticated)
      (by simpa only [initialEq] using agreementRun)
      (by simpa only [initialEq] using recordRun)
      started applicationEq (recordAtCall.trans finishExtension)
    obtain ⟨contents,_applicationEq,equalRoot,initializers⟩:=compared
    have completedAt :pending.binding.complete (RegistrationAuthenticationShared.digestArray adDigest)=.ok beaconInitial.agreement.binding:=by
      rw [contents.1]
      exact RegistrationResponseExecutor.completedBinding_run pending adDigest
    have earlier:leading=beforeBuild.2++Event.opened (.inl (.inr (.build handle data)))
        (physical configuration initial.created initial.credential beforeBuild.1.1 beforeBuild.1.2)::
        (buildStages.map Event.stage++Event.closed (.inl (.inr (.build handle data)))
          (.ok (buildReply,RegistrationNativePlatformPublicAdapterSourceRuntime.objects (physical configuration initial.created initial.credential afterBuild.1.1 afterBuild.1.2)))
          (physical configuration initial.created initial.credential afterBuild.1.1 afterBuild.1.2).backend::tailEvents):=by
      rw [←logBefore,buildAfterLog,buildBlock]
      simp only [RegistrationNativePlatformPublicAdapterLoggedCallbackSpan.opened,
        RegistrationNativePlatformPublicAdapterLoggedCallbackSpan.closed,List.append_assoc,List.cons_append,List.nil_append]
    refine ⟨handle,data,physical configuration initial.created initial.credential beforeBuild.1.1 beforeBuild.1.2,beforeBuild.2,buildStages,tailEvents,
      .ok (buildReply,RegistrationNativePlatformPublicAdapterSourceRuntime.objects (physical configuration initial.created initial.credential afterBuild.1.1 afterBuild.1.2)),
      (physical configuration initial.created initial.credential afterBuild.1.1 afterBuild.1.2).backend,earlier,
      token,serverInitial,hashed,request,digest,signature,adDigest,beaconInitial,completed,tokenFound,firstRecorded,?_,keyEq,finishedStage,completedAt,contents,equalRoot,initializers,
      nativeCurrent.control,pin,availability,serverApplication,RegistrationNativeWorldCache.cache afterBuild.1.1.1.1,
      ⟨adCut⟩,(by
        have backendCache := congrArg
          (fun state : RegistrationNativePlatformSdkReification.Backend n KemSK × P => state.1.world.primitive.2)
          afterBuild.1.2.base.backend
        exact backendCache.symm),selectedDigest,adBeforeOpening.2⟩
    exact payloadEq ▸signed

theorem coverage (crypto :Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (correct :configuration.keyView.Correct) (previous :P) (budget :PqxdhDeploymentInterface.Budget)
    (bounded :∀publication,RegistrationNativePlatformPublicAdapterInterface.Respects mode budget (adversary publication))
    (functional :PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (result :RegistrationNativeKemRecipientLogSource.Result KemSK
      (Option (RegistrationNativePlatformKemInitializedJournal.History n source Value P)×P) budget.create)
    (supported :result∈support (RegistrationNativePlatformPublicAdapterSourceAgreementGame.experiment (n:=n) configuration ensureInit identityIndex identifier bounds mode adversary previous budget functional))
    (origin :¬RegistrationNativePlatformOrdinaryKemExceptions.OriginCollision source (result.2.1.1.1,result.2.1.2))
    (marker :result.2.2≠true) :
    RegistrationNativePlatformPublicAdapterSourceAgreementGame.Holds configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary crypto previous
      (result.2.1.1.1,result.2.1.2) :=by
  classical
  have stronger := coverage_with_session_ad configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary
    crypto correct previous budget bounded functional result supported origin marker
  intro outcome sourceSupported compatible failed
  have held := stronger outcome sourceSupported compatible
  cases outcome with
  | none => exact failed.elim
  | some selected =>
    obtain ⟨initial,finished⟩ := selected
    exact failed (RegistrationNativePlatformPublicAdapterSourceAgreement.owners_of_session_ad
      crypto setup.source initial.public.mldsaPublic finished.2.2 held)

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementCoverage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementCoverage.coverage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementCoverage.coverage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementCoverage.coverage_with_session_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementCoverage.coverage_with_session_ad
