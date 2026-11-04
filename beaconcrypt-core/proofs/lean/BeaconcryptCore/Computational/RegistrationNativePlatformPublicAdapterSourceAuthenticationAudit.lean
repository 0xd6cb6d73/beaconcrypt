-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPin
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedFinish
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationAudit
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
variable {Value :Type}
variable (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
local notation "Private"=>RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential
local notation "physical"=>RegistrationNativePlatformPublicAdapterAuditLowModel.physical (n:=n) configuration created credential
local notation "Log"=>RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P

local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
local notation "codec"=>RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire)
local notation "route"=>RegistrationNativePlatformPublicAdapterRouting.route
local notation "typed"=>RegistrationNativePlatformPublicAdapterAuditModel.typed configuration created credential
local notation "failure"=>RegistrationNativePlatformPublicAdapterAuditModel.failure credential

/- The source callback verdict is charged to the typed authentication attempt on that same callback. -/
omit [PublicWrapperPlatform.CryptoOperations] in
theorem bad (command :RegistrationNativePlatformPublicAdapterInterface.Command)
    (before after :RegistrationNativePlatformExtractedSdkPublic.State Private)
    (leading :List RegistrationNativePlatformPublicAdapterSourceTrace.Stage)
    (history :before.1.1.1.server.world.world.2=RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipts leading)
    (reply :RegistrationNativePlatformPublicAdapterInterface.CommandSpec.Range command)
    (supported :(reply,after.1)∈support ((RegistrationNativePlatformPublicAdapterAuditModel.model configuration created credential (.inr command)).run before.1))
    (sourceBad :RegistrationNativePlatformPublicAdapterSourceAuthentication.Bad configuration.view credential.publicKey leading command
      (physical before.1 before.2) reply (physical after.1 after.2)) :after.1.2.bad=true :=by
  classical
  rcases before with ⟨⟨current,prior⟩,stored⟩
  rcases after with ⟨after,storedAfter⟩
  have historyEq (key :Pqxdh.Bytes):RegistrationSigningShared.historyFor key (RegistrationNativeMldsaShared.nativeProject current.1)=
      RegistrationNativePlatformPublicAdapterSourceSigningHistory.history key leading :=by
    exact RegistrationNativePlatformPublicAdapterSourceSigningHistory.history_eq key
      (RegistrationNativeMldsaShared.nativeProject current.1,leading) history
  cases sourceBad with
  | accept input packet session ownerIndex beforeSource afterSource self token decoded found protectedKey returned absent=>
    change (some session,after)∈support ((RegistrationNativePlatformPublicAdapterAuditModel.raw configuration created credential
      (.inr (.accept (TranscriptAuthParts.absSlice input)))).run (current,prior)) at supported
    unfold RegistrationNativePlatformPublicAdapterAuditModel.raw at supported
    erw [RegistrationNativePlatformPublicAdapterTypedAuditRaw.query] at supported
    simp only [RegistrationNativePlatformPublicAdapterTypedAuditRaw.form,RegistrationNativeConcreteReaders.init,decoded,
      support_map] at supported
    obtain ⟨middle,called,same⟩:=supported
    simp only [RegistrationNativePlatformPublicAdapterTypedAudit.handler,StateT.run,support_map] at called
    obtain ⟨base,called,actualResult⟩:=called
    subst middle
    rcases base with ⟨answer,next⟩
    cases actual:answer with
    | fail error | div=>simp only [Prod.map_def,id_eq,actual,RegistrationNativeRawAdapter.resultOption,Prod.mk.injEq,reduceCtorEq,false_and] at same
    | ok optional=>cases optional with
      | none=>simp only [Prod.map_def,id_eq,actual,RegistrationNativeRawAdapter.resultOption,Prod.mk.injEq,reduceCtorEq,false_and] at same
      | some identifier=>
        simp only [Prod.map_def,id_eq,actual,RegistrationNativeRawAdapter.resultOption,Prod.mk.injEq] at same
        rcases same with ⟨sameIndex,sameState⟩
        have sameValue:=Option.some.inj sameIndex
        subst identifier
        subst after
        have nativeSupport:((.ok (some session),next.1),next.2)∈support
          (((RegistrationNativePlatformExtractedSdkServer.Accept.native coins setup codec checks
            (AdapterPublicServerSourceLens.admitted <$>configuration.replayAllocate stored.base.objects.server.consumed_registrations)
            route source.verify configuration.agreement.representation created input).run current.1).run current.2) :=by
          have target:=RegistrationNativePlatformPublicAdapterAuditedAccept.validTarget configuration created credential (current,prior) stored input packet decoded
          have original:=Eq.mp (congrArg (fun action=>(answer,next)∈support action) target.symm) called
          simp only [RegistrationNativePlatformPackedState.pack,StateT.run,support_map] at original
          obtain ⟨inner,reached,equal⟩:=original
          have nativeReply:=congrArg (fun value=>value.1) equal
          have nativeState:=congrArg (fun value=>value.2.1) equal
          have nativeP:=congrArg (fun value=>value.2.2) equal
          rw [actual] at nativeReply
          change inner.1.1=.ok (some session) at nativeReply
          change inner.1.2=next.1 at nativeState
          change inner.2=next.2 at nativeP
          change ((inner.1.1,inner.1.2),inner.2)∈_ at reached
          erw [nativeReply,nativeState,nativeP] at reached
          exact reached
        have pins:=RegistrationNativePlatformPublicAdapterAcceptPin.returned_source coins setup codec checks
          (AdapterPublicServerSourceLens.admitted <$>configuration.replayAllocate stored.base.objects.server.consumed_registrations)
          route source.verify configuration.agreement.representation created configuration.view configuration.views credential configuration.edFunctional input
          current.1 next.1 current.2 next.2 session storedAfter.base token returned nativeSupport
        have actualBad:=RegistrationNativePlatformPublicAdapterSourceAuthentication.accept configuration.view configuration.views setup.joint created credential current
          stored.base leading historyEq packet session ownerIndex self found token pins protectedKey absent
        change prior.bad ||decide (failure (.inr (.accept packet)) (.ok (some session)) current)=true
        simp only [RegistrationNativePlatformPublicAdapterAuditModel.failure]
        simp [actualBad]
  | finish index input packet application beforeSource afterSource self pending prekey oneTime kem decoded found phase protectedKey absent=>
    change (some application,after)∈support ((RegistrationNativePlatformPublicAdapterAuditModel.raw configuration created credential
      (.inr (.finish index (TranscriptAuthParts.absSlice input)))).run (current,prior)) at supported
    unfold RegistrationNativePlatformPublicAdapterAuditModel.raw at supported
    erw [RegistrationNativePlatformPublicAdapterTypedAuditRaw.query] at supported
    have readResponseEq:RegistrationNativeWire.readResponse RegistrationNativeConcreteCodec.wire (TranscriptAuthParts.absSlice input)=some packet:=
      (RegistrationNativeConcreteReaders.response _).trans decoded
    simp only [RegistrationNativePlatformPublicAdapterTypedAuditRaw.form,support_map] at supported
    obtain ⟨middle,called,same⟩:=supported
    simp only [RegistrationNativePlatformPublicAdapterTypedAudit.handler,StateT.run,support_map] at called
    obtain ⟨base,called,actualResult⟩:=called
    subst middle
    erw [readResponseEq] at called same
    rcases base with ⟨answer,next⟩
    cases actual:answer with
    | fail error | div=>simp only [Prod.map_def,id_eq,actual,RegistrationNativeRawAdapter.resultOption,Prod.mk.injEq,reduceCtorEq,false_and] at same
    | ok optional=>cases optional with
      | none=>simp only [Prod.map_def,id_eq,actual,RegistrationNativeRawAdapter.resultOption,Prod.mk.injEq,reduceCtorEq,false_and] at same
      | some plaintext=>
        simp only [Prod.map_def,id_eq,actual,RegistrationNativeRawAdapter.resultOption,Prod.mk.injEq] at same
        rcases same with ⟨sameReply,sameState⟩
        have sameValue:=Option.some.inj sameReply
        subst plaintext
        subst after
        have actualBad:=RegistrationNativePlatformPublicAdapterSourceAuthentication.finish configuration.view configuration.views setup.joint created credential current
          stored.base leading historyEq index packet application self found pending prekey oneTime kem phase protectedKey absent
        change prior.bad ||decide (failure (.inr (.finish index (some packet))) (.ok (some application)) current)=true
        simp only [RegistrationNativePlatformPublicAdapterAuditModel.failure]
        simp [actualBad]

omit [PublicWrapperPlatform.CryptoOperations] in
theorem raw_monotone (query :RegistrationNativeInterface.Spec.Domain)
    (before :RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source)
    (result :RegistrationNativeInterface.Spec.Range query×RegistrationNativePlatformPublicAdapterAuditModel.State n KemSK P source)
    (supported :result∈support ((RegistrationNativePlatformPublicAdapterAuditModel.raw configuration created credential query).run before))
    (positive :before.2.bad=true) :result.2.2.bad=true :=by
  unfold RegistrationNativePlatformPublicAdapterAuditModel.raw at supported
  rw [RegistrationNativePlatformPublicAdapterTypedAuditRaw.query] at supported
  cases form:RegistrationNativePlatformPublicAdapterTypedAuditRaw.form RegistrationNativeConcreteCodec.wire query with
  | pure value=>
    simp only [form,support_pure,Set.mem_singleton_iff] at supported
    cases supported
    exact positive
  | query chosen observe=>
    simp only [form,support_map] at supported
    obtain ⟨middle,called,same⟩:=supported
    simp only [RegistrationNativePlatformPublicAdapterTypedAudit.handler,StateT.run,support_map] at called
    obtain ⟨actual,called,retained⟩:=called
    subst middle
    subst result
    change (RegistrationNativePlatformPublicAdapterTypedAudit.update _ _ _ _ _ _).bad=true
    simp only [RegistrationNativePlatformPublicAdapterTypedAudit.update,positive,Bool.true_or]

omit [PublicWrapperPlatform.CryptoOperations] in
theorem closed_bad (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain)
    (before after :RegistrationNativePlatformExtractedSdkPublic.State Private)
    (leading :List RegistrationNativePlatformPublicAdapterSourceTrace.Stage)
    (history :before.1.1.1.server.world.world.2=RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipts leading)
    (reply :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Range query)
    (supported :(reply,after.1)∈support ((RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration created credential query).run before.1))
    (marked :RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.closed configuration.view credential.publicKey
      (some (physical before.1 before.2,leading)) query
      (.ok (reply,RegistrationNativePlatformPublicAdapterSourceRuntime.objects (physical after.1 after.2)))
      (physical after.1 after.2).backend=true) :after.1.2.bad=true :=by
  cases query with
  | inl publicQuery=>cases publicQuery with
    | inl coin=>simp only [RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.closed,Bool.false_eq_true] at marked
    | inr command=>
      have actual:= (RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.closed_iff configuration.view credential.publicKey
        (physical before.1 before.2) leading command reply (RegistrationNativePlatformPublicAdapterSourceRuntime.objects (physical after.1 after.2))
        (physical after.1 after.2).backend).mp marked
      rw [RegistrationNativePlatformPublicAdapterSourceRuntime.join_objects] at actual
      have native:=Eq.mp (congrArg (fun action=>(reply,after.1)∈support (action.run before.1))
        (RegistrationNativePlatformPublicAdapterAuditLowModel.public_query configuration created credential (.inr command))) supported
      exact bad configuration created credential command before after leading history reply native actual
  | inr refused=>cases refused <;>simp only [RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.closed,Bool.false_eq_true] at marked

omit [PublicWrapperPlatform.CryptoOperations] in
theorem monotone (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain)
    (before :RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source)
    (result :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Range query×RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source)
    (supported :result∈support ((RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration created credential query).run before))
    (positive :before.2.bad=true) :result.2.2.bad=true :=by
  cases query with
  | inl publicQuery=>
    have actual:=Eq.mp (congrArg (fun action=>result∈support (action.run before))
      (RegistrationNativePlatformPublicAdapterAuditLowModel.public_query configuration created credential publicQuery)) supported
    cases publicQuery with
    | inl coin=>exact raw_monotone configuration created credential (.inl coin) before result actual positive
    | inr command=>exact raw_monotone configuration created credential (.inr (RegistrationNativePlatformPublicAdapterInterface.nativeCommand command)) before result actual positive
  | inr refused=>cases refused with
    | serverSend key bytes oversized=>
      have actual:=Eq.mp (congrArg (fun action=>result∈support (action.run before))
        (RegistrationNativePlatformPublicAdapterAuditLowModel.server_query configuration created credential key bytes oversized)) supported
      exact raw_monotone configuration created credential (.inr (.serverSend key bytes)) before result actual positive
    | beaconSend owner bytes oversized=>
      have actual:=Eq.mp (congrArg (fun action=>result∈support (action.run before))
        (RegistrationNativePlatformPublicAdapterAuditLowModel.beacon_query configuration created credential owner bytes oversized)) supported
      exact raw_monotone configuration created credential (.inr (.beaconSend owner bytes)) before result actual positive

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationAudit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationAudit.bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationAudit.bad

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationAudit.raw_monotone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationAudit.raw_monotone

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationAudit.closed_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationAudit.closed_bad

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationAudit.monotone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationAudit.monotone
