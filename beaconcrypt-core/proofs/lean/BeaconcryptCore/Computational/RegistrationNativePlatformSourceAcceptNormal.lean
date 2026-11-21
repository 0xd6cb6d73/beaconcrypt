-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedAuthentication
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer
import BeaconcryptCore.PanicFreedom.Registration
import BeaconcryptCore.PanicFreedom.RegistrationTrivial
import BeaconcryptCore.PanicFreedom.KeyAgreement
import BeaconcryptCore.PanicFreedom.PeerOwnership
/-! Actual current accept normality follows from typed authentication/agreement queries, unconditional core panic-freedom and Boolean stateful reservation. Rejection remains a normal optional outcome; no caller controller or whole-normality law is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptNormal
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec Checks)
variable {A S I KemSK Reader Response Platform : Type} {base : OracleSpec I} {n : Nat}
def Normal {A : Type} (result : RustM A) : Prop := ∃value,result=.ok value
private theorem pure_normal {J : Type} {spec : OracleSpec J} (value : A) (result : RustM A)
    (supported : result∈support (pure (.ok value) :OracleComp spec (RustM A))) : Normal result := by
  simp only [support_pure,Set.mem_singleton_iff] at supported
  exact ⟨value,supported⟩
private theorem auth_edge (query : RegistrationAuthenticationExecutor.Spec.Domain)
    (event : RegistrationAuthenticationExecutor.Spec.Range query→RegistrationAuthenticationFlow.Event)
    (resume : RegistrationAuthenticationExecutor.Spec.Range query→RustM registration.InitAuthentication)
    (total : ∀reply,∃next,resume reply=.ok next)
    (result : RustM (Option (RegistrationAuthenticationFlow.Event×registration.InitAuthentication)))
    (supported : result∈support (do
      let reply←(RegistrationAuthenticationExecutor.Spec.query query : OracleComp RegistrationAuthenticationExecutor.Spec _)
      pure (RegistrationAuthenticationExecutor.edge (event reply) (resume reply)))) : Normal result := by
  simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at supported
  obtain ⟨reply,_possible,rfl⟩:=supported
  obtain ⟨next,resumed⟩:=total reply
  exact ⟨some (event reply,next),by simp only [RegistrationAuthenticationExecutor.edge,resumed]⟩
private theorem auth_step (state : registration.InitAuthentication)
    (result : RustM (Option (RegistrationAuthenticationFlow.Event×registration.InitAuthentication)))
    (supported : result∈support (RegistrationAuthenticationExecutor.step state)) : Normal result := by
  cases state with
  | HashRequested pending=>
    obtain ⟨request,requested⟩:=PanicFreedom.RegistrationTrivial.InitHash_request_total pending
    simp only [RegistrationAuthenticationExecutor.step,requested,RegistrationAuthenticationExecutor.continueWith] at supported
    exact auth_edge _ _ _ (PanicFreedom.Registration.InitHash_resume_total pending) result supported
  | Ed25519VerificationRequested pending=>
    obtain ⟨request,requested⟩:=PanicFreedom.Registration.InitEd25519Verification_request_total pending
    simp only [RegistrationAuthenticationExecutor.step,requested,RegistrationAuthenticationExecutor.continueWith] at supported
    exact auth_edge _ _ _ (PanicFreedom.Registration.InitEd25519Verification_resume_total pending) result supported
  | Accepted accepted=>exact pure_normal none result supported
  | Rejected=>exact pure_normal none result supported
private theorem auth_execute (fuel : Nat) (state : registration.InitAuthentication)
    (result : RustM (List RegistrationAuthenticationFlow.Event×registration.InitAuthentication))
    (supported : result∈support (RegistrationAuthenticationExecutor.execute fuel state)) : Normal result := by
  induction fuel generalizing state result with
  | zero=>exact pure_normal ([],state) result supported
  | succ fuel ih=>
    simp only [RegistrationAuthenticationExecutor.execute,mem_support_bind_iff] at supported
    obtain ⟨stepped,called,later⟩:=supported
    obtain ⟨next,nextEq⟩:=auth_step state stepped called
    rw [nextEq,RegistrationAuthenticationExecutor.continueWith] at later
    cases next with
    | none=>exact pure_normal ([],state) result later
    | some pair=>
      rcases pair with ⟨event,after⟩
      simp only [mem_support_bind_iff] at later
      obtain ⟨rest,continued,returned⟩:=later
      obtain ⟨final,finalEq⟩:=ih after rest continued
      rw [finalEq,RegistrationAuthenticationExecutor.continueWith] at returned
      exact pure_normal (event::final.1,final.2) result returned
/-- Every typed reply of the complete extracted authentication controller has a normal result. -/
theorem authentication (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (result : RustM (List RegistrationAuthenticationFlow.Event×registration.InitAuthentication))
    (supported : result∈support (RegistrationAuthenticationExecutor.begin pin packet)) : Normal result := by
  obtain ⟨state,started⟩:=PanicFreedom.Registration.begin_init_authentication_total pin packet
  simp only [RegistrationAuthenticationExecutor.begin,started,RegistrationAuthenticationExecutor.continueWith] at supported
  exact auth_execute 5 state result supported
private theorem agree_query (query : RegistrationAgreementExecutor.Spec.Domain)
    (resume : RegistrationAgreementExecutor.Spec.Range query→RustM agreement.AgreementEffect)
    (total : ∀reply,∃next,resume reply=.ok next) (result : RustM agreement.AgreementEffect)
    (supported : result∈support (do
      let reply←(RegistrationAgreementExecutor.Spec.query query : OracleComp RegistrationAgreementExecutor.Spec _)
      pure (resume reply))) : Normal result := by
  simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at supported
  obtain ⟨reply,_possible,rfl⟩:=supported
  exact total reply
private theorem agree_step (state : agreement.AgreementEffect) (result : RustM agreement.AgreementEffect)
    (supported : result∈support (RegistrationAgreementExecutor.step state)) : Normal result := by
  cases state with
  | ConvertPublic pending=>
    obtain ⟨request,requested⟩:=PanicFreedom.KeyAgreement.public_conversion_key_total pending
    simp only [RegistrationAgreementExecutor.step,requested,RegistrationAgreementExecutor.continueWith] at supported
    exact agree_query (.convertPublic request) pending.resume (PanicFreedom.KeyAgreement.public_conversion_resume_total pending) result supported
  | ConvertSecret pending=>
    obtain ⟨request,requested⟩:=PanicFreedom.KeyAgreement.secret_conversion_role_total pending
    simp only [RegistrationAgreementExecutor.step,requested,RegistrationAgreementExecutor.continueWith] at supported
    exact agree_query (.convertSecret request) pending.resume (PanicFreedom.KeyAgreement.secret_conversion_resume_total pending) result supported
  | GenerateEphemeral pending=>
    obtain ⟨request,requested⟩:=PanicFreedom.KeyAgreement.ephemeral_role_total pending
    simp only [RegistrationAgreementExecutor.step,requested,RegistrationAgreementExecutor.continueWith] at supported
    exact agree_query (.generate request) pending.resume (PanicFreedom.KeyAgreement.ephemeral_resume_total pending) result supported
  | Encapsulate pending=>
    obtain ⟨request,requested⟩:=PanicFreedom.KeyAgreement.encapsulation_key_total pending
    simp only [RegistrationAgreementExecutor.step,requested,RegistrationAgreementExecutor.continueWith] at supported
    exact agree_query (.encapsulate request) pending.resume (PanicFreedom.KeyAgreement.encapsulation_resume_total pending) result supported
  | Decapsulate pending=>
    obtain ⟨request,requested⟩:=PanicFreedom.KeyAgreement.decapsulation_ciphertext_total pending
    simp only [RegistrationAgreementExecutor.step,requested,RegistrationAgreementExecutor.continueWith] at supported
    exact agree_query (.decapsulate request) pending.resume (PanicFreedom.KeyAgreement.decapsulation_resume_total pending) result supported
  | Dh pending=>
    obtain ⟨request,requested⟩:=PanicFreedom.KeyAgreement.dh_request_total pending
    simp only [RegistrationAgreementExecutor.step,requested,RegistrationAgreementExecutor.continueWith] at supported
    exact agree_query (.dh request) pending.resume (PanicFreedom.KeyAgreement.dh_resume_total pending) result supported
  | RootKdf pending=>
    obtain ⟨request,requested⟩:=PanicFreedom.KeyAgreement.root_kdf_request_total pending
    simp only [RegistrationAgreementExecutor.step,requested,RegistrationAgreementExecutor.continueWith] at supported
    exact agree_query (.root request) pending.resume (PanicFreedom.KeyAgreement.root_kdf_resume_total pending) result supported
  | Rejected rejection=>exact pure_normal (spec:=RegistrationAgreementExecutor.Spec) (.Rejected rejection) result (by simpa only [RegistrationAgreementExecutor.step] using supported)
  | ServerComplete accepted=>exact pure_normal (spec:=RegistrationAgreementExecutor.Spec) (.ServerComplete accepted) result (by simpa only [RegistrationAgreementExecutor.step] using supported)
  | BeaconComplete accepted=>exact pure_normal (spec:=RegistrationAgreementExecutor.Spec) (.BeaconComplete accepted) result (by simpa only [RegistrationAgreementExecutor.step] using supported)
private theorem agree_drive (fuel : Nat) (state : agreement.AgreementEffect) (result : RustM agreement.AgreementEffect)
    (supported : result∈support (RegistrationAgreementExecutor.drive fuel state)) : Normal result := by
  induction fuel generalizing state result with
  | zero=>exact pure_normal state result supported
  | succ fuel ih=>
    simp only [RegistrationAgreementExecutor.drive,mem_support_bind_iff] at supported
    obtain ⟨stepped,called,later⟩:=supported
    obtain ⟨next,nextEq⟩:=agree_step state stepped called
    rw [nextEq,RegistrationAgreementExecutor.continueWith] at later
    exact ih next result later
/-- Replay-aware Server agreement is normal through all optional rejections. -/
theorem agreement (control : pqxdh.ServerState) (authenticated : registration.AuthenticatedInit)
    (history : RegistrationReplaySchedule.State) (result : RustM agreement.AgreementEffect)
    (supported : result∈support (RegistrationReplaySchedule.begin control authenticated history)) : Normal result := by
  rw [RegistrationReplaySchedule.begin_eq] at supported
  split at supported
  · exact pure_normal (.Rejected .None) result supported
  · obtain ⟨state,started⟩:=PanicFreedom.KeyAgreement.begin_server_agreement_total control .Fresh authenticated
    simp only [RegistrationAgreementExecutor.server,started,RegistrationAgreementExecutor.continueWith] at supported
    exact agree_drive 9 state result supported
private theorem source_supported {J : Type} {spec : OracleSpec J} {X : Type}
    (implementation : QueryImpl spec (StateT S ProbComp)) (work : OracleComp spec X)
    (before : S) (result : X×S) (supported : result∈support ((simulateQ implementation work).run before)) :
    result.1∈support work := by
  apply OracleComp.support_simulateQ_run'_subset implementation work before
  rw [StateT.run'_eq,support_map]
  exact ⟨result,supported,rfl⟩
private theorem auth_world (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before : PqxdhRecordLiftWorld.State n)
    (result : RustM (List RegistrationAuthenticationFlow.Event×registration.InitAuthentication)×PqxdhRecordLiftWorld.State n)
    (supported : result∈support ((RegistrationWorldAuthentication.begin setup codec route verify pin packet).run before)) :
    Normal result.1 := by
  unfold RegistrationWorldAuthentication.begin RegistrationWorldAuthentication.program at supported
  rw [←QueryImpl.simulateQ_compose] at supported
  exact authentication pin packet result.1 (source_supported _ _ before result supported)
private theorem agree_native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerFrontendCompiler.State n)
    (result : RustM agreement.AgreementEffect×RegistrationServerFrontendCompiler.State n)
    (supported : result∈support ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before)) :
    Normal result.1 := by
  simp only [RegistrationServerNativeSource.agree,StateT.run,support_map] at supported
  obtain ⟨inner,called,rfl⟩:=supported
  exact agreement before.control authenticated before.consumed inner.1 (source_supported _ _ before.world inner called)
private theorem retain_native (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (accepted : agreement.ServerAgreement)
    (before : RegistrationServerFrontendCompiler.State n)
    (result : RustM (Option Nat)×RegistrationServerFrontendCompiler.State n)
    (supported : result∈support ((RegistrationServerNativeSource.retain created accepted).run before)) : Normal result.1 := by
  have consumed : ∃reply,RegistrationReplaySchedule.consume accepted before.consumed=.ok reply := by
    cases present : before.consumed.contains (PqxdhRefinement.absBytes accepted.pending.registration_id.bytes) with
    | false=>exact ⟨_,RegistrationReplaySchedule.consume_fresh accepted before.consumed present⟩
    | true=>exact ⟨_,RegistrationReplaySchedule.consume_replayed accepted before.consumed present⟩
  obtain ⟨⟨optional,history⟩,called⟩:=consumed
  cases optional <;>
    simp only [RegistrationServerNativeSource.retain,RegistrationServerNativeSource.sourceStep,
      RegistrationWorldServerFrontend.retain,RegistrationServerFrontendCompiler.restore,StateT.run,called,map_pure,
      support_pure,Set.mem_singleton_iff] at supported
  all_goals subst result
  all_goals exact ⟨_,rfl⟩
/-- Every actual reached native Init authentication reply is normal at the same World and external platform state. -/
theorem authenticate (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before : RegistrationServerFrontendCompiler.State n) (previous : Platform)
    (result : (RustM (List RegistrationAuthenticationFlow.Event×registration.InitAuthentication)×RegistrationServerFrontendCompiler.State n)×Platform)
    (supported : result∈support (((RegistrationNativePlatformSourceAccept.authenticate coins setup codec route verify pin packet).run before).run previous)) :
    Normal result.1.1 := by
  rw [RegistrationNativePlatformSourceAccept.authenticate_run,StateT.run_map,support_map] at supported
  obtain ⟨inner,called,rfl⟩:=supported
  exact auth_world setup codec route verify pin packet before.world.world.1 inner.1
    (source_supported coins _ previous inner called)
/-- Recomputing the actual Server pin is normal even at an uncached reached World. -/
theorem pin (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (before : RegistrationServerFrontendCompiler.State n) (previous : Platform)
    (result : (RegistrationNativeServerPinRecompute.PinReply×RegistrationServerFrontendCompiler.State n)×Platform)
    (supported : result∈support (((RegistrationNativePlatformSourceBuild.pin coins).run before).run previous)) : Normal result.1.1 := by
  have run : (RegistrationNativePlatformSourceBuild.pin coins).run before =
      (fun inner=>(inner.1,{before with world:={before.world with world:=(inner.2,before.world.world.2)}})) <$>
        simulateQ coins ((RegistrationNativeServerPinRecompute.native before.pin.binding before.pin.public_key).run before.world.world.1) := rfl
  rw [run,StateT.run_map,support_map] at supported
  obtain ⟨inner,called,rfl⟩:=supported
  have native:=source_supported coins _ previous inner called
  rw [RegistrationNativeServerPinRecompute.native_run] at native
  simp only [support_pure,Set.mem_singleton_iff] at native
  exact ⟨_,congrArg Prod.fst native⟩
private theorem pure_state (value : A) (before : S) (previous : Platform)
    (result : (RustM A×S)×Platform)
    (supported : result∈support (((pure (.ok value) : StateT S (StateT Platform ProbComp) (RustM A)).run before).run previous)) :
    Normal result.1.1 := by
  simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
  exact ⟨value,congrArg (fun r=>r.1.1) supported⟩
/-- Replay refusal and arbitrary Boolean registration reservation preserve normal returns. -/
theorem afterAuthentication (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK) (checks : Checks)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerFrontendCompiler.State n) (previous : Platform)
    (result : (RustM (Option Nat)×RegistrationServerFrontendCompiler.State n)×Platform)
    (supported : result∈support (((RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks reserve representation created packet authenticated).run before).run previous)) :
    Normal result.1.1 := by
  rw [RegistrationNativePlatformServerSdk.afterAuthentication_run] at supported
  split at supported
  · exact pure_state none before previous result supported
  · simp only [StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨⟨⟨admitted,middle⟩,middleP⟩,_reserved,later⟩:=supported
    cases admitted with
    | false=>exact pure_state none middle middleP result later
    | true=>
      simp only [ite_true,StateT.run_bind,mem_support_bind_iff] at later
      obtain ⟨completed,called,continued⟩:=later
      have native:=source_supported coins _ middleP completed called
      obtain ⟨effect,normal⟩:=agree_native setup checks representation created packet authenticated middle completed.1 native
      rw [normal] at continued
      cases effect with
      | ServerComplete accepted=>
        exact retain_native created accepted completed.1.2 result.1
          (source_supported coins _ completed.2 result continued)
      | _=>exact pure_state none completed.1.2 completed.2 result continued

private theorem after_pin (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (optional : core.option.Option session.ServerAuthenticationPin)
    (before : RegistrationServerFrontendCompiler.State n) (previous : Platform)
    (result : (RustM (Option Nat)×RegistrationServerFrontendCompiler.State n)×Platform)
    (supported : result∈support (((RegistrationNativePlatformSourceAccept.afterPin coins setup codec checks reserve route verify representation created packet (.ok optional)).run before).run previous)) :
    Normal result.1.1 := by
  cases optional with
  | none=>exact pure_state none before previous result supported
  | some current=>
    simp only [RegistrationNativePlatformSourceAccept.afterPin,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨checked,called,later⟩:=supported
    obtain ⟨⟨events,state⟩,normal⟩:=authenticate coins setup codec route verify current packet before previous checked called
    rw [normal] at later
    cases state with
    | Accepted authenticated=>exact afterAuthentication coins setup checks reserve representation created packet authenticated checked.1.2 checked.2 result later
    | _=>exact pure_state none checked.1.2 checked.2 result later
/-- Complete current acceptance is normal at arbitrary reached Server/platform states, including failed authentication, replay and reservation refusal. -/
theorem accept (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (before : RegistrationServerFrontendCompiler.State n) (previous : Platform)
    (result : (RustM (Option Nat)×RegistrationServerFrontendCompiler.State n)×Platform)
    (supported : result∈support (((RegistrationNativePlatformSourceAccept.accept coins setup codec checks reserve route verify representation created packet).run before).run previous)) :
    Normal result.1.1 := by
  simp only [RegistrationNativePlatformSourceAccept.accept,RegistrationNativePlatformSourceAccept.acceptWith,
    StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨current,called,later⟩:=supported
  obtain ⟨optional,normal⟩:=pin coins before previous current called
  rw [normal] at later
  exact after_pin coins setup codec checks (StateT.lift reserve) route verify representation created packet optional current.1.2 current.2 result later
/-- The actual extracted Init authentication child has the same normal accept result under only the narrow Ed operation contract. -/
theorem extracted_accept [ed : AdapterInitEdPrimitive.Operations]
    (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (functional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (packet : registration.InitPacket) (before : RegistrationServerFrontendCompiler.State n) (previous : Platform)
    (result : (RustM (Option Nat)×RegistrationServerFrontendCompiler.State n)×Platform)
    (supported : result∈support (((RegistrationNativePlatformExtractedAuthentication.accept coins setup codec route verify checks representation created reserve packet).run before).run previous)) :
    Normal result.1.1 := by
  rw [RegistrationNativePlatformExtractedAuthentication.accept_source coins setup codec route verify checks representation created functional reserve packet] at supported
  exact accept coins setup codec checks reserve route verify representation created packet before previous result supported


private theorem server_run {source : RegistrationNativeMldsa.Source}
    (work : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) A)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    (RegistrationNativePlatformExperiment.server work).run before=
      (fun inner=>(inner.1,{before with server:=inner.2})) <$> work.run before.server := rfl
/-- The actual decoded/parsed SDK native acceptance wrapper is normal on the same complete native/platform state. -/
theorem dispatch [ed : AdapterInitEdPrimitive.Operations] {source : RegistrationNativeMldsa.Source}
    (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (functional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (input : Slice U8) (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform)
    (result : (RustM (Option Nat)×RegistrationNativeExperiment.State n KemSK source)×Platform)
    (supported : result∈support (((RegistrationNativePlatformExtractedSdkServer.Accept.native coins setup codec checks reserve route verify representation created input).run before).run previous)) :
    Normal result.1.1 := by
  cases decoded : RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none=>
    simp only [RegistrationNativePlatformExtractedSdkServer.Accept.native,decoded] at supported
    exact pure_state none before previous result supported
  | some packet=>
    simp only [RegistrationNativePlatformExtractedSdkServer.Accept.native,decoded,StateT.run_bind,StateT.run_modify,pure_bind] at supported
    rw [server_run,StateT.run_map,support_map] at supported
    obtain ⟨inner,called,rfl⟩:=supported
    exact extracted_accept coins setup codec checks reserve route verify representation created functional packet before.server previous inner called

end BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptNormal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptNormal.authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptNormal.authentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptNormal.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptNormal.agreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptNormal.authenticate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptNormal.authenticate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptNormal.pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptNormal.pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptNormal.afterAuthentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptNormal.afterAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptNormal.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptNormal.accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptNormal.extracted_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptNormal.extracted_accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptNormal.dispatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptNormal.dispatch
