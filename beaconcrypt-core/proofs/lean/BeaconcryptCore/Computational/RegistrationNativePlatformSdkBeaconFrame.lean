-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAcceptNormal
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildNormal
import BeaconcryptCore.Computational.RegistrationNativeWorldOwnerFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconFrame
attribute [local irreducible] RegistrationAuthenticationExecutor.begin registration.begin_init_authentication RegistrationWorldAuthentication.begin RegistrationServerNativeSource.agree
open BeaconcryptCore.Refinement
open PqxdhRecordLiftInterface ratchet.concrete
variable {S T A B : Type}
private def Keeps (project : S→T) (work : StateT S ProbComp A) : Prop :=
  ∀before result,result∈support (work.run before)→project result.2=project before
private theorem pure_keeps (project : S→T) (value : A) : Keeps project (pure value) := by
  intro before result supported
  simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
  subst result
  rfl
private theorem bind_keeps (project : S→T) (work : StateT S ProbComp A) (next : A→StateT S ProbComp B)
    (first : Keeps project work) (later : ∀value,Keeps project (next value)) : Keeps project (work >>=next) := by
  intro before result supported
  simp only [StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,called,continued⟩ := supported
  exact (later middle.1 middle.2 result continued).trans (first before middle called)
private theorem map_keeps (project : S→T) (work : StateT S ProbComp A) (f : A→B)
    (first : Keeps project work) : Keeps project (f <$>work) := by
  intro before result supported
  rw [StateT.run_map,support_map] at supported
  obtain ⟨middle,called,rfl⟩ := supported
  exact first before middle called
private theorem program_keeps {I : Type} {spec : OracleSpec I} (project : S→T)
    (impl : QueryImpl spec (StateT S ProbComp)) (leaves : ∀query,Keeps project (impl query))
    (work : OracleComp spec A) : Keeps project (simulateQ impl work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_keeps project value
  | query_bind query next ih =>
    rw [simulateQ_bind,simulateQ_spec_query]
    exact bind_keeps project _ _ (leaves query) ih
variable {n : Nat} {I KemSK Reader Response Auxiliary : Type} {base : OracleSpec I}
private def owners (before : RegistrationWorldAgreement.State n Auxiliary) := before.world.1.owners
private theorem record (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) : Keeps (owners (n:=n) (Auxiliary:=Auxiliary)) (RegistrationWorldRecords.record setup codec query) := by
  intro before result supported
  simp only [RegistrationWorldRecords.record,StateT.run,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  rfl
private theorem shared (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : MldsaSharedNative.Spec.Domain) : Keeps (owners (n:=n) (Auxiliary:=Auxiliary)) (RegistrationWorldRecords.shared setup codec query) := by
  cases query with
  | inr query => exact record setup codec query
  | inl query =>
    intro before result supported
    simp only [RegistrationWorldRecords.shared,StateT.run,support_map] at supported
    obtain ⟨inner,called,rfl⟩ := supported
    exact RegistrationNativeWorldOwnerFrame.hash_owners query.2 before.world.1 inner called
private theorem records (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : RegistrationRecordPrimitives.Spec.Domain) : Keeps (owners (n:=n) (Auxiliary:=Auxiliary)) (RegistrationWorldRecords.handler setup codec query) := by
  intro before result supported
  simp only [RegistrationWorldRecords.handler,StateT.run,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact program_keeps owners (RegistrationWorldRecords.shared setup codec) (shared setup codec)
    (RegistrationRecordPrimitives.callbacks setup.source query) before inner called
private theorem outgoing (sign : registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Spec.Domain) : Keeps (fun before : RegistrationWorldSigning.State n=>before.1.owners) (RegistrationWorldSigning.outgoing sign query) := by
  intro before result supported
  cases query with
  | hash request =>
    simp only [RegistrationWorldSigning.outgoing,StateT.run,support_map] at supported
    obtain ⟨inner,called,rfl⟩ := supported
    exact RegistrationNativeWorldOwnerFrame.hash_owners _ before.1 inner called
  | sign request payload digest =>
    simp only [RegistrationWorldSigning.outgoing,StateT.run,support_map] at supported
    obtain ⟨inner,called,rfl⟩ := supported
    exact RegistrationNativeWorldOwnerFrame.sampled_owners _ before.1 inner called
private theorem agreement (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Spec.Domain) : Keeps (owners (n:=n)) (RegistrationWorldAgreement.agreement source primitive query) := by
  intro before result supported
  simp only [RegistrationWorldAgreement.agreement,StateT.run,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact RegistrationNativeWorldOwnerFrame.sampled_owners _ before.world.1 inner called
private theorem authentication_query (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (query : RegistrationAuthenticationExecutor.Spec.Domain) :
    Keeps (fun before : PqxdhRecordLiftWorld.State n=>before.owners) (RegistrationWorldAuthentication.implementation setup codec route verify query) := by
  cases query with
  | hash request =>
    change Keeps _ ((fun digest=>core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest)) <$>
      PqxdhRecordLiftWorld.effects (.inr (.hash (RegistrationInputs.hashBytes request))))
    exact map_keeps _ _ _ (RegistrationNativeWorldOwnerFrame.hash_owners _)
  | mldsa request => exact pure_keeps _ _
  | ed25519 request => exact pure_keeps _ _
private theorem authentication (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    Keeps (fun before : PqxdhRecordLiftWorld.State n=>before.owners) (RegistrationWorldAuthentication.begin setup codec route verify pin packet) := by
  unfold RegistrationWorldAuthentication.begin RegistrationWorldAuthentication.program
  rw [←QueryImpl.simulateQ_compose]
  exact program_keeps _ _ (authentication_query setup codec route verify) _
private theorem pin_native (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize) :
    Keeps (fun before : PqxdhRecordLiftWorld.State n=>before.owners) (RegistrationNativeServerPinRecompute.native binding publicKey) := by
  intro before result supported
  rw [RegistrationNativeServerPinRecompute.native_run,bind_pure_comp,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact RegistrationNativeWorldOwnerFrame.hash_owners _ before inner called
private theorem agree_native (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    Keeps (fun before : RegistrationServerFrontendCompiler.State n=>before.world.world.1.owners)
      (RegistrationServerNativeSource.agree setup checks representation created packet authenticated) := by
  intro before result supported
  simp only [RegistrationServerNativeSource.agree,StateT.run,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact program_keeps owners _ (agreement setup.source _) _ before.world inner called
private theorem retain_native (created : PqxdhLiveServerConstruction.Created Unit) (accepted : agreement.ServerAgreement) :
    Keeps (fun before : RegistrationServerFrontendCompiler.State n=>before.world.world.1.owners) (RegistrationServerNativeSource.retain created accepted) := by
  intro before result supported
  unfold RegistrationServerNativeSource.retain RegistrationServerNativeSource.sourceStep RegistrationWorldServerFrontend.retain at supported
  cases consumed : RegistrationReplaySchedule.consume accepted before.consumed with
  | fail error | div =>
    simp only [StateT.run,RegistrationServerFrontendCompiler.restore,consumed,map_pure,support_pure,Set.mem_singleton_iff] at supported
    subst result
    rfl
  | ok pair =>
    rcases pair with ⟨optional,history⟩
    cases optional <;>
      simp only [StateT.run,RegistrationServerFrontendCompiler.restore,consumed,map_pure,support_pure,Set.mem_singleton_iff] at supported <;>
      subst result <;> rfl
variable {P : Type}
private def KeepsP (project : S→T) (work : StateT S (StateT P ProbComp) A) : Prop :=
  ∀before previous result,result∈support ((work.run before).run previous)→project result.1.2=project before
private theorem pureP (project : S→T) (value : A) : KeepsP (P:=P) project (pure value) := by
  intro before previous result supported
  simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
  subst result
  rfl
private theorem bindP (project : S→T) (work : StateT S (StateT P ProbComp) A) (next : A→StateT S (StateT P ProbComp) B)
    (first : KeepsP project work) (later : ∀value,KeepsP project (next value)) : KeepsP project (work >>=next) := by
  intro before previous result supported
  simp only [StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,called,continued⟩ := supported
  exact (later middle.1.1 middle.1.2 middle.2 result continued).trans (first before previous middle called)
private theorem liftP (project : S→T) (work : StateT P ProbComp A) : KeepsP project (StateT.lift work) := by
  intro before previous result supported
  simp only [StateT.run_lift,bind_pure_comp,StateT.run_map,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  rfl
private theorem nativeP (project : S→T) (work : StateT S ProbComp A) (safe : Keeps project work)
    (coins : QueryImpl unifSpec (StateT P ProbComp)) : KeepsP project (fun before=>simulateQ coins (work.run before)) := by
  intro before previous result supported
  exact safe before result.1 (RegistrationNativePlatformHashReceipt.native_support coins _ result.1 previous result.2 supported)
private def serverOwners (before : RegistrationServerFrontendCompiler.State n) := before.world.world.1.owners
private theorem source_pin (coins : QueryImpl unifSpec (StateT P ProbComp)) :
    KeepsP (serverOwners (n:=n)) (RegistrationNativePlatformSourceBuild.pin coins) := by
  intro before previous result supported
  change result∈support (((fun inner : RegistrationNativeServerPinRecompute.PinReply×PqxdhRecordLiftWorld.State n=>
    (inner.1,{before with world:={before.world with world:=(inner.2,before.world.world.2)}})) <$>
    simulateQ coins ((RegistrationNativeServerPinRecompute.native before.pin.binding before.pin.public_key).run before.world.world.1)).run previous) at supported
  rw [StateT.run_map,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact nativeP (fun value=>value.owners) _ (pin_native before.pin.binding before.pin.public_key) coins _ _ inner called
private theorem source_authentication (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    KeepsP (serverOwners (n:=n)) (RegistrationNativePlatformSourceAccept.authenticate coins setup codec route verify pin packet) := by
  intro before previous result supported
  rw [RegistrationNativePlatformSourceAccept.authenticate_run,StateT.run_map,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact nativeP (fun value=>value.owners) _ (authentication setup codec route verify pin packet) coins _ _ inner called
private theorem afterAuthentication (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (reserve : StateT P ProbComp Bool) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    KeepsP (serverOwners (n:=n)) (RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks (StateT.lift reserve) representation created packet authenticated) := by
  unfold RegistrationNativePlatformServerSdk.afterAuthentication
  apply bindP
  · intro before previous result supported
    simp only [StateT.run_get,StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
    subst result
    rfl
  · intro before
    split
    · exact pureP _ _
    · apply bindP _ _ _ (liftP _ reserve)
      intro admitted
      cases admitted with
      | false => exact pureP _ _
      | true =>
        apply bindP _ _ _ (nativeP _ _ (agree_native setup checks representation created packet authenticated) coins)
        intro completed
        cases completed with
        | fail error | div => exact pureP _ _
        | ok completed => cases completed with
          | ServerComplete accepted => exact nativeP _ _ (retain_native created accepted) coins
          | _ => exact pureP _ _
private theorem afterPin (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (checks : PqxdhServerAuthExperiment.Checks) (reserve : StateT P ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) (pinned : RustM (core.option.Option session.ServerAuthenticationPin)) :
    KeepsP (serverOwners (n:=n)) (RegistrationNativePlatformSourceAccept.afterPin coins setup codec checks (StateT.lift reserve) route verify representation created packet pinned) := by
  unfold RegistrationNativePlatformSourceAccept.afterPin
  cases pinned with
  | fail error | div => exact pureP _ _
  | ok optional => cases optional with
    | none => exact pureP _ _
    | some pin =>
      apply bindP _ _ _ (source_authentication coins setup codec route verify pin packet)
      intro checked
      cases checked with
      | fail error | div => exact pureP _ _
      | ok pair =>
        rcases pair with ⟨events,checked⟩
        cases checked with
        | Accepted authenticated => exact afterAuthentication coins setup checks reserve representation created packet authenticated
        | _ => exact pureP _ _
private theorem accept_server (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (checks : PqxdhServerAuthExperiment.Checks) (reserve : StateT P ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) :
    KeepsP (serverOwners (n:=n)) (RegistrationNativePlatformSourceAccept.accept coins setup codec checks reserve route verify representation created packet) := by
  unfold RegistrationNativePlatformSourceAccept.accept RegistrationNativePlatformSourceAccept.acceptWith
  exact bindP _ _ _ (source_pin coins) (afterPin coins setup codec checks reserve route verify representation created packet)
variable {source : RegistrationNativeMldsa.Source}
def image (before : RegistrationNativeExperiment.State n KemSK source) :=
  (before.beacons,before.pool.keys,before.server.world.world.1.owners)
theorem accept [ed : AdapterInitEdPrimitive.Operations]
    (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (checks : PqxdhServerAuthExperiment.Checks) (reserve : StateT P ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (functional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (input : Slice U8) (before : RegistrationNativeExperiment.State n KemSK source) (previous : P)
    (result : (RustM (Option Nat)×RegistrationNativeExperiment.State n KemSK source)×P)
    (supported : result∈support (((RegistrationNativePlatformExtractedSdkServer.Accept.native coins setup codec checks reserve route verify representation created input).run before).run previous)) :
    image result.1.2=image before := by
  cases decoded : RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none =>
    simp only [RegistrationNativePlatformExtractedSdkServer.Accept.native,decoded,StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
    subst result
    rfl
  | some packet =>
    simp only [RegistrationNativePlatformExtractedSdkServer.Accept.native,decoded,StateT.run_bind,StateT.run_modify,pure_bind] at supported
    rw [RegistrationNativePlatformExtractedAuthentication.accept_source coins setup codec route verify checks representation created functional reserve packet] at supported
    rw [AdapterPublicServerSourceLens.server_run,StateT.run_map,support_map] at supported
    obtain ⟨inner,called,rfl⟩ := supported
    have kept := accept_server coins setup codec checks reserve route verify representation created packet before.server previous inner called
    exact congrArg (fun worldOwners=>(before.beacons,before.pool.keys,worldOwners)) kept
private theorem mapP (project : S→T) (work : StateT S (StateT P ProbComp) A) (f : A→B)
    (first : KeepsP project work) : KeepsP project (f <$>work) := by
  intro before previous result supported
  simp only [StateT.run_map,support_map] at supported
  obtain ⟨middle,called,rfl⟩ := supported
  exact first before previous middle called
private theorem programP {J : Type} {spec : OracleSpec J} (project : S→T)
    (impl : QueryImpl spec (StateT S (StateT P ProbComp))) (leaves : ∀query,KeepsP project (impl query))
    (work : OracleComp spec A) : KeepsP project (simulateQ impl work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pureP project value
  | query_bind query next ih =>
    rw [simulateQ_bind,simulateQ_spec_query]
    exact bindP project _ _ (leaves query) ih
private theorem continueP (project : S→T) (action : RustM A)
    (next : A→StateT S (StateT P ProbComp) (RustM B)) (later : ∀value,KeepsP project (next value)) :
    KeepsP project (match action with | .ok value=>next value | .fail error=>pure (.fail error) | .div=>pure .div) := by
  cases action with
  | ok value => exact later value
  | fail error | div => exact pureP _ _
private theorem resultP (project : S→T) {C : Type} (action : RustM (core.result.Result A C))
    (next : A→StateT S (StateT P ProbComp) (RustM (core.result.Result B C)))
    (later : ∀value,KeepsP project (next value)) :
    KeepsP project (match action with | .ok (.Ok value)=>next value | .ok (.Err error)=>pure (.ok (.Err error)) | .fail error=>pure (.fail error) | .div=>pure .div) := by
  cases action with
  | fail error | div => exact pureP _ _
  | ok reply => cases reply with
    | Ok value => exact later value
    | Err error => exact pureP _ _
private theorem source_records (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : RegistrationRecordPrimitives.Spec.Domain) :
    KeepsP (owners (n:=n) (Auxiliary:=Auxiliary)) (RegistrationNativePlatformServerCompletion.records coins setup codec query) :=
  nativeP _ _ (records setup codec query) coins
private theorem source_outgoing (coins : QueryImpl unifSpec (StateT P ProbComp))
    (sign : registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Spec.Domain) :
    KeepsP (owners (n:=n) (Auxiliary:=Auxiliary)) (RegistrationNativePlatformServerCompletion.outgoing coins sign query) := by
  apply nativeP
  intro before result supported
  simp only [RegistrationNativePlatformServerCompletion.nativeOutgoing,StateT.run,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact outgoing sign query before.world inner called
variable [primitive : AdapterSealPrimitive.Operations]
variable {E : Type}
private theorem seal_query (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocate : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (query : AdapterSealNative.Request) :
    KeepsP (owners (n:=n) (Auxiliary:=Auxiliary)) (RegistrationNativePlatformSourceSeal.handler coins setup codec view failure allocate query) := by
  cases query with
  | reserve before capacity => exact liftP _ _
  | aead plaintext associated nonce key =>
    intro before previous result supported
    rw [RegistrationNativePlatformSourceSeal.handler,RegistrationNativePlatformSourceSeal.aead_run,StateT.run_map,support_map] at supported
    obtain ⟨inner,called,rfl⟩ := supported
    exact nativeP _ _ (record setup codec _) coins before previous inner called
private theorem sealing (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocate : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (request : record_effects.AeadSealRequest) :
    KeepsP (owners (n:=n) (Auxiliary:=Auxiliary)) (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocate request) := by
  intro before previous result supported
  unfold RegistrationNativePlatformSourceSeal.sealing at supported
  simp only [StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,called,later⟩ := supported
  have kept := programP owners _ (seal_query coins setup codec view failure allocate) (AdapterSealNative.execute E request) before previous middle called
  simp only [StateT.run_modify,StateT.run_pure,support_pure,Set.mem_singleton_iff] at later
  obtain ⟨after,rfl,rfl⟩ := later
  exact kept
omit primitive in
private theorem source_hash (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (erased transcript : commitment.CommitmentTranscript) :
    KeepsP (owners (n:=n) (Auxiliary:=Auxiliary)) (RegistrationNativePlatformSourceSeal.hash coins setup codec erased transcript) := by
  unfold RegistrationNativePlatformSourceSeal.hash
  exact bindP _ _ _ (source_records coins setup codec _) (fun _=>pureP _ _)
omit primitive in
private theorem source_write (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (request : record_effects.RecordWriteRequest) :
    KeepsP (owners (n:=n) (Auxiliary:=RegistrationServerRoleBackend.State)) (RegistrationNativePlatformSourceBuild.write helper request) := by
  intro before previous result supported
  rw [RegistrationNativePlatformSourceBuild.write_run,StateT.run_map,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  rfl
omit primitive in
private theorem source_encode (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (view : registration.SignedResponseView) :
    KeepsP (owners (n:=n) (Auxiliary:=RegistrationServerRoleBackend.State)) (RegistrationNativePlatformSourceBuild.encode writer view) :=
  liftP _ _
omit primitive in
private theorem recordContinueP (project : S→T) (action : RustM A)
    (next : A→StateT S (StateT P ProbComp) (RustM (RegistrationServerRecordExecutor.Result)))
    (later : ∀value,KeepsP project (next value)) :
    KeepsP project (RegistrationNativePlatformServerRecord.continueWith action next) := by
  cases action with
  | ok value => exact later value
  | fail error | div => exact pureP _ _
omit primitive in
private theorem recordResultP (project : S→T) (action : RustM (core.result.Result A pqxdh.ServerState))
    (next : A→StateT S (StateT P ProbComp) (RustM (RegistrationServerRecordExecutor.Result)))
    (later : ∀value,KeepsP project (next value)) :
    KeepsP project (RegistrationNativePlatformServerRecord.continueResult action next) := by
  cases action with
  | fail error | div => exact pureP _ _
  | ok reply => cases reply with
    | Ok value => exact later value
    | Err error => exact pureP _ _
omit primitive in
private theorem publicationContinueP {Encoded : Type} (project : S→T) (action : RustM A)
    (next : A→StateT S (StateT P ProbComp) (RustM (RegistrationWorldServerPublication.Result Encoded)))
    (later : ∀value,KeepsP project (next value)) :
    KeepsP project (RegistrationNativePlatformServerPublication.continueWith action next) := by
  cases action with
  | ok value => exact later value
  | fail error | div => exact pureP _ _
omit primitive in
private theorem publicationResultP {Encoded : Type} (project : S→T) (action : RustM (core.result.Result A pqxdh.ServerState))
    (next : A→StateT S (StateT P ProbComp) (RustM (RegistrationWorldServerPublication.Result Encoded)))
    (later : ∀value,KeepsP project (next value)) :
    KeepsP project (RegistrationNativePlatformServerPublication.continueResult action next) := by
  cases action with
  | fail error | div => exact pureP _ _
  | ok reply => cases reply with
    | Ok value => exact later value
    | Err error => exact pureP _ _
omit primitive in
private theorem completionContinueP {Encoded : Type} (project : S→T) (action : RustM A)
    (next : A→StateT S (StateT P ProbComp) (RustM (RegistrationWorldServerCompletion.Result Encoded)))
    (later : ∀value,KeepsP project (next value)) :
    KeepsP project (RegistrationNativePlatformServerCompletion.continueWith action next) := by
  cases action with
  | ok value => exact later value
  | fail error | div => exact pureP _ _
omit primitive in
private theorem completionResultP {Encoded : Type} (project : S→T) (action : RustM (core.result.Result A pqxdh.ServerState))
    (next : A→StateT S (StateT P ProbComp) (RustM (RegistrationWorldServerCompletion.Result Encoded)))
    (later : ∀value,KeepsP project (next value)) :
    KeepsP project (RegistrationNativePlatformServerCompletion.continueResult action next) := by
  cases action with
  | fail error | div => exact pureP _ _
  | ok reply => cases reply with
    | Ok value => exact later value
    | Err error => exact pureP _ _
namespace Completion
variable {Encoded : Type}
variable (project : S→T)
variable (record : QueryImpl RegistrationRecordPrimitives.Spec (StateT S (StateT P ProbComp)))
variable (sealing : record_effects.AeadSealRequest→StateT S (StateT P ProbComp) (RustM (core.option.Option (Slice U8×Std.Array U8 16#usize))))
variable (write : record_effects.RecordWriteRequest→StateT S (StateT P ProbComp) (RustM (core.option.Option (Slice U8))))
variable (sign : QueryImpl RegistrationSigningShared.Spec (StateT S (StateT P ProbComp)))
variable (encode : registration.SignedResponseView→StateT S (StateT P ProbComp) (RustM (core.option.Option Encoded)))
variable (records : ∀query,KeepsP project (record query))
variable (sealed : ∀request,KeepsP project (sealing request))
variable (written : ∀request,KeepsP project (write request))
variable (signed : ∀query,KeepsP project (sign query))
variable (encoded : ∀view,KeepsP project (encode view))
omit primitive in
include written in
private theorem fromWrite (pending : registration.ServerRecordWrite) : KeepsP project (RegistrationNativePlatformServerRecord.fromWrite write pending) := by
  unfold RegistrationNativePlatformServerRecord.fromWrite
  apply recordContinueP
  intro request
  exact bindP _ _ _ (written request) (fun _=>pureP _ _)
omit primitive in
include records written in
private theorem fromCommitment (pending : registration.ServerRecordCommitment) : KeepsP project (RegistrationNativePlatformServerRecord.fromCommitment record write pending) := by
  unfold RegistrationNativePlatformServerRecord.fromCommitment
  apply recordContinueP
  intro transcript
  apply bindP _ _ _ (records (.hash transcript))
  intro digest
  exact recordResultP _ _ _ (fromWrite project write written)
omit primitive in
include records sealed written in
private theorem fromAead (pending : registration.ServerRecordAead) : KeepsP project (RegistrationNativePlatformSourceRecord.fromAead record sealing write pending) := by
  unfold RegistrationNativePlatformSourceRecord.fromAead
  apply recordContinueP
  intro request
  apply bindP _ _ _ (sealed request)
  intro optional
  exact recordResultP _ _ _ (fromCommitment project record write records written)
omit primitive in
include records sealed written in
private theorem fromRatchet (pending : registration.ServerInitialSeal) : KeepsP project (RegistrationNativePlatformSourceRecord.fromRatchet record sealing write pending) := by
  unfold RegistrationNativePlatformSourceRecord.fromRatchet
  apply recordContinueP
  intro request
  apply bindP _ _ _ (records (.ratchetKdf request))
  intro reply
  exact recordResultP _ _ _ (fromAead project record sealing write records sealed written)
omit primitive in
include records sealed written in
private theorem fromInitial (pending : registration.ServerInitialKdf) : KeepsP project (RegistrationNativePlatformSourceRecord.fromInitial record sealing write pending) := by
  unfold RegistrationNativePlatformSourceRecord.fromInitial
  apply recordContinueP
  intro request
  apply bindP _ _ _ (records (.initialKdf request))
  intro reply
  exact recordResultP _ _ _ (fromRatchet project record sealing write records sealed written)
omit primitive in
include encoded in
private theorem ready (pending : registration.ServerResponseReady) : KeepsP project (RegistrationNativePlatformServerPublication.ready encode pending) := by
  unfold RegistrationNativePlatformServerPublication.ready
  apply publicationContinueP
  intro view
  exact bindP _ _ _ (encoded view) (fun _=>pureP _ _)
omit primitive in
include signed encoded in
private theorem signing (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest) (pending : registration.ServerResponseSigning) :
    KeepsP project (RegistrationNativePlatformServerPublication.signing sign encode payload digest pending) := by
  unfold RegistrationNativePlatformServerPublication.signing
  apply publicationContinueP
  intro request
  apply bindP _ _ _ (signed (.sign request payload digest))
  intro signature
  exact publicationResultP _ _ _ (ready project encode encoded)
omit primitive in
include signed encoded in
private theorem publication (pending : registration.ServerResponseHash) : KeepsP project (RegistrationNativePlatformServerPublication.program sign encode pending) := by
  unfold RegistrationNativePlatformServerPublication.program
  apply publicationContinueP
  intro request
  apply bindP _ _ _ (signed (.hash request))
  intro digest
  exact publicationResultP _ _ _ (signing project sign encode signed encoded _ _)
end Completion
omit primitive in
private theorem install_known (keyId : U64) (binding : PeerBinding) (kernel : ConcreteRatchetKernel) :
    Keeps (fun before : PqxdhRecordLiftWorld.State n=>before.owners)
      (PqxdhRecordLiftWorld.effects (.inr (.installServer keyId binding (.known kernel)))) := by
  intro before result supported
  simp only [PqxdhRecordLiftWorld.effects,PqxdhRecordLiftWorld.capability,StateT.run] at supported
  unfold PqxdhRecordLiftWorld.installServer at supported
  cases server : before.server with
  | none =>
    simp only [PqxdhRecordLiftWorld.chargeEffect,server,support_pure,Set.mem_singleton_iff] at supported
    subst result
    rfl
  | some server =>
    simp only [PqxdhRecordLiftWorld.chargeEffect,server] at supported
    split at supported
    · simp only [PqxdhRecordLiftWorld.resolve,PqxdhRecordLiftWorld.markUsed,StateT.run_pure,pure_bind,support_pure,Set.mem_singleton_iff] at supported
      subst result
      rfl
    · simp only [support_pure,Set.mem_singleton_iff] at supported
      subst result
      rfl
omit primitive in
private theorem source_install (coins : QueryImpl unifSpec (StateT P ProbComp)) (control : pqxdh.ServerState)
    (published : registration.PublishedServerResponse (alloc.vec.Vec U8)) :
    KeepsP (owners (n:=n) (Auxiliary:=RegistrationServerRoleBackend.State))
      (RegistrationNativePlatformServerCompletion.installWith (RegistrationNativePlatformServerCompletion.capability coins) control published) := by
  unfold RegistrationNativePlatformServerCompletion.installWith
  apply completionResultP
  intro pending
  apply completionContinueP
  intro keyId
  apply completionContinueP
  intro parts
  apply bindP
  · apply nativeP
    intro before result supported
    simp only [RegistrationWorldServerCompletion.capability,StateT.run,support_map] at supported
    obtain ⟨inner,called,rfl⟩ := supported
    exact install_known keyId (PeerBinding.ofSession parts.1.binding) parts.1.ratchet before.world.1 inner called
  · intro inserted
    exact pureP _ _
private theorem finish (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocate : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    KeepsP (owners (n:=n) (Auxiliary:=RegistrationServerRoleBackend.State))
      (RegistrationNativePlatformSourceBuild.finishSource coins setup codec
        (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocate)
        (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) sign helper writer control pending) := by
  have hashEq : RegistrationNativePlatformSourceSeal.hash (n:=n) (Auxiliary:=RegistrationServerRoleBackend.State) coins setup codec erased=
      fun transcript=>(fun digest=>RustM.ok (digest,erased)) <$>
        RegistrationNativePlatformServerCompletion.records coins setup codec (.hash transcript) := by
    funext transcript
    exact bind_pure_comp _ _
  unfold RegistrationNativePlatformSourceBuild.finishSource RegistrationNativePlatformSourceCompletion.fromInitialSource
  rw [hashEq,RegistrationNativePlatformSourceRecord.fromInitialWithHash_native]
  apply bindP _ _ _ (Completion.fromInitial owners _ _ _ (source_records coins setup codec)
    (sealing coins setup codec view failure allocate) (source_write helper) pending)
  intro recorded
  apply completionResultP
  intro response
  apply bindP _ _ _ (Completion.publication owners _ _ (source_outgoing coins sign) (source_encode writer) response)
  intro published
  exact completionResultP _ _ _ (source_install coins control)
omit primitive in
private theorem worldP (work : StateT (RegistrationServerRootCompiler.Local n) (StateT P ProbComp) A)
    (kept : KeepsP owners work) : KeepsP serverOwners (RegistrationNativePlatformServerSdk.world work) := by
  intro before previous result supported
  change result∈support (((fun inner=>(inner.1,{before with world:=inner.2})) <$>work.run before.world).run previous) at supported
  rw [StateT.run_map,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact kept before.world previous inner called
omit primitive in
private theorem commitP (reply : RustM (RegistrationWorldServerCompletion.Result (alloc.vec.Vec U8))) :
    KeepsP (serverOwners (n:=n)) (RegistrationNativePlatformServerSdk.commit (m:=StateT P ProbComp) reply) := by
  intro before previous result supported
  cases reply with
  | fail error | div =>
    simp only [RegistrationNativePlatformServerSdk.commit,StateT.run] at supported
    subst result
    rfl
  | ok reply =>
    cases reply <;>
      simp only [RegistrationNativePlatformServerSdk.commit,StateT.run] at supported <;>
      subst result <;> rfl
private theorem initialP (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocate : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    KeepsP (serverOwners (n:=n)) (RegistrationNativePlatformCompletionSdk.fromInitial
      (RegistrationNativePlatformExtractedSdkServer.Build.sourceFinish coins setup codec view failure allocate helper erased sign writer) control pending) := by
  rw [RegistrationNativePlatformExtractedSdkServer.Build.finish_current]
  unfold RegistrationNativePlatformCompletionSdk.fromInitial
  exact bindP _ _ _ (worldP _ (finish coins setup codec view failure allocate helper erased sign writer control pending)) commitP
omit primitive in
private theorem presentP (coins : QueryImpl unifSpec (StateT P ProbComp)) (keyId : U64) :
    KeepsP (serverOwners (n:=n)) (RegistrationNativePlatformCompletionSdk.nativePresent coins keyId) := by
  intro before previous result supported
  simp only [RegistrationNativePlatformCompletionSdk.nativePresent,RegistrationNativePlatformServerSdk.world,
    RegistrationNativePlatformServerCompletion.capability,RegistrationNativePlatformServerCompletion.liftNative,
    RegistrationWorldServerCompletion.capability,PqxdhRecordLiftWorld.effects,PqxdhRecordLiftWorld.capability,
    StateT.run,simulateQ_pure,map_pure] at supported
  subst result
  rfl
namespace Outer
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocate : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
variable (erased : commitment.CommitmentTranscript)
variable (sign : registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
variable (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT P ProbComp) Bool)
variable (reserved : KeepsP serverOwners reserve)
include reserved in
private theorem afterOccupancy (control : pqxdh.ServerState) (pending : peer.CompletionLookup) (occupied : Bool) :
    KeepsP serverOwners (RegistrationNativePlatformCompletionSdk.afterOccupancy reserve
      (RegistrationNativePlatformExtractedSdkServer.Build.sourceFinish coins setup codec view failure allocate helper erased sign writer) control pending occupied) := by
  unfold RegistrationNativePlatformCompletionSdk.afterOccupancy
  cases resumed : pending.resume occupied with
  | fail error | div => exact pureP _ _
  | ok reply => cases reply with
    | Err previous => exact pureP _ _
    | Ok initial =>
      apply bindP _ _ _ reserved
      intro admitted
      cases admitted with
      | false => exact pureP _ _
      | true => exact initialP coins setup codec view failure allocate helper erased sign writer control initial
include reserved in
private theorem afterPin (control : pqxdh.ServerState) (token : peer.ConsumedRegistration) (application : Slice U8)
    (pinned : RustM (core.option.Option session.ServerAuthenticationPin)) :
    KeepsP serverOwners (RegistrationNativePlatformCompletionSdk.afterPin reserve (RegistrationNativePlatformCompletionSdk.nativePresent coins)
      (RegistrationNativePlatformExtractedSdkServer.Build.sourceFinish coins setup codec view failure allocate helper erased sign writer) control token application pinned) := by
  unfold RegistrationNativePlatformCompletionSdk.afterPin
  cases pinned with
  | fail error | div => exact pureP _ _
  | ok optional => cases optional with
    | none => exact pureP _ _
    | some pin =>
      dsimp only
      cases began : peer.begin_completion_lookup control pin token application with
      | fail error | div => exact pureP _ _
      | ok reply => cases reply with
        | Err previous => exact pureP _ _
        | Ok pending =>
          dsimp only
          cases requested : pending.request with
          | fail error | div => exact pureP _ _
          | ok keyId =>
            dsimp only
            split
            · exact bindP _ _ _ (presentP coins keyId)
                (afterOccupancy coins setup codec view failure allocate helper erased sign writer reserve reserved control pending)
            · exact pureP _ _
include reserved in
private theorem complete (token : peer.ConsumedRegistration) (application : Slice U8) :
    KeepsP serverOwners (RegistrationNativePlatformCompletionSdk.complete (RegistrationNativePlatformSourceBuild.pin coins) reserve
      (RegistrationNativePlatformCompletionSdk.nativePresent coins)
      (RegistrationNativePlatformExtractedSdkServer.Build.sourceFinish coins setup codec view failure allocate helper erased sign writer) token application) := by
  unfold RegistrationNativePlatformCompletionSdk.complete
  apply bindP
  · intro before previous result supported
    simp only [StateT.run_get,StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
    subst result
    rfl
  · intro before
    exact bindP _ _ _ (source_pin coins)
      (afterPin coins setup codec view failure allocate helper erased sign writer reserve reserved before.control token application)
end Outer
theorem complete {Allocation : Type}
    (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocate : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest→ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (reserved : StateT P ProbComp Allocation) (admitted : Allocation→Bool)
    (token : peer.ConsumedRegistration) (application : Slice U8)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : P)
    (result : (RustM (Option (U64×alloc.vec.Vec U8))×RegistrationNativeExperiment.State n KemSK source)×P)
    (supported : result∈support (((RegistrationNativePlatformExperiment.server
      (RegistrationNativePlatformCompletionSdk.complete (RegistrationNativePlatformSourceBuild.pin coins)
        (admitted <$>StateT.lift reserved) (RegistrationNativePlatformCompletionSdk.nativePresent coins)
        (RegistrationNativePlatformExtractedSdkServer.Build.sourceFinish coins setup codec view failure allocate helper erased sign writer)
        token application)).run before).run previous)) : image result.1.2=image before := by
  rw [AdapterPublicServerSourceLens.server_run,StateT.run_map,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  have kept := Outer.complete coins setup codec view failure allocate helper erased sign writer
    (admitted <$>StateT.lift reserved) (mapP _ _ _ (liftP _ reserved)) token application before.server previous inner called
  exact congrArg (fun worldOwners=>(before.beacons,before.pool.keys,worldOwners)) kept
omit primitive in
theorem step_support {N Reply : Type} {Private : N→Type} {model : ProbComp (Reply×N)}
    (step : RegistrationNativePlatformExtractedSdkAdaptive.Step Private model)
    (packet : step.Packet) (supported : packet∈support step.sample) : step.native packet∈support model := by
  have mapped : step.native packet∈support (step.native <$>step.sample) := by
    rw [support_map]
    exact ⟨packet,supported,rfl⟩
  exact (congrArg (fun distribution=>step.native packet∈support distribution) step.native_exact).mp mapped
omit primitive in
theorem material [ed : AdapterInitEdPrimitive.Operations] [material : PublicWrapperPlatform.Material] [PublicWrapperPlatform.Platform]
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (objects : Nat→Option beaconcrypt_public_wrapper.beacon.Beacon)
    (before after : RegistrationNativeExperiment.State n KemSK source)
    (same : image after=image before)
    (prior : RegistrationNativePlatformExtractedSdkCarrier.BeaconTable view joint objects before)
    (indexed : RegistrationNativeHiddenAllocationOwners.NativeIndexed before.beacons)
    (allocated : before.server.world.world.1.owners.length=before.beacons.length) :
    RegistrationNativePlatformExtractedSdkCarrier.BeaconTable view joint objects after ∧
      RegistrationNativeHiddenAllocationOwners.NativeIndexed after.beacons ∧
      after.server.world.world.1.owners.length=after.beacons.length := by
  have sameBeacons := congrArg (fun fields=>fields.1) same
  have sameKeys := congrArg (fun fields=>fields.2.1) same
  have sameOwners := congrArg (fun fields=>fields.2.2) same
  change after.beacons=before.beacons at sameBeacons
  change after.pool.keys=before.pool.keys at sameKeys
  change after.server.world.world.1.owners=before.server.world.world.1.owners at sameOwners
  refine ⟨?_,?_,?_⟩
  · intro index
    have held := prior index
    simp only [sameBeacons,sameOwners] at held ⊢
    cases found : before.beacons[index]? with
    | none => simpa only [found] using held
    | some owner =>
      dsimp only at held ⊢
      simp only [found] at held
      obtain ⟨self,objectEq,related⟩ := held
      refine ⟨self,objectEq,related.identityPublic,related.identitySecret,related.mldsa,related.pin,
        related.serverPublic,related.identifier,?_⟩
      simpa only [AdapterPublicWrapperState.Phase,AdapterPublicWrapperState.KemPair,sameKeys] using related.phase
  · simpa only [sameBeacons] using indexed
  · simpa only [sameOwners,sameBeacons] using allocated
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconFrame.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconFrame.accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconFrame.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconFrame.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconFrame.step_support' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconFrame.step_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconFrame.material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconFrame.material
