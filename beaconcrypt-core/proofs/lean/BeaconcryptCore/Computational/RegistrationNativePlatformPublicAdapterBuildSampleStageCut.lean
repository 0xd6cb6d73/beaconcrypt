-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStages
import BeaconcryptCore.Computational.RegistrationNativePlatformPackedState
/-! A selected actual source signing stage determines the earlier successful first-record result and its exact unsigned payload. The proof follows the fixed source request tree, retains the same supported hash/sign calls and poststates, and permits identical signing stages in prior callbacks. Packing preserves the complete native cut and external platform state. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage recorded)
open RegistrationNativePlatformServerPublication
open RegistrationNativePlatformPublicAdapterBuildStages (Spec observation code)
variable {S Log :Type}
variable (implementation :QueryImpl Spec (StateT S ProbComp)) (note :Stage→Log)
local notation "Publication"=>RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))
noncomputable def logged :=recorded implementation (fun query reply=>(observation query reply).map note)
noncomputable def outgoing :QueryImpl RegistrationSigningShared.Spec (StateT (S×List Log) ProbComp):=
  fun query=>logged implementation note (.inr (.inl query))
noncomputable def writer (signed :registration.SignedResponseView) :=logged implementation note (.inr (.inr signed))
private theorem pure_log (value :Publication) (before :S) (past :List Log)
    (result :Publication×(S×List Log))
    (supported :result∈support ((pure value:StateT (S×List Log) ProbComp Publication).run (before,past))) :
    result.2.2=past :=by
  simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
  cases supported
  rfl

theorem ready_log (pending :registration.ServerResponseReady) (before :S) (past :List Log)
    (result :Publication×(S×List Log))
    (supported :result∈support ((ready (writer implementation note) pending).run (before,past))) :
    result.2.2=past :=by
  cases message:pending.message with
  | fail error | div=>
    simp only [ready,message,continueWith] at supported
    exact pure_log _ _ _ _ supported
  | ok signed=>
    simp only [ready,message,continueWith,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨encoded,called,later⟩:=supported
    have final:=pure_log _ _ _ _ later
    simp only [writer,logged,recorded,StateT.run,support_map] at called
    obtain ⟨raw,_called,same⟩:=called
    cases same
    simpa only [observation,List.map_nil,List.append_nil] using final

theorem continued_log (reply :RustM (core.result.Result registration.ServerResponseReady pqxdh.ServerState))
    (before :S) (past :List Log) (result :Publication×(S×List Log))
    (supported :result∈support ((continueResult reply (ready (writer implementation note))).run (before,past))) :
    result.2.2=past :=by
  cases reply with
  | fail error | div=>exact pure_log _ _ _ _ supported
  | ok status=>cases status with
    | Err old=>exact pure_log _ _ _ _ supported
    | Ok pending=>exact ready_log implementation note pending before past result supported

theorem program_log (pending :registration.ServerResponseHash) (before :S) (past :List Log)
    (result :Publication×(S×List Log))
    (supported :result∈support ((program (outgoing implementation note) (writer implementation note) pending).run (before,past))) :
    ∃request digest signature signingRequest hashedState signedState,
      pending.request=.ok request ∧
      ((digest,hashedState):CtxRomAuth.CtxDigest×S)∈support ((implementation (.inr (.inl (.hash request)))).run before) ∧
      ((signature,signedState):RegistrationSigningShared.SignReply×S)∈support
        ((implementation (.inr (.inl (.sign signingRequest (RegistrationSigningTrace.Command.payload (.server pending)) digest)))).run hashedState) ∧
      signingRequest.public_key=pending.binding.server_pin.public_key ∧
      result.2.2=past++[note (.hash request digest),note (.sign signingRequest (RegistrationSigningTrace.Command.payload (.server pending)) digest signature)] :=by
  obtain ⟨request,requested,payload⟩:=RegistrationSigningTrace.command_request_exact (.server pending)
  change pending.request=.ok request at requested
  simp only [program,requested,continueWith,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨hashed,queried,continued⟩:=supported
  simp only [outgoing,logged,recorded,StateT.run,support_map] at queried
  obtain ⟨hashedRaw,hashCalled,same⟩:=queried
  cases same
  obtain ⟨next,resumed,_candidate,_binding,_kernel,_ciphertext,_input,signRequested⟩:=
    RegistrationPublication.server_response_hash_refines pending (RegistrationAuthenticationShared.digestArray hashedRaw.1)
  rw [resumed] at continued
  simp only [continueResult,signing,signRequested,continueWith,StateT.run_bind,mem_support_bind_iff] at continued
  obtain ⟨signed,signedCall,later⟩:=continued
  simp only [outgoing,logged,recorded,StateT.run,support_map] at signedCall
  obtain ⟨signedRaw,actualSign,same⟩:=signedCall
  cases same
  have final:=continued_log implementation note (next.resume signedRaw.1) _ _ result later
  have payloadEq:(⟨.server,RegistrationInputs.hashBytes request⟩:MldsaTranscriptAuth.Payload)=RegistrationSigningTrace.Command.payload (.server pending):=
    congrArg (MldsaTranscriptAuth.Payload.mk .server) payload
  refine ⟨request,hashedRaw.1,signedRaw.1,⟨pending.binding.server_pin.public_key,.Server,next.input,authentication.SIGNING_CONTEXT⟩,hashedRaw.2,signedRaw.2,requested,hashCalled,?_,?_,?_⟩
  · exact Eq.mp (congrArg (fun selected=>signedRaw∈support ((implementation (.inr (.inl (.sign ⟨pending.binding.server_pin.public_key,.Server,next.input,authentication.SIGNING_CONTEXT⟩ selected hashedRaw.1)))).run hashedRaw.2)) payloadEq) actualSign
  · rfl
  · simpa only [observation,RegistrationNativePlatformPublicAdapterSourceTrace.signingObservation,List.map_cons,List.map_nil,List.append_assoc,List.cons_append,List.nil_append,payloadEq] using final

private theorem sign_before (injective :Function.Injective note)
    (initial :registration.ServerInitialKdf) (reply :RustM RegistrationServerRecordExecutor.Result)
    (request :registration.MldsaSigningRequest) (payload :MldsaTranscriptAuth.Payload)
    (digest :CtxRomAuth.CtxDigest) (signature :RegistrationSigningShared.SignReply) (past :List Log)
    (present :note (.sign request payload digest signature)∈past++[note (.firstRecord initial reply)]) :
    note (.sign request payload digest signature)∈past :=by
  rcases List.mem_append.mp present with prior|last
  · exact prior
  · have impossible:=injective (List.mem_singleton.mp last)
    cases impossible

theorem code_cut (injective :Function.Injective note)
    (initial :registration.ServerInitialKdf) (before :S) (past :List Log)
    (result :Publication×(S×List Log))
    (supported :result∈support ((simulateQ (logged implementation note) (code initial)).run (before,past)))
    (request :registration.MldsaSigningRequest) (payload :MldsaTranscriptAuth.Payload)
    (digest :CtxRomAuth.CtxDigest) (signature :RegistrationSigningShared.SignReply)
    (present :note (.sign request payload digest signature)∈result.2.2)
    (fresh :note (.sign request payload digest signature)∉past) :
    ∃hashed firstState hashRequest hashState signState,
      ((.ok (.Ok hashed),firstState):RustM RegistrationServerRecordExecutor.Result×S)∈support
        ((implementation (.inl initial)).run before) ∧
      hashed.request=.ok hashRequest ∧
      ((digest,hashState):CtxRomAuth.CtxDigest×S)∈support
        ((implementation (.inr (.inl (.hash hashRequest)))).run firstState) ∧
      ((signature,signState):RegistrationSigningShared.SignReply×S)∈support
        ((implementation (.inr (.inl (.sign request payload digest)))).run hashState) ∧
      payload=RegistrationSigningTrace.Command.payload (.server hashed) ∧
      request.public_key=hashed.binding.server_pin.public_key ∧
      result.2.2=past++[note (.firstRecord initial (.ok (.Ok hashed))),note (.hash hashRequest digest),note (.sign request payload digest signature)] :=by
  rw [RegistrationNativePlatformPublicAdapterBuildStages.interpret] at supported
  simp only [StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨first,called,later⟩:=supported
  simp only [logged,recorded,StateT.run,support_map] at called
  obtain ⟨raw,firstCalled,same⟩:=called
  cases same
  cases reply:raw.1 with
  | fail error | div=>
    simp only [reply,continueResult] at later
    have kept:=pure_log _ _ _ _ later
    rw [kept] at present
    exact False.elim (fresh (sign_before note injective initial _ request payload digest signature past present))
  | ok status=>cases status with
    | Err old=>
      simp only [reply,continueResult] at later
      have kept:=pure_log _ _ _ _ later
      rw [kept] at present
      exact False.elim (fresh (sign_before note injective initial _ request payload digest signature past present))
    | Ok hashed=>
      simp only [reply,continueResult,observation,List.map_cons,List.map_nil] at later
      obtain ⟨hashRequest,actualDigest,actualSignature,actualRequest,hashState,signState,hashRequested,hashCalled,signCalled,key,events⟩:=
        program_log implementation note hashed raw.2 (past++[note (.firstRecord initial (.ok (.Ok hashed)))]) result later
      have actualEvents:result.2.2=past++[note (.firstRecord initial raw.1),note (.hash hashRequest actualDigest),note (.sign actualRequest (RegistrationSigningTrace.Command.payload (.server hashed)) actualDigest actualSignature)]:=by
        simpa only [reply,List.append_assoc,List.cons_append,List.nil_append] using events
      rw [actualEvents] at present
      rcases List.mem_append.mp present with prior|own
      · exact False.elim (fresh prior)
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at own
        rcases own with first|hash|sign
        · cases injective first
        · cases injective hash
        · obtain ⟨requestEq,payloadEq,digestEq,signatureEq⟩:=Stage.sign.inj (injective sign)
          subst actualRequest
          subst actualDigest
          subst actualSignature
          subst payload
          refine ⟨hashed,raw.2,hashRequest,hashState,signState,?_,hashRequested,hashCalled,?_,rfl,key,?_⟩
          · exact (show raw=(.ok (.Ok hashed),raw.2) from Prod.ext reply rfl) ▸firstCalled
          · exact signCalled
          · simpa only [reply] using actualEvents



theorem shift_source {A :Type} (work :OracleComp Spec A) (before :S) (past :List Log) :
    (fun result:A×(S×List Log)=>(result.1,(result.2.1,past++result.2.2))) <$>
      (simulateQ (logged implementation note) work).run (before,[])=
      (simulateQ (logged implementation note) work).run (before,past) :=by
  let shift :S×List Log→S×List Log:=fun current=>(current.1,past++current.2)
  have same:Prod.map id shift <$>(simulateQ (logged implementation note) work).run (before,[])=
      (simulateQ (logged implementation note) work).run (shift (before,[])):=by
    apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    intro query current
    simp only [logged,recorded,StateT.run,Functor.map_map]
    simp only [Prod.map,id_eq,shift,List.append_assoc]
  have functions:Prod.map id shift=(fun result:A×(S×List Log)=>(result.1,(result.2.1,past++result.2.2))):=by
    funext result
    rfl
  rw [functions] at same
  simpa only [shift,List.append_nil] using same

theorem emitted_cut (injective :Function.Injective note)
    (initial :registration.ServerInitialKdf) (before :S) (past suffix :List Log)
    (result :Publication×(S×List Log))
    (supported :result∈support ((simulateQ (logged implementation note) (code initial)).run (before,past)))
    (observed :result.2.2=past++suffix)
    (request :registration.MldsaSigningRequest) (payload :MldsaTranscriptAuth.Payload)
    (digest :CtxRomAuth.CtxDigest) (signature :RegistrationSigningShared.SignReply)
    (present :note (.sign request payload digest signature)∈suffix) :
    ∃hashed firstState hashRequest hashState signState,
      ((.ok (.Ok hashed),firstState):RustM RegistrationServerRecordExecutor.Result×S)∈support
        ((implementation (.inl initial)).run before) ∧
      hashed.request=.ok hashRequest ∧
      ((digest,hashState):CtxRomAuth.CtxDigest×S)∈support
        ((implementation (.inr (.inl (.hash hashRequest)))).run firstState) ∧
      ((signature,signState):RegistrationSigningShared.SignReply×S)∈support
        ((implementation (.inr (.inl (.sign request payload digest)))).run hashState) ∧
      payload=RegistrationSigningTrace.Command.payload (.server hashed) ∧
      request.public_key=hashed.binding.server_pin.public_key ∧
      suffix=[note (.firstRecord initial (.ok (.Ok hashed))),note (.hash hashRequest digest),note (.sign request payload digest signature)] :=by
  rw [←shift_source implementation note (code initial) before past,support_map] at supported
  obtain ⟨origin,called,same⟩:=supported
  have logs:past++origin.2.2=past++suffix:=(congrArg (fun value:Publication×(S×List Log)=>value.2.2) same).trans observed
  have originSuffix:origin.2.2=suffix:=List.append_cancel_left logs
  have originPresent:note (.sign request payload digest signature)∈origin.2.2:=originSuffix.symm ▸present
  obtain ⟨hashed,first,hashRequest,hash,signed,firstCalled,requested,hashCalled,signCalled,payloadEq,key,events⟩:=
    code_cut implementation note injective initial before [] origin called request payload digest signature originPresent List.not_mem_nil
  refine ⟨hashed,first,hashRequest,hash,signed,firstCalled,requested,hashCalled,signCalled,payloadEq,key,?_⟩
  simpa only [originSuffix,List.nil_append] using events

section Nested
variable {P A :Type}
variable (nested :QueryImpl Spec (StateT S (StateT P ProbComp)))

noncomputable def packed :QueryImpl Spec (StateT (S×P) ProbComp):=
  fun query=>RegistrationNativePlatformPackedState.pack (nested query)

def packLog (reached :(A×(S×List Log))×P):A×((S×P)×List Log):=
  (reached.1.1,((reached.1.2.1,reached.2),reached.1.2.2))

theorem nested_source (work :OracleComp Spec A) (before :S) (previous :P) (past :List Log) :
    packLog <$>((simulateQ (recorded nested (fun query reply=>(observation query reply).map note)) work).run (before,past)).run previous=
      (simulateQ (logged (packed nested) note) work).run ((before,previous),past) :=by
  let associate :((S×List Log)×P)→((S×P)×List Log):=fun state=>((state.1.1,state.2),state.1.2)
  have same:Prod.map id associate <$>(simulateQ
      (fun query=>RegistrationNativePlatformPackedState.pack (recorded nested (fun query reply=>(observation query reply).map note) query)) work).run ((before,past),previous)=
      (simulateQ (logged (packed nested) note) work).run (associate ((before,past),previous)):=by
    apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    intro query current
    simp only [RegistrationNativePlatformPackedState.pack,logged,packed,recorded,StateT.run,Functor.map_map]
    change (fun a:(Spec.Range query×(S×List Log))×P=>Prod.map id associate (a.1.1,(a.1.2,a.2))) <$>
      ((fun result:Spec.Range query×S=>(result.1,(result.2,current.1.2++(observation query result.1).map note))) <$>
        (nested query).run current.1.1).run current.2 = _
    rw [StateT.run_map,Functor.map_map]
    rfl
  rw [←RegistrationNativePlatformPackedState.simulate_pack] at same
  unfold packLog
  simpa only [RegistrationNativePlatformPackedState.pack,StateT.run,Functor.map_map,Prod.map,id_eq,associate] using same

private theorem pack_supported {V :Type} (work :StateT S (StateT P ProbComp) V)
    (before :S) (previous :P) (value :V) (after :S) (next :P) :
    (value,(after,next))∈support ((RegistrationNativePlatformPackedState.pack work).run (before,previous)) ↔
      ((value,after),next)∈support ((work.run before).run previous) :=by
  simp only [RegistrationNativePlatformPackedState.pack,StateT.run,support_map]
  constructor
  · rintro ⟨raw,called,same⟩
    obtain ⟨valueEq,stateEq⟩:=Prod.mk.inj same
    obtain ⟨afterEq,nextEq⟩:=Prod.mk.inj stateEq
    have rawEq:raw=((value,after),next):=Prod.ext (Prod.ext valueEq afterEq) nextEq
    exact rawEq ▸called
  · intro called
    exact ⟨((value,after),next),called,rfl⟩

theorem nested_cut (injective :Function.Injective note)
    (initial :registration.ServerInitialKdf) (before :S) (previous :P) (past :List Log)
    (result :(Publication×(S×List Log))×P)
    (supported :result∈support (((simulateQ (recorded nested (fun query reply=>(observation query reply).map note)) (code initial)).run (before,past)).run previous))
    (request :registration.MldsaSigningRequest) (payload :MldsaTranscriptAuth.Payload)
    (digest :CtxRomAuth.CtxDigest) (signature :RegistrationSigningShared.SignReply)
    (present :note (.sign request payload digest signature)∈result.1.2.2)
    (fresh :note (.sign request payload digest signature)∉past) :
    ∃hashed firstState firstPlatform hashRequest hashState hashPlatform signState signPlatform,
      ((.ok (.Ok hashed),firstState),firstPlatform)∈support (((nested (.inl initial)).run before).run previous) ∧
      hashed.request=.ok hashRequest ∧
      ((digest,hashState),hashPlatform)∈support (((nested (.inr (.inl (.hash hashRequest)))).run firstState).run firstPlatform) ∧
      ((signature,signState),signPlatform)∈support (((nested (.inr (.inl (.sign request payload digest)))).run hashState).run hashPlatform) ∧
      payload=RegistrationSigningTrace.Command.payload (.server hashed) ∧
      request.public_key=hashed.binding.server_pin.public_key ∧
      result.1.2.2=past++[note (.firstRecord initial (.ok (.Ok hashed))),note (.hash hashRequest digest),note (.sign request payload digest signature)] :=by
  have supportedPacked:packLog result∈support ((simulateQ (logged (packed nested) note) (code initial)).run ((before,previous),past)):=by
    rw [←nested_source note nested (code initial) before previous past,support_map]
    exact ⟨result,supported,rfl⟩
  obtain ⟨hashed,first,hashRequest,hash,signed,firstCalled,requested,hashCalled,signCalled,payloadEq,key,events⟩:=
    code_cut (packed nested) note injective initial (before,previous) past (packLog result) supportedPacked request payload digest signature present fresh
  exact ⟨hashed,first.1,first.2,hashRequest,hash.1,hash.2,signed.1,signed.2,
    (pack_supported _ _ _ _ _ _).mp firstCalled,requested,
    (pack_supported _ _ _ _ _ _).mp hashCalled,(pack_supported _ _ _ _ _ _).mp signCalled,payloadEq,key,events⟩
theorem nested_emitted_cut (injective :Function.Injective note)
    (initial :registration.ServerInitialKdf) (before :S) (previous :P) (past suffix :List Log)
    (result :(Publication×(S×List Log))×P)
    (supported :result∈support (((simulateQ (recorded nested (fun query reply=>(observation query reply).map note)) (code initial)).run (before,past)).run previous))
    (observed :result.1.2.2=past++suffix)
    (request :registration.MldsaSigningRequest) (payload :MldsaTranscriptAuth.Payload)
    (digest :CtxRomAuth.CtxDigest) (signature :RegistrationSigningShared.SignReply)
    (present :note (.sign request payload digest signature)∈suffix) :
    ∃hashed firstState firstPlatform hashRequest hashState hashPlatform signState signPlatform,
      ((.ok (.Ok hashed),firstState),firstPlatform)∈support (((nested (.inl initial)).run before).run previous) ∧
      hashed.request=.ok hashRequest ∧
      ((digest,hashState),hashPlatform)∈support (((nested (.inr (.inl (.hash hashRequest)))).run firstState).run firstPlatform) ∧
      ((signature,signState),signPlatform)∈support (((nested (.inr (.inl (.sign request payload digest)))).run hashState).run hashPlatform) ∧
      payload=RegistrationSigningTrace.Command.payload (.server hashed) ∧
      request.public_key=hashed.binding.server_pin.public_key ∧
      suffix=[note (.firstRecord initial (.ok (.Ok hashed))),note (.hash hashRequest digest),note (.sign request payload digest signature)] :=by
  have supportedPacked:packLog result∈support ((simulateQ (logged (packed nested) note) (code initial)).run ((before,previous),past)):=by
    rw [←nested_source note nested (code initial) before previous past,support_map]
    exact ⟨result,supported,rfl⟩
  obtain ⟨hashed,first,hashRequest,hash,signed,firstCalled,requested,hashCalled,signCalled,payloadEq,key,events⟩:=
    emitted_cut (packed nested) note injective initial (before,previous) past suffix (packLog result) supportedPacked observed request payload digest signature present
  exact ⟨hashed,first.1,first.2,hashRequest,hash.1,hash.2,signed.1,signed.2,
    (pack_supported _ _ _ _ _ _).mp firstCalled,requested,
    (pack_supported _ _ _ _ _ _).mp hashCalled,(pack_supported _ _ _ _ _ _).mp signCalled,payloadEq,key,events⟩
end Nested

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut.ready_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut.ready_log

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut.continued_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut.continued_log

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut.program_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut.program_log

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut.code_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut.code_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut.shift_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut.shift_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut.emitted_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut.emitted_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut.nested_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut.nested_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut.nested_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut.nested_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut.nested_emitted_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut.nested_emitted_cut
