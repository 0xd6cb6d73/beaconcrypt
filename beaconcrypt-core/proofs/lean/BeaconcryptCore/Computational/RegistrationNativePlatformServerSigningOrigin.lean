-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceFrames
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
import BeaconcryptCore.Computational.RegistrationNativeServerSigningOrigin

/-! Actual source response publication appends exactly the reached Server hash capability's issuance receipt before any later signature, dynamic writer or publication failure. The same Local and external platform poststates are retained. Issuance does not imply completed peer installation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerSigningOrigin
open BeaconcryptCore.Refinement
open RegistrationSigningShared (SignReply Receipt)
open RegistrationNativePlatformServerPublication (program signing ready continueWith continueResult)
open RegistrationServerRootCompiler (Local)
open RegistrationSigningTrace (Command replyBytes)
open RegistrationInputs (hashBytes)
variable {n : Nat} {E Platform Value : Type}

private theorem pure_history (value : Value) (before : Local n) (previous : Platform)
    (result : (Value × Local n) × Platform)
    (supported : result ∈ support (((pure value : StateT (Local n) (StateT Platform ProbComp) Value).run before).run previous)) :
    result.1.2.world.2 = before.world.2 := by
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem encode_history
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (view : registration.SignedResponseView) (before : Local n) (previous : Platform)
    (result : (RustM (Option (alloc.vec.Vec U8)) × Local n) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformSourceBuild.encode writer view).run before).run previous)) :
    result.1.2.world.2 = before.world.2 := by
  simp only [RegistrationNativePlatformSourceBuild.encode, StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  exact (congrArg (fun value => value.1.2.world.2) same).symm

private theorem ready_history
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (pending : registration.ServerResponseReady) (before : Local n) (previous : Platform)
    (result : (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)) × Local n) × Platform)
    (supported : result ∈ support (((ready (RegistrationNativePlatformSourceBuild.encode writer) pending).run before).run previous)) :
    result.1.2.world.2 = before.world.2 := by
  unfold ready continueWith at supported
  cases message : pending.message with
  | fail error | div => simp only [message] at supported; exact pure_history _ before previous result supported
  | ok view =>
    simp only [message, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, continued⟩ := supported
    exact (pure_history _ middle.1.2 middle.2 result continued).trans (encode_history writer view before previous middle called)

private theorem continued_history
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (action : RustM (core.result.Result registration.ServerResponseReady pqxdh.ServerState))
    (before : Local n) (previous : Platform)
    (result : (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)) × Local n) × Platform)
    (supported : result ∈ support (((continueResult action (ready (RegistrationNativePlatformSourceBuild.encode writer))).run before).run previous)) :
    result.1.2.world.2 = before.world.2 := by
  cases action with
  | fail error | div => exact pure_history _ before previous result supported
  | ok outcome => cases outcome with
    | Err prior => exact pure_history _ before previous result supported
    | Ok pending => exact ready_history writer pending before previous result supported

private theorem hash_history (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp SignReply) (request : registration.HashRequest)
    (before : Local n) (previous : Platform) (result : (CtxRomAuth.CtxDigest × Local n) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformServerCompletion.outgoing coins sign (.hash request)).run before).run previous)) :
    result.1.2.world.2 = before.world.2 := by
  have actual : result.1 ∈ support ((RegistrationNativePlatformServerCompletion.nativeOutgoing sign (.hash request)).run before) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous result.2 supported
  simp only [RegistrationNativePlatformServerCompletion.nativeOutgoing, RegistrationWorldSigning.outgoing, StateT.run,
    Functor.map_map, support_map] at actual
  obtain ⟨inner, _called, same⟩ := actual
  exact (congrArg (fun value => value.2.world.2) same).symm

private theorem sign_history (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp SignReply) (request : registration.MldsaSigningRequest)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (before : Local n) (previous : Platform) (result : (SignReply × Local n) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformServerCompletion.outgoing coins sign (.sign request payload digest)).run before).run previous)) :
    result.1.2.world.2 = before.world.2 ++ [(⟨⟨request.public_key, payload, replyBytes result.1.1⟩, digest⟩ : Receipt)] := by
  have actual : result.1 ∈ support ((RegistrationNativePlatformServerCompletion.nativeOutgoing sign (.sign request payload digest)).run before) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous result.2 supported
  simp only [RegistrationNativePlatformServerCompletion.nativeOutgoing, RegistrationWorldSigning.outgoing, StateT.run,
    Functor.map_map, support_map] at actual
  obtain ⟨inner, _called, same⟩ := actual
  have historyEq := (congrArg (fun value => value.2.world.2) same).symm
  have replyEq := congrArg Prod.fst same
  change result.1.2.world.2 = before.world.2 ++ [(⟨⟨request.public_key, payload, replyBytes inner.1⟩, digest⟩ : Receipt)] at historyEq
  change inner.1 = result.1.1 at replyEq
  rw [replyEq] at historyEq
  exact historyEq

private theorem signing_request (pending : registration.ServerResponseSigning) :
    pending.request = .ok ⟨pending.binding.server_pin.public_key, .Server, pending.input, authentication.SIGNING_CONTEXT⟩ := rfl

/-- Every actual source response publication appends its own exact hash/sign attempt receipt, including failed signatures, writer failures and divergence. -/
theorem program_receipt (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (pending : registration.ServerResponseHash) (before : Local n) (previous : Platform)
    (result : (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)) × Local n) × Platform)
    (supported : result ∈ support (((program (RegistrationNativePlatformServerCompletion.outgoing coins sign)
      (RegistrationNativePlatformSourceBuild.encode writer) pending).run before).run previous)) :
    ∃ digest signature, result.1.2.world.2 = before.world.2 ++
      [(⟨⟨pending.binding.server_pin.public_key, Command.payload (.server pending), replyBytes signature⟩, digest⟩ : Receipt)] := by
  obtain ⟨request, requested, payload⟩ := RegistrationSigningTrace.command_request_exact (.server pending)
  change pending.request = .ok request at requested
  simp only [program, requested, continueWith, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨hashed, queried, continued⟩ := supported
  have prior := hash_history coins sign request before previous hashed queried
  obtain ⟨next, resumed, _candidate, binding, _kernel, _ciphertext, _input, _request⟩ :=
    RegistrationPublication.server_response_hash_refines pending (RegistrationAuthenticationShared.digestArray hashed.1.1)
  rw [resumed] at continued
  change result ∈ support (((signing (RegistrationNativePlatformServerCompletion.outgoing coins sign)
    (RegistrationNativePlatformSourceBuild.encode writer) ⟨.server, hashBytes request⟩ hashed.1.1 next).run hashed.1.2).run hashed.2) at continued
  simp only [signing, signing_request, continueWith, StateT.run_bind, mem_support_bind_iff] at continued
  obtain ⟨signed, signedCall, later⟩ := continued
  have appended := sign_history coins sign _ _ _ hashed.1.2 hashed.2 signed signedCall
  have final := continued_history writer (next.resume signed.1.1) signed.1.2 signed.2 result later
  have payloadEq : (⟨.server, hashBytes request⟩ : MldsaTranscriptAuth.Payload) = Command.payload (.server pending) :=
    congrArg (MldsaTranscriptAuth.Payload.mk .server) payload
  refine ⟨hashed.1.1, signed.1.1, ?_⟩
  simpa only [prior, binding, payloadEq] using final.trans appended

private def Quiet {V : Type} (work : StateT (Local n) (StateT Platform ProbComp) V) : Prop :=
  ∀ before previous result, result ∈ support ((work.run before).run previous) → result.1.2.world.2 = before.world.2

private theorem pure_quiet (value : Value) : Quiet (Platform := Platform) (n := n) (pure value) := pure_history value

private theorem bind_quiet {Next : Type}
    (work : StateT (Local n) (StateT Platform ProbComp) Value)
    (next : Value → StateT (Local n) (StateT Platform ProbComp) Next)
    (first : Quiet work) (rest : ∀ value, Quiet (next value)) : Quiet (work >>= next) := by
  intro before previous result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  exact (rest middle.1.1 middle.1.2 middle.2 result continued).trans (first before previous middle called)

private theorem capability_quiet (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (query : PqxdhRecordLiftInterface.Capability n) : Quiet (RegistrationNativePlatformServerCompletion.capability coins query) := by
  intro before previous result supported
  have actual : result.1 ∈ support ((RegistrationWorldServerCompletion.capability query).run before) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous result.2 supported
  simp only [RegistrationWorldServerCompletion.capability, StateT.run, support_map] at actual
  obtain ⟨inner, _called, same⟩ := actual
  exact (congrArg (fun value => value.2.world.2) same).symm

private theorem install_quiet (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (published : registration.PublishedServerResponse (alloc.vec.Vec U8)) :
    Quiet (n := n) (RegistrationNativePlatformServerCompletion.installWith (RegistrationNativePlatformServerCompletion.capability coins) control published) := by
  unfold RegistrationNativePlatformServerCompletion.installWith
  cases moved : peer.begin_peer_insert control published with
  | fail error | div => exact pure_quiet _
  | ok answer => cases answer with
    | Err previous => exact pure_quiet _
    | Ok pending =>
      dsimp only [RegistrationNativePlatformServerCompletion.continueResult]
      cases requested : pending.request with
      | fail error | div => exact pure_quiet _
      | ok keyId =>
        dsimp only [RegistrationNativePlatformServerCompletion.continueWith]
        cases unpacked : pending.into_parts with
        | fail error | div => exact pure_quiet _
        | ok parts =>
          dsimp only [RegistrationNativePlatformServerCompletion.continueWith]
          exact bind_quiet _ _ (capability_quiet coins _) (fun _ => pure_quiet _)

private theorem continuation_quiet {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → StateT (Local n) (StateT Platform ProbComp) (RustM (RegistrationWorldServerCompletion.Result (alloc.vec.Vec U8))))
    (law : ∀ value, Quiet (next value)) : Quiet (RegistrationNativePlatformServerCompletion.continueResult action next) := by
  cases action with
  | fail error | div => exact pure_quiet _
  | ok answer => cases answer with
    | Err previous => exact pure_quiet _
    | Ok value => exact law value

/-- The actual complete publication/install suffix retains exactly that same issuance receipt through every later failure. -/
theorem afterRecord_receipt (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (hashed : registration.ServerResponseHash) (before : Local n) (previous : Platform)
    (result : (RustM (RegistrationWorldServerCompletion.Result (alloc.vec.Vec U8)) × Local n) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformSourceBuildCut.afterRecord coins sign writer control hashed).run before).run previous)) :
    ∃ digest signature, result.1.2.world.2 = before.world.2 ++
      [(⟨⟨hashed.binding.server_pin.public_key, Command.payload (.server hashed), replyBytes signature⟩, digest⟩ : Receipt)] := by
  simp only [RegistrationNativePlatformSourceBuildCut.afterRecord, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  obtain ⟨digest, signature, appended⟩ := program_receipt coins sign writer hashed before previous middle called
  exact ⟨digest, signature, (continuation_quiet _ _ (install_quiet coins control) middle.1.2 middle.2 result continued).trans appended⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformServerSigningOrigin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerSigningOrigin.program_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerSigningOrigin.program_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerSigningOrigin.afterRecord_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerSigningOrigin.afterRecord_receipt
