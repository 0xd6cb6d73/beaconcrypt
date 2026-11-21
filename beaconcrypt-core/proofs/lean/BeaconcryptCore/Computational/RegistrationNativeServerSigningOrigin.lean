-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeResponseStageContents

/-! Actual Server signing receipts identify the source hash capability even when signing, dynamic encoding or later installation fails. This keeps unsigned issuance provenance separate from successful peer publication. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerSigningOrigin
open RegistrationSigningShared (SignReply Receipt)
open RegistrationWorldServerPublication (program signing continueWith continueResult)
open BeaconcryptCore.Refinement.RegistrationSigningTrace (Command replyBytes)
open BeaconcryptCore.Refinement.RegistrationInputs (hashBytes)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {Auxiliary Encoded Value ι KemSK Reader Response : Type} {base : OracleSpec ι}

private theorem hash_receipts (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (request : registration.HashRequest) (before : RegistrationSigningShared.State)
    (result : CtxRomAuth.CtxDigest × RegistrationSigningShared.State)
    (supported : result ∈ support ((RegistrationSigningShared.implementation sign (.hash request)).run before)) :
    result.2.1 = before.1 := by
  simp only [RegistrationSigningShared.implementation, MldsaSharedNative.authentication, StateT.run, support_map] at supported
  obtain ⟨inner, _queried, same⟩ := supported
  exact (congrArg (fun value : CtxRomAuth.CtxDigest × RegistrationSigningShared.State => value.2.1) same).symm

/-- Every supported response hash/sign continuation appends exactly its actual selected key, unsigned source payload, returned digest and optional signature reply, before any later outcome. -/
theorem program_receipt (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) (before : RegistrationSigningShared.State)
    (result : RustM (RegistrationWorldServerPublication.Result Encoded) × RegistrationSigningShared.State)
    (supported : result ∈ support ((simulateQ (RegistrationSigningShared.implementation sign) (program encode pending)).run before)) :
    ∃ digest signature, result.2.1 = before.1 ++
      [(⟨⟨pending.binding.server_pin.public_key, Command.payload (.server pending), replyBytes signature⟩, digest⟩ : Receipt)] := by
  obtain ⟨request, requested, payload⟩ := BeaconcryptCore.Refinement.RegistrationSigningTrace.command_request_exact (.server pending)
  change pending.request = .ok request at requested
  simp only [program, requested, continueWith, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨hashed, queried, continued⟩ := supported
  have prior := hash_receipts sign request before hashed queried
  obtain ⟨next, resumed, _candidate, binding, _kernel, _ciphertext, _input, _request⟩ :=
    BeaconcryptCore.Refinement.RegistrationPublication.server_response_hash_refines pending
      (RegistrationAuthenticationShared.digestArray hashed.1)
  rw [resumed] at continued
  change result ∈ support ((simulateQ (RegistrationSigningShared.implementation sign)
    (signing encode ⟨.server, hashBytes request⟩ hashed.1 next)).run hashed.2) at continued
  rw [RegistrationWorldServerPublication.signing_run, support_map] at continued
  obtain ⟨signature, _signed, same⟩ := continued
  have payloadEq : (⟨.server, hashBytes request⟩ : MldsaTranscriptAuth.Payload) = Command.payload (.server pending) :=
    congrArg (MldsaTranscriptAuth.Payload.mk .server) payload
  refine ⟨hashed.1, signature, ?_⟩
  have receipts := (congrArg (fun value : RustM (RegistrationWorldServerPublication.Result Encoded) × RegistrationSigningShared.State => value.2.1) same).symm
  simpa only [prior, binding, payloadEq] using receipts

/-- The actual instrumented World retains the same source-stage issuance receipt on every optional publication outcome. -/
theorem world_receipt (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) (before : RegistrationWorldSigning.State n)
    (result : RustM (RegistrationWorldServerPublication.Result Encoded) × RegistrationWorldSigning.State n)
    (supported : result ∈ support ((simulateQ (RegistrationWorldSigning.outgoing sign) (program encode pending)).run before)) :
    ∃ digest signature, result.2.2 = before.2 ++
      [(⟨⟨pending.binding.server_pin.public_key, Command.payload (.server pending), replyBytes signature⟩, digest⟩ : Receipt)] := by
  apply program_receipt sign encode pending (RegistrationWorldSigning.project before)
    (result.1, RegistrationWorldSigning.project result.2)
  rw [← RegistrationWorldServerPublication.world_project, support_map]
  exact ⟨result, supported, rfl⟩

private theorem shared_receipts (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : MldsaSharedNative.Spec.Domain) (before : RegistrationWorldAgreement.State n Auxiliary)
    (result : MldsaSharedNative.Spec.Range query × RegistrationWorldAgreement.State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldRecords.shared setup codec query).run before)) :
    result.2.world.2 = before.world.2 := by
  cases query with
  | inl query =>
      simp only [RegistrationWorldRecords.shared, StateT.run, support_map] at supported
      obtain ⟨inner, _possible, same⟩ := supported
      cases same
      rfl
  | inr query =>
      simp only [RegistrationWorldRecords.shared, RegistrationWorldRecords.record, StateT.run, support_map] at supported
      obtain ⟨inner, _possible, same⟩ := supported
      cases same
      rfl
private theorem shared_program_receipts (setup : Setup base KemSK) (codec : Codec Reader Response)
    (work : OracleComp MldsaSharedNative.Spec Value) (before : RegistrationWorldAgreement.State n Auxiliary)
    (result : Value × RegistrationWorldAgreement.State n Auxiliary)
    (supported : result ∈ support ((simulateQ (RegistrationWorldRecords.shared setup codec) work).run before)) :
    result.2.world.2 = before.world.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, queried, continued⟩ := supported
      exact (ih middle.1 middle.2 result continued).trans (shared_receipts setup codec query before middle queried)
private theorem record_receipts (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RegistrationRecordPrimitives.Spec.Domain) (before : RegistrationWorldAgreement.State n Auxiliary)
    (result : RegistrationRecordPrimitives.Spec.Range query × RegistrationWorldAgreement.State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldRecords.handler setup codec query).run before)) :
    result.2.world.2 = before.world.2 := by
  simp only [RegistrationWorldRecords.handler, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact shared_program_receipts setup codec (RegistrationRecordPrimitives.callbacks setup.source query) before inner possible
private theorem records_receipts (setup : Setup base KemSK) (codec : Codec Reader Response)
    (work : OracleComp RegistrationRecordPrimitives.Spec Value) (before : RegistrationWorldAgreement.State n Auxiliary)
    (result : Value × RegistrationWorldAgreement.State n Auxiliary)
    (supported : result ∈ support ((simulateQ (RegistrationWorldRecords.handler setup codec) work).run before)) :
    result.2.world.2 = before.world.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, queried, continued⟩ := supported
      exact (ih middle.1 middle.2 result continued).trans (record_receipts setup codec query before middle queried)

private theorem capability_receipts (query : PqxdhRecordLiftInterface.Capability n)
    (before : RegistrationWorldAgreement.State n Auxiliary)
    (result : (PqxdhRecordLiftInterface.CapabilitySpec n).Range query × RegistrationWorldAgreement.State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldServerCompletion.capability query).run before)) :
    result.2.world.2 = before.world.2 := by
  simp only [RegistrationWorldServerCompletion.capability, StateT.run, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  rfl
private theorem install_receipts (control : pqxdh.ServerState)
    (published : registration.PublishedServerResponse Encoded) (before : RegistrationWorldAgreement.State n Auxiliary)
    (result : RustM (RegistrationWorldServerCompletion.Result Encoded) × RegistrationWorldAgreement.State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldServerCompletion.install control published).run before)) :
    result.2.world.2 = before.world.2 := by
  obtain ⟨prepared, preparedRun, _fields⟩ := BeaconcryptCore.Refinement.PeerOwnership.peer_insert_begin_retains control published
  cases prepared with
  | Err previous =>
      simp only [RegistrationWorldServerCompletion.install, preparedRun] at supported
      change result ∈ support (pure ((.ok (.Err previous) : RustM (RegistrationWorldServerCompletion.Result Encoded)), before) :
        ProbComp (RustM (RegistrationWorldServerCompletion.Result Encoded) × RegistrationWorldAgreement.State n Auxiliary)) at supported
      simp only [support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | Ok pending =>
      rw [RegistrationWorldServerCompletion.install_native control published pending preparedRun,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, inserted, returned⟩ := supported
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at returned
      cases returned
      exact capability_receipts _ before middle inserted


private theorem pure_receipts {Value : Type} (value : Value) (before : RegistrationWorldAgreement.State n Auxiliary)
    (result : Value × RegistrationWorldAgreement.State n Auxiliary)
    (supported : result ∈ support ((pure value : StateT (RegistrationWorldAgreement.State n Auxiliary) ProbComp Value).run before)) :
    result.2.world.2 = before.world.2 := by
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem completion_signing_receipt (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) (before : RegistrationWorldAgreement.State n Auxiliary)
    (result : RustM (RegistrationWorldServerPublication.Result Encoded) × RegistrationWorldAgreement.State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldServerCompletion.signing sign encode pending).run before)) :
    ∃ digest signature, result.2.world.2 = before.world.2 ++
      [(⟨⟨pending.binding.server_pin.public_key, Command.payload (.server pending), replyBytes signature⟩, digest⟩ : Receipt)] := by
  simp only [RegistrationWorldServerCompletion.signing, StateT.run, support_map] at supported
  obtain ⟨inner, reached, same⟩ := supported
  cases same
  exact world_receipt sign encode pending before.world inner reached

/-- Hash/sign issuance provenance remains literal after every installation success or failure, including failed signing and encoding. -/
theorem publish_receipt (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerResponseHash)
    (before : RegistrationWorldAgreement.State n Auxiliary)
    (result : RustM (RegistrationWorldServerCompletion.Result Encoded) × RegistrationWorldAgreement.State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldServerCompletion.publish sign encode control pending).run before)) :
    ∃ digest signature, result.2.world.2 = before.world.2 ++
      [(⟨⟨pending.binding.server_pin.public_key, Command.payload (.server pending), replyBytes signature⟩, digest⟩ : Receipt)] := by
  rw [RegistrationWorldServerCompletion.publish, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨signed, middle⟩, queried, continued⟩ := supported
  obtain ⟨digest, signature, recorded⟩ := completion_signing_receipt sign encode pending before (signed, middle) queried
  have retained : result.2.world.2 = middle.world.2 := by
    cases signed with
    | fail error | div => exact pure_receipts _ middle result continued
    | ok answer => cases answer with
      | Err previous => exact pure_receipts _ middle result continued
      | Ok published => exact install_receipts control published middle result continued
  exact ⟨digest, signature, retained.trans recorded⟩

/-- Every newly issued response from the actual first-record controller has its same-run source hash stage and five-callback initial path, even if the public completion ultimately fails. -/
theorem fromInitial_stage (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf)
    (before : RegistrationWorldAgreement.State n Auxiliary)
    (result : RustM (RegistrationWorldServerCompletion.Result Encoded) × RegistrationWorldAgreement.State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldServerCompletion.fromInitial setup codec sign encode control initial).run before)) :
    result.2.world.2 = before.world.2 ∨
      ∃ hashed middle digest signature,
        (.ok (.Ok hashed), middle) ∈ support ((simulateQ (RegistrationWorldRecords.handler setup codec)
          (RegistrationServerRecordExecutor.fromInitial initial)).run before) ∧
        RegistrationServerRecordExecutor.Path initial hashed ∧
        result.2.world.2 = before.world.2 ++
          [(⟨⟨hashed.binding.server_pin.public_key, Command.payload (.server hashed), replyBytes signature⟩, digest⟩ : Receipt)] := by
  rw [RegistrationWorldServerCompletion.fromInitial, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨recorded, middle⟩, queried, continued⟩ := supported
  have old : middle.world.2 = before.world.2 := records_receipts setup codec (RegistrationServerRecordExecutor.fromInitial initial) before (recorded, middle) queried
  cases recorded with
  | fail error | div => exact Or.inl ((pure_receipts _ middle result continued).trans old)
  | ok answer => cases answer with
    | Err previous => exact Or.inl ((pure_receipts _ middle result continued).trans old)
    | Ok hashed =>
        obtain ⟨digest, signature, appended⟩ := publish_receipt sign encode control hashed middle result continued
        have path : RegistrationServerRecordExecutor.Path initial hashed := by
          apply RegistrationServerRecordExecutor.fromInitial_path
          apply OracleComp.support_simulateQ_run'_subset (RegistrationWorldRecords.handler setup codec)
            (RegistrationServerRecordExecutor.fromInitial initial) before
          rw [StateT.run'_eq, support_map]
          exact Set.mem_image_of_mem Prod.fst queried
        exact Or.inr ⟨hashed, middle, digest, signature, queried, path, by simpa only [old] using appended⟩

end BeaconcryptCore.Computational.RegistrationNativeServerSigningOrigin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerSigningOrigin.program_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerSigningOrigin.program_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerSigningOrigin.world_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerSigningOrigin.world_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerSigningOrigin.publish_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerSigningOrigin.publish_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerSigningOrigin.fromInitial_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerSigningOrigin.fromInitial_stage
