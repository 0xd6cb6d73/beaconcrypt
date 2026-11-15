-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
import BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationFrame
import BeaconcryptCore.Refinement.AdapterPublicServerLocalLens
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildCut

/-! Every reached actual prefixed first-record callback preserves the initialized Server record map, including failed allocation, failed sealing and failed writing. The proof follows literal native callbacks and full shared poststates. This derives the material frame required by the enclosing source response installer. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicServerCompletionFrame
open BeaconcryptCore.Computational
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationWorldAgreement (State)
variable {n : Nat} {E Auxiliary Platform Value Next ι KemSK Reader Response : Type} {base : OracleSpec ι}

private structure Relation (S : Type) where
  holds : S → S → Prop
  reflexive : ∀ state, holds state state
  transitive : ∀ first middle last, holds first middle → holds middle last → holds first last

private def Keeps {S : Type} (relation : Relation S)
    (work : StateT S (StateT Platform ProbComp) Value) : Prop :=
  ∀ before previous (result : Value × S) next,
    (result, next) ∈ support ((work.run before).run previous) → relation.holds before result.2

private theorem pure_keeps {S : Type} (relation : Relation S) (value : Value) :
    Keeps (Platform := Platform) relation (pure value : StateT S (StateT Platform ProbComp) Value) := by
  intro before previous result next supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
  rw [congrArg Prod.snd supported.1]
  exact relation.reflexive _

private theorem bind_keeps {S : Type} (relation : Relation S)
    (work : StateT S (StateT Platform ProbComp) Value)
    (next : Value → StateT S (StateT Platform ProbComp) Next)
    (first : Keeps relation work) (rest : ∀ value, Keeps relation (next value)) : Keeps relation (work >>= next) := by
  intro before previous result platform supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨value, middle⟩, current⟩, reached, continued⟩ := supported
  exact relation.transitive before middle result.2
    (first before previous (value, middle) current reached) (rest value middle current result platform continued)

private theorem map_keeps {S X Y : Type} (relation : Relation S) (f : X → Y)
    (work : StateT S (StateT Platform ProbComp) X) (keeps : Keeps relation work) : Keeps relation (f <$> work) := by
  intro before previous result platform supported
  simp only [StateT.run_map, support_map] at supported
  obtain ⟨⟨⟨value, middle⟩, current⟩, reached, equal⟩ := supported
  have stateEq := congrArg (fun result => result.1.2) equal
  rw [← stateEq]
  exact keeps before previous (value, middle) current reached

private theorem simulate_keeps {S I : Type} {spec : OracleSpec I} (relation : Relation S)
    (handler : QueryImpl spec (StateT S (StateT Platform ProbComp)))
    (queryKeeps : ∀ query, Keeps relation (handler query)) (work : OracleComp spec Value) :
    Keeps relation (simulateQ handler work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using pure_keeps relation value
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact bind_keeps relation _ _ (queryKeeps query) ih

private theorem with_keeps {S A : Type} (relation : Relation S) (head : RustM A)
    (next : A → StateT S (StateT Platform ProbComp) (RustM RegistrationServerRecordExecutor.Result)) (rest : ∀ value, Keeps relation (next value)) :
    Keeps relation (RegistrationNativePlatformServerRecord.continueWith head next) := by
  cases head with
  | ok value => exact rest value
  | fail error | div => exact pure_keeps relation _

private theorem result_keeps {S A : Type} (relation : Relation S)
    (head : RustM (core.result.Result A pqxdh.ServerState))
    (next : A → StateT S (StateT Platform ProbComp) (RustM RegistrationServerRecordExecutor.Result))
    (rest : ∀ value, Keeps relation (next value)) :
    Keeps relation (RegistrationNativePlatformServerRecord.continueResult head next) := by
  cases head with
  | fail error | div => exact pure_keeps relation _
  | ok result => cases result with
    | Err prior => exact pure_keeps relation _
    | Ok value => exact rest value

private def frame : Relation (State n Auxiliary) where
  holds before after := after.world.1.server = before.world.1.server
  reflexive _ := rfl
  transitive _ _ _ first second := second.trans first

private theorem raw_server (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (before : State n Auxiliary)
    (result : RawCtxMixedOwner.NativeSpec.Range query × State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldRecords.record setup codec query).run before)) :
    result.2.world.1.server = before.world.1.server := by
  simp only [RegistrationWorldRecords.record, StateT.run, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  cases same
  rfl

private theorem shared_server (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : MldsaSharedNative.Spec.Domain) (before : State n Auxiliary)
    (result : MldsaSharedNative.Spec.Range query × State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldRecords.shared setup codec query).run before)) :
    result.2.world.1.server = before.world.1.server := by
  cases query with
  | inr query => exact raw_server setup codec query before result supported
  | inl query =>
    simp only [RegistrationWorldRecords.shared, StateT.run, support_map] at supported
    obtain ⟨inner, called, same⟩ := supported
    cases same
    exact AdapterPublicServerAuthenticationFrame.hash_server _ _ _ _ called

private theorem handler_server (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RegistrationRecordPrimitives.Spec.Domain) (before : State n Auxiliary)
    (result : RegistrationRecordPrimitives.Spec.Range query × State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldRecords.handler setup codec query).run before)) :
    result.2.world.1.server = before.world.1.server := by
  simp only [RegistrationWorldRecords.handler, StateT.run, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  cases same
  exact simulateQ_run_preservesInv (RegistrationWorldRecords.shared setup codec)
    (fun current => current.world.1.server = before.world.1.server)
    (fun query current original after reached => (shared_server setup codec query current after reached).trans original)
    (RegistrationRecordPrimitives.callbacks setup.source query) before rfl inner called

private theorem records_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (query : RegistrationRecordPrimitives.Spec.Domain) :
    Keeps frame (RegistrationNativePlatformServerCompletion.records (n := n) (Auxiliary := Auxiliary) coins setup codec query) := by
  intro before previous result next supported
  have actual := RegistrationNativePlatformHashReceipt.native_support coins _ result previous next supported
  exact handler_server setup codec query before result actual

private theorem primitive_frame (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (before : State n Auxiliary)
    (result : RawCtxMixedOwner.NativeSpec.Range query × State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldRecords.record setup codec query).run before)) :
    frame.holds before result.2 := raw_server setup codec query before result supported

variable [primitive : AdapterSealPrimitive.Operations]

private theorem aead_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (plaintext : Slice U8) (associated : Option (Slice U8)) (nonce : primitive.Nonce) (key : primitive.Key) :
    Keeps frame (RegistrationNativePlatformSourceSeal.aead (n := n) (Auxiliary := Auxiliary)
      coins setup codec view failure plaintext associated nonce key) := by
  intro before previous result next supported
  change (result, next) ∈ support
    ((fun inner => ((.ok (RegistrationNativePlatformSourceSeal.detached failure inner.1.1), inner.1.2), inner.2)) <$>
      (simulateQ coins ((RegistrationWorldRecords.record setup codec
        (.inr (.inl (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key)))).run before)).run previous) at supported
  rw [support_map] at supported
  obtain ⟨⟨inner, platform⟩, called, equal⟩ := supported
  have stateEq := congrArg (fun value => value.1.2) equal
  rw [← stateEq]
  have actual := RegistrationNativePlatformHashReceipt.native_support coins _ inner previous platform called
  exact primitive_frame setup codec _ before inner actual

private theorem query_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (query : (AdapterSealNative.Spec E).Domain) :
    Keeps frame (RegistrationNativePlatformSourceSeal.handler (n := n) (Auxiliary := Auxiliary)
      coins setup codec view failure allocation query) := by
  cases query with
  | aead plaintext associated nonce key => exact aead_keeps coins setup codec view failure plaintext associated nonce key
  | reserve bytes capacity =>
      intro before previous result next supported
      simp only [RegistrationNativePlatformSourceSeal.handler, StateT.run_lift] at supported
      simp only [bind_pure_comp, StateT.run_map, support_map] at supported
      obtain ⟨⟨reply, platform⟩, _allocated, equal⟩ := supported
      have stateEq := congrArg (fun value => value.1.2) equal
      rw [← stateEq]
      exact frame.reflexive _

private theorem sealing_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (request : record_effects.AeadSealRequest) :
    Keeps frame (RegistrationNativePlatformSourceSeal.sealing (n := n) (Auxiliary := Auxiliary)
      coins setup codec view failure allocation request) := by
  unfold RegistrationNativePlatformSourceSeal.sealing
  apply bind_keeps frame _ _ (simulate_keeps frame _ (query_keeps coins setup codec view failure allocation) _)
  intro result
  apply bind_keeps frame
  · intro before previous returned next supported
    simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
    rw [congrArg Prod.snd supported.1]
    rfl
  · intro _
    exact pure_keeps frame _

omit primitive in
private theorem hash_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased transcript : commitment.CommitmentTranscript) :
    Keeps frame (RegistrationNativePlatformSourceSeal.hash (n := n) (Auxiliary := Auxiliary) coins setup codec erased transcript) := by
  unfold RegistrationNativePlatformSourceSeal.hash
  exact bind_keeps frame _ _ (records_keeps coins setup codec _) (fun _ => pure_keeps frame _)

omit primitive in
private theorem write_keeps (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (request : record_effects.RecordWriteRequest) :
    Keeps frame (RegistrationNativePlatformSourceBuild.write (n := n) helper request) := by
  intro before previous result next supported
  rw [RegistrationNativePlatformSourceBuild.write_joint, support_map] at supported
  obtain ⟨⟨reply, platform⟩, _written, equal⟩ := supported
  have stateEq := congrArg (fun value => value.1.2) equal
  rw [← stateEq]
  rfl

omit primitive in
private theorem fromWrite_keeps {S : Type} (relation : Relation S)
    (write : record_effects.RecordWriteRequest → StateT S (StateT Platform ProbComp) (RustM (Option (Slice U8)))) (writeKeeps : ∀ request, Keeps relation (write request))
    (pending : registration.ServerRecordWrite) :
    Keeps relation (RegistrationNativePlatformServerRecord.fromWrite write pending) := by
  unfold RegistrationNativePlatformServerRecord.fromWrite
  apply with_keeps
  intro request
  exact bind_keeps relation _ _ (writeKeeps request) (fun _ => pure_keeps relation _)

omit primitive in
private theorem fromCommitment_keeps {S : Type} (relation : Relation S)
    (hash : commitment.CommitmentTranscript → StateT S (StateT Platform ProbComp) RegistrationNativePlatformCommitment.HashReply) (write : record_effects.RecordWriteRequest → StateT S (StateT Platform ProbComp) (RustM (Option (Slice U8))))
    (hashKeeps : ∀ transcript, Keeps relation (hash transcript)) (writeKeeps : ∀ request, Keeps relation (write request))
    (pending : registration.ServerRecordCommitment) :
    Keeps relation (RegistrationNativePlatformCommitment.fromCommitment hash write pending) := by
  rw [RegistrationNativePlatformCommitment.normalize]
  apply bind_keeps relation _ _ (hashKeeps _)
  intro result
  apply result_keeps
  intro next
  exact fromWrite_keeps relation write writeKeeps next

omit primitive in
private theorem fromAead_keeps {S : Type} (relation : Relation S)
    (sealing : record_effects.AeadSealRequest → StateT S (StateT Platform ProbComp) (RustM AdapterSealNative.Output))
    (hash : commitment.CommitmentTranscript → StateT S (StateT Platform ProbComp) RegistrationNativePlatformCommitment.HashReply) (write : record_effects.RecordWriteRequest → StateT S (StateT Platform ProbComp) (RustM (Option (Slice U8))))
    (sealKeeps : ∀ request, Keeps relation (sealing request))
    (hashKeeps : ∀ transcript, Keeps relation (hash transcript)) (writeKeeps : ∀ request, Keeps relation (write request))
    (pending : registration.ServerRecordAead) :
    Keeps relation (RegistrationNativePlatformSourceRecord.fromAeadWithHash sealing hash write pending) := by
  unfold RegistrationNativePlatformSourceRecord.fromAeadWithHash
  apply with_keeps
  intro request
  apply bind_keeps relation _ _ (sealKeeps request)
  intro result
  apply result_keeps
  intro next
  exact fromCommitment_keeps relation hash write hashKeeps writeKeeps next

omit primitive in
private theorem fromRatchet_keeps {S : Type} (relation : Relation S)
    (record : QueryImpl RegistrationRecordPrimitives.Spec (StateT S (StateT Platform ProbComp)))
    (sealing : record_effects.AeadSealRequest → StateT S (StateT Platform ProbComp) (RustM AdapterSealNative.Output))
    (hash : commitment.CommitmentTranscript → StateT S (StateT Platform ProbComp) RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → StateT S (StateT Platform ProbComp) (RustM (Option (Slice U8))))
    (recordKeeps : ∀ query, Keeps relation (record query)) (sealKeeps : ∀ request, Keeps relation (sealing request))
    (hashKeeps : ∀ transcript, Keeps relation (hash transcript)) (writeKeeps : ∀ request, Keeps relation (write request))
    (pending : registration.ServerInitialSeal) :
    Keeps relation (RegistrationNativePlatformSourceRecord.fromRatchetWithHash record sealing hash write pending) := by
  unfold RegistrationNativePlatformSourceRecord.fromRatchetWithHash
  apply with_keeps
  intro request
  apply bind_keeps relation _ _ (recordKeeps _)
  intro reply
  apply result_keeps
  intro next
  exact fromAead_keeps relation sealing hash write sealKeeps hashKeeps writeKeeps next

omit primitive in
private theorem fromInitial_keeps {S : Type} (relation : Relation S)
    (record : QueryImpl RegistrationRecordPrimitives.Spec (StateT S (StateT Platform ProbComp)))
    (sealing : record_effects.AeadSealRequest → StateT S (StateT Platform ProbComp) (RustM AdapterSealNative.Output))
    (hash : commitment.CommitmentTranscript → StateT S (StateT Platform ProbComp) RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → StateT S (StateT Platform ProbComp) (RustM (Option (Slice U8))))
    (recordKeeps : ∀ query, Keeps relation (record query)) (sealKeeps : ∀ request, Keeps relation (sealing request))
    (hashKeeps : ∀ transcript, Keeps relation (hash transcript)) (writeKeeps : ∀ request, Keeps relation (write request))
    (pending : registration.ServerInitialKdf) :
    Keeps relation (RegistrationNativePlatformSourceRecord.fromInitialWithHash record sealing hash write pending) := by
  unfold RegistrationNativePlatformSourceRecord.fromInitialWithHash
  apply with_keeps
  intro request
  apply bind_keeps relation _ _ (recordKeeps _)
  intro reply
  apply result_keeps
  intro next
  exact fromRatchet_keeps relation record sealing hash write recordKeeps sealKeeps hashKeeps writeKeeps next

/-- Every actual source first-record outcome preserves the initialized Server records, regardless of later publication success. -/
theorem record_frame (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : registration.ServerInitialKdf) (before : RegistrationServerRootCompiler.Local n) (previous : Platform)
    (result : RustM RegistrationServerRecordExecutor.Result × RegistrationServerRootCompiler.Local n) (next : Platform)
    (supported : (result, next) ∈ support
      (((RegistrationNativePlatformSourceSealTrace.record coins setup codec view failure allocation erased helper initial).run before).run previous)) :
    result.2.world.1.server = before.world.1.server := by
  exact fromInitial_keeps frame
    (RegistrationNativePlatformServerCompletion.records coins setup codec)
    (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
    (RegistrationNativePlatformSourceSeal.hash coins setup codec erased)
    (RegistrationNativePlatformSourceBuild.write helper)
    (records_keeps coins setup codec) (sealing_keeps coins setup codec view failure allocation)
    (hash_keeps coins setup codec erased) (write_keeps helper) initial before previous result next supported


omit primitive in
private theorem sampled_server {A : Type} (work : ProbComp A) (before : PqxdhRecordLiftWorld.State n)
    (result : A × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.sampled work).run before)) :
    result.2.server = before.server := by
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  cases same
  rfl

omit primitive in
private theorem pub_with_keeps {S A Encoded : Type} (relation : Relation S) (head : RustM A)
    (next : A → StateT S (StateT Platform ProbComp) (RustM (RegistrationWorldServerPublication.Result Encoded)))
    (rest : ∀ value, Keeps relation (next value)) :
    Keeps relation (RegistrationNativePlatformServerPublication.continueWith head next) := by
  cases head with
  | ok value => exact rest value
  | fail error | div => exact pure_keeps relation _

omit primitive in
private theorem pub_result_keeps {S A Encoded : Type} (relation : Relation S)
    (head : RustM (core.result.Result A pqxdh.ServerState))
    (next : A → StateT S (StateT Platform ProbComp) (RustM (RegistrationWorldServerPublication.Result Encoded)))
    (rest : ∀ value, Keeps relation (next value)) :
    Keeps relation (RegistrationNativePlatformServerPublication.continueResult head next) := by
  cases head with
  | fail error | div => exact pure_keeps relation _
  | ok result => cases result with
    | Err prior => exact pure_keeps relation _
    | Ok value => exact rest value

omit primitive in
private theorem outgoing_cache (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Spec.Domain) :
    Keeps frame (RegistrationNativePlatformServerCompletion.outgoing (n := n) (Auxiliary := Auxiliary) coins sign query) := by
  intro before previous result next supported
  have actual := RegistrationNativePlatformHashReceipt.native_support coins _ result previous next supported
  simp only [RegistrationNativePlatformServerCompletion.nativeOutgoing, StateT.run, support_map] at actual
  obtain ⟨inner, called, equal⟩ := actual
  have stateEq := congrArg Prod.snd equal
  rw [← stateEq]
  cases query with
  | hash request =>
      simp only [RegistrationWorldSigning.outgoing, StateT.run, support_map] at called
      obtain ⟨effect, reached, equal⟩ := called
      have worldEq := congrArg (fun value => value.2.1) equal
      change inner.2.1.server = before.world.1.server
      rw [← worldEq]
      exact AdapterPublicServerAuthenticationFrame.hash_server _ before.world.1 effect.2 effect.1 reached
  | sign request payload digest =>
      simp only [RegistrationWorldSigning.outgoing, StateT.run, support_map] at called
      obtain ⟨effect, reached, equal⟩ := called
      have worldEq := congrArg (fun value => value.2.1) equal
      change inner.2.1.server = before.world.1.server
      rw [← worldEq]
      exact sampled_server (sign request) before.world.1 effect reached

omit primitive in
private theorem encode_cache
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (view : registration.SignedResponseView) :
    Keeps frame (RegistrationNativePlatformSourceBuild.encode (n := n) writer view) := by
  intro before previous result next supported
  rw [RegistrationNativePlatformSourceBuild.encode_run, StateT.run_map, support_map] at supported
  obtain ⟨⟨answer, platform⟩, _encoded, equal⟩ := supported
  have stateEq := congrArg (fun value => value.1.2) equal
  rw [← stateEq]
  rfl

omit primitive in
private theorem publication_ready_cache
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (pending : registration.ServerResponseReady) :
    Keeps frame (RegistrationNativePlatformServerPublication.ready
      (RegistrationNativePlatformSourceBuild.encode (n := n) writer) pending) := by
  unfold RegistrationNativePlatformServerPublication.ready
  apply pub_with_keeps frame
  intro view
  exact bind_keeps frame _ _ (encode_cache writer view) (fun _ => pure_keeps frame _)

omit primitive in
private theorem publication_signing_cache (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest) (pending : registration.ServerResponseSigning) :
    Keeps frame (RegistrationNativePlatformServerPublication.signing
      (RegistrationNativePlatformServerCompletion.outgoing (n := n) coins sign)
      (RegistrationNativePlatformSourceBuild.encode writer) payload digest pending) := by
  unfold RegistrationNativePlatformServerPublication.signing
  apply pub_with_keeps frame
  intro request
  apply bind_keeps frame _ _ (outgoing_cache coins sign _)
  intro reply
  exact pub_result_keeps frame _ _ (publication_ready_cache writer)

omit primitive in
private theorem publication_cache (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (pending : registration.ServerResponseHash) :
    Keeps frame (RegistrationNativePlatformServerPublication.program
      (RegistrationNativePlatformServerCompletion.outgoing (n := n) coins sign)
      (RegistrationNativePlatformSourceBuild.encode writer) pending) := by
  unfold RegistrationNativePlatformServerPublication.program
  apply pub_with_keeps frame
  intro request
  apply bind_keeps frame _ _ (outgoing_cache coins sign _)
  intro digest
  exact pub_result_keeps frame _ _ (publication_signing_cache coins sign writer _ digest)

omit primitive in
theorem publication_frame (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (pending : registration.ServerResponseHash) (before : RegistrationServerRootCompiler.Local n) (previous : Platform)
    (result : RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)) × RegistrationServerRootCompiler.Local n) (next : Platform)
    (supported : (result, next) ∈ support
      (((RegistrationNativePlatformServerPublication.program
        (RegistrationNativePlatformServerCompletion.outgoing coins sign)
        (RegistrationNativePlatformSourceBuild.encode writer) pending).run before).run previous)) :
    result.2.world.1.server = before.world.1.server :=
  publication_cache coins sign writer pending before previous result next supported

theorem record_publication_frame (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : registration.ServerInitialKdf) (before : RegistrationServerRootCompiler.Local n) (previous : Platform)
    (result : RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)) × RegistrationServerRootCompiler.Local n) (next : Platform)
    (supported : (result, next) ∈ support
      (((do let recorded ← RegistrationNativePlatformSourceSealTrace.record coins setup codec view failure allocation erased helper initial
            RegistrationNativePlatformServerPublication.continueResult recorded
              (RegistrationNativePlatformServerPublication.program
                (RegistrationNativePlatformServerCompletion.outgoing coins sign)
                (RegistrationNativePlatformSourceBuild.encode writer))).run before).run previous)) :
    result.2.world.1.server = before.world.1.server := by
  apply bind_keeps frame
    (RegistrationNativePlatformSourceSealTrace.record coins setup codec view failure allocation erased helper initial)
    (fun recorded => RegistrationNativePlatformServerPublication.continueResult recorded
      (RegistrationNativePlatformServerPublication.program
        (RegistrationNativePlatformServerCompletion.outgoing coins sign)
        (RegistrationNativePlatformSourceBuild.encode writer)))
    (fun start platform result next reached => record_frame coins setup codec view failure allocation erased helper initial start platform result next reached)
    (fun recorded => pub_result_keeps frame recorded _ (publication_cache coins sign writer))
    before previous result next supported

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {mlSource : RegistrationNativeMldsa.Source}

omit primitive in
theorem material_local (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (views : AdapterPublicWrapperStorage.Views) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.server.Server) (before : RegistrationServerFrontendCompiler.State n)
    (related : AdapterPublicWrapperState.Server view views created credential self before)
    (after : RegistrationServerRootCompiler.Local n)
    (sameServer : after.world.1.server = before.world.world.1.server) :
    AdapterPublicWrapperState.Server view views created credential self {before with world := after} := by
  rcases related.peers with ⟨records, reached, sender, identity, peers⟩
  exact ⟨related.identity, related.control, related.pinIdentity, related.pinIdentifier, related.pinMldsa,
    related.replay, records, sameServer.trans reached, sender, identity, peers⟩

theorem record_publication_material (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : registration.ServerInitialKdf)
    (sourceView : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (views : AdapterPublicWrapperStorage.Views) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.server.Server) (before : RegistrationServerFrontendCompiler.State n)
    (related : AdapterPublicWrapperState.Server sourceView views created credential self before)
    (previous : Platform)
    (result : RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)) × RegistrationServerRootCompiler.Local n) (next : Platform)
    (supported : (result, next) ∈ support
      (((do let recorded ← RegistrationNativePlatformSourceSealTrace.record coins setup codec view failure allocation erased helper initial
            RegistrationNativePlatformServerPublication.continueResult recorded
              (RegistrationNativePlatformServerPublication.program
                (RegistrationNativePlatformServerCompletion.outgoing coins sign)
                (RegistrationNativePlatformSourceBuild.encode writer))).run before.world).run previous)) :
    AdapterPublicWrapperState.Server sourceView views created credential self {before with world := result.2} := by
  exact material_local sourceView views created credential self before related result.2
    (record_publication_frame coins setup codec view failure allocation erased helper sign writer initial before.world previous result next supported)

end BeaconcryptCore.Refinement.AdapterPublicServerCompletionFrame
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionFrame.record_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionFrame.record_frame

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionFrame.publication_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionFrame.publication_frame
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionFrame.record_publication_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionFrame.record_publication_frame

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionFrame.material_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionFrame.material_local
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionFrame.record_publication_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionFrame.record_publication_material
