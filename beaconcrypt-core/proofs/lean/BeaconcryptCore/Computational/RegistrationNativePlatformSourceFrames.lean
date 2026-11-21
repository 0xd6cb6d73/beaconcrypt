-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildCut

/-! Actual source first-record calls preserve the earlier signing log and extend the shared cache on every outcome. The proof follows the full source seal/request, mutable hash and raw-writer bodies, including every failed allocator or primitive prefix. These frames permit a later failed build to retain the earlier reached source-stage witness. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceFrames
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
  holds before after := before.world.1.primitive.2 ≤ after.world.1.primitive.2 ∧ after.world.2 = before.world.2
  reflexive _ := ⟨le_refl _, rfl⟩
  transitive _ _ _ first second := ⟨first.1.trans second.1, second.2.trans first.2⟩

private theorem records_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (query : RegistrationRecordPrimitives.Spec.Domain) :
    Keeps frame (RegistrationNativePlatformServerCompletion.records (n := n) (Auxiliary := Auxiliary) coins setup codec query) := by
  intro before previous result next supported
  have actual := RegistrationNativePlatformHashReceipt.native_support coins _ result previous next supported
  exact RegistrationNativeWorldStageCache.records setup codec (RegistrationRecordPrimitives.Spec.query query) before result
    (by simpa only [simulateQ_spec_query] using actual)

private theorem primitive_frame (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (before : State n Auxiliary)
    (result : RawCtxMixedOwner.NativeSpec.Range query × State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldRecords.record setup codec query).run before)) :
    frame.holds before result.2 := by
  simp only [RegistrationWorldRecords.record, StateT.run, support_map] at supported
  obtain ⟨inner, reached, equal⟩ := supported
  cases equal
  exact ⟨RegistrationWorldCache.primitive_cache setup codec query before.world.1.primitive inner reached, rfl⟩

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
    exact ⟨le_refl _, rfl⟩
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
  exact ⟨le_refl _, rfl⟩

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

/-- Every actual source first-record outcome extends the shared cache and preserves the complete earlier ML receipt prefix. -/
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
    before.world.1.primitive.2 ≤ result.2.world.1.primitive.2 ∧ result.2.world.2 = before.world.2 := by
  exact fromInitial_keeps frame
    (RegistrationNativePlatformServerCompletion.records coins setup codec)
    (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
    (RegistrationNativePlatformSourceSeal.hash coins setup codec erased)
    (RegistrationNativePlatformSourceBuild.write helper)
    (records_keeps coins setup codec) (sealing_keeps coins setup codec view failure allocation)
    (hash_keeps coins setup codec erased) (write_keeps helper) initial before previous result next supported

omit primitive in
private def cache : Relation (State n Auxiliary) where
  holds before after := before.world.1.primitive.2 ≤ after.world.1.primitive.2
  reflexive _ := le_refl _
  transitive _ _ _ first second := first.trans second

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
private theorem completion_with_keeps {S A Encoded : Type} (relation : Relation S) (head : RustM A)
    (next : A → StateT S (StateT Platform ProbComp) (RustM (RegistrationWorldServerCompletion.Result Encoded)))
    (rest : ∀ value, Keeps relation (next value)) :
    Keeps relation (RegistrationNativePlatformServerCompletion.continueWith head next) := by
  cases head with
  | ok value => exact rest value
  | fail error | div => exact pure_keeps relation _

omit primitive in
private theorem completion_result_keeps {S A Encoded : Type} (relation : Relation S)
    (head : RustM (core.result.Result A pqxdh.ServerState))
    (next : A → StateT S (StateT Platform ProbComp) (RustM (RegistrationWorldServerCompletion.Result Encoded)))
    (rest : ∀ value, Keeps relation (next value)) :
    Keeps relation (RegistrationNativePlatformServerCompletion.continueResult head next) := by
  cases head with
  | fail error | div => exact pure_keeps relation _
  | ok result => cases result with
    | Err prior => exact pure_keeps relation _
    | Ok value => exact rest value

omit primitive in
private theorem outgoing_cache (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Spec.Domain) :
    Keeps cache (RegistrationNativePlatformServerCompletion.outgoing (n := n) (Auxiliary := Auxiliary) coins sign query) := by
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
      change before.world.1.primitive.2 ≤ inner.2.1.primitive.2
      rw [← worldEq]
      exact RegistrationWorldCache.effects_cache _ before.world.1 effect reached
  | sign request payload digest =>
      simp only [RegistrationWorldSigning.outgoing, StateT.run, support_map] at called
      obtain ⟨effect, reached, equal⟩ := called
      have worldEq := congrArg (fun value => value.2.1) equal
      change before.world.1.primitive.2 ≤ inner.2.1.primitive.2
      rw [← worldEq]
      exact (RegistrationWorldCache.sampled_cache (sign request) before.world.1 effect reached).ge

omit primitive in
private theorem encode_cache
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (view : registration.SignedResponseView) :
    Keeps cache (RegistrationNativePlatformSourceBuild.encode (n := n) writer view) := by
  intro before previous result next supported
  rw [RegistrationNativePlatformSourceBuild.encode_run, StateT.run_map, support_map] at supported
  obtain ⟨⟨answer, platform⟩, _encoded, equal⟩ := supported
  have stateEq := congrArg (fun value => value.1.2) equal
  rw [← stateEq]
  exact le_refl _

omit primitive in
private theorem capability_cache (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (query : PqxdhRecordLiftInterface.Capability n) :
    Keeps cache (RegistrationNativePlatformServerCompletion.capability (Auxiliary := Auxiliary) coins query) := by
  intro before previous result next supported
  have actual := RegistrationNativePlatformHashReceipt.native_support coins _ result previous next supported
  simp only [RegistrationWorldServerCompletion.capability, StateT.run, support_map] at actual
  obtain ⟨inner, called, equal⟩ := actual
  have stateEq := congrArg Prod.snd equal
  rw [← stateEq]
  exact RegistrationWorldCache.effects_cache (.inr query) before.world.1 inner called

omit primitive in
private theorem publication_ready_cache
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (pending : registration.ServerResponseReady) :
    Keeps cache (RegistrationNativePlatformServerPublication.ready
      (RegistrationNativePlatformSourceBuild.encode (n := n) writer) pending) := by
  unfold RegistrationNativePlatformServerPublication.ready
  apply pub_with_keeps cache
  intro view
  exact bind_keeps cache _ _ (encode_cache writer view) (fun _ => pure_keeps cache _)

omit primitive in
private theorem publication_signing_cache (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest) (pending : registration.ServerResponseSigning) :
    Keeps cache (RegistrationNativePlatformServerPublication.signing
      (RegistrationNativePlatformServerCompletion.outgoing (n := n) coins sign)
      (RegistrationNativePlatformSourceBuild.encode writer) payload digest pending) := by
  unfold RegistrationNativePlatformServerPublication.signing
  apply pub_with_keeps cache
  intro request
  apply bind_keeps cache _ _ (outgoing_cache coins sign _)
  intro reply
  exact pub_result_keeps cache _ _ (publication_ready_cache writer)

omit primitive in
private theorem publication_cache (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (pending : registration.ServerResponseHash) :
    Keeps cache (RegistrationNativePlatformServerPublication.program
      (RegistrationNativePlatformServerCompletion.outgoing (n := n) coins sign)
      (RegistrationNativePlatformSourceBuild.encode writer) pending) := by
  unfold RegistrationNativePlatformServerPublication.program
  apply pub_with_keeps cache
  intro request
  apply bind_keeps cache _ _ (outgoing_cache coins sign _)
  intro digest
  exact pub_result_keeps cache _ _ (publication_signing_cache coins sign writer _ digest)

omit primitive in
private theorem install_cache (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (published : registration.PublishedServerResponse (alloc.vec.Vec U8)) :
    Keeps cache (RegistrationNativePlatformServerCompletion.installWith
      (RegistrationNativePlatformServerCompletion.capability (n := n) (Auxiliary := Auxiliary) coins) control published) := by
  unfold RegistrationNativePlatformServerCompletion.installWith
  apply completion_result_keeps cache
  intro pending
  apply completion_with_keeps cache
  intro keyId
  apply completion_with_keeps cache
  intro parts
  exact bind_keeps cache _ _ (capability_cache coins _) (fun _ => pure_keeps cache _)

omit primitive in
private theorem afterRecord_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (hashed : registration.ServerResponseHash) :
    Keeps cache (RegistrationNativePlatformSourceBuildCut.afterRecord (n := n) coins sign writer control hashed) := by
  unfold RegistrationNativePlatformSourceBuildCut.afterRecord
  apply bind_keeps cache _ _ (publication_cache coins sign writer hashed)
  intro published
  exact completion_result_keeps cache _ _ (install_cache coins control)

omit primitive in
/-- Source outgoing hashing, signing, response serialization and installation retain the reached first-record cache on every outcome. -/
theorem afterRecord_cache (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (hashed : registration.ServerResponseHash)
    (before : RegistrationServerRootCompiler.Local n) (previous : Platform)
    (result : RustM (RegistrationWorldServerCompletion.Result (alloc.vec.Vec U8)) × RegistrationServerRootCompiler.Local n)
    (next : Platform)
    (supported : (result, next) ∈ support
      (((RegistrationNativePlatformSourceBuildCut.afterRecord coins sign writer control hashed).run before).run previous)) :
    before.world.1.primitive.2 ≤ result.2.world.1.primitive.2 :=
  afterRecord_keeps coins sign writer control hashed before previous result next supported

omit primitive in
private theorem pure_state {S X : Type} (value : X) (before : S) (previous : Platform)
    (result : X × S) (next : Platform)
    (supported : (result, next) ∈ support (((pure value : StateT S (StateT Platform ProbComp) X).run before).run previous)) :
    result.2 = before := by
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
  exact congrArg Prod.snd supported.1

/-- The complete source completion retains its earlier cache on every successful or failed prefix. -/
theorem finish_cache (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf)
    (before : RegistrationServerRootCompiler.Local n) (previous : Platform)
    (result : RustM (RegistrationWorldServerCompletion.Result (alloc.vec.Vec U8)) × RegistrationServerRootCompiler.Local n)
    (next : Platform)
    (supported : (result, next) ∈ support
      (((RegistrationNativePlatformSourceBuild.finishSource coins setup codec
        (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) sign helper writer control initial).run before).run previous)) : before.world.1.primitive.2 ≤ result.2.world.1.primitive.2 := by
  obtain ⟨recorded, current, platform, called, continued⟩ := RegistrationNativePlatformSourceBuildCut.cut
    coins setup codec view failure allocation erased sign helper writer control initial before result.2 previous next result.1 supported
  have facts := record_frame coins setup codec view failure allocation erased helper initial before previous (recorded, current) platform called
  cases recorded with
  | fail error | div =>
      have stateEq := pure_state _ current platform result next continued
      rw [stateEq]
      exact facts.1
  | ok answer => cases answer with
    | Err prior =>
        have stateEq := pure_state _ current platform result next continued
        rw [stateEq]
        exact facts.1
    | Ok hashed => exact facts.1.trans (afterRecord_cache coins sign writer control hashed current platform result next continued)

/-- A new actual signing receipt forces an earlier successful first-record cut, even if signing, response encoding or installation later failed. -/
theorem new_receipts (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf)
    (before : RegistrationServerRootCompiler.Local n) (previous : Platform)
    (result : RustM (RegistrationWorldServerCompletion.Result (alloc.vec.Vec U8)) × RegistrationServerRootCompiler.Local n)
    (next : Platform)
    (supported : (result, next) ∈ support
      (((RegistrationNativePlatformSourceBuild.finishSource coins setup codec
        (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) sign helper writer control initial).run before).run previous))
    (changed : result.2.world.2 ≠ before.world.2) :
    ∃ hashed current platform,
      ((.ok (.Ok hashed), current), platform) ∈ support
        (((RegistrationNativePlatformSourceSealTrace.record coins setup codec view failure allocation erased helper initial).run before).run previous) ∧
      RegistrationServerRecordExecutor.Path initial hashed ∧
      current.world.1.primitive.2 ≤ result.2.world.1.primitive.2 ∧
      (result, next) ∈ support
        (((RegistrationNativePlatformSourceBuildCut.afterRecord coins sign writer control hashed).run current).run platform) := by
  obtain ⟨recorded, current, platform, called, continued⟩ := RegistrationNativePlatformSourceBuildCut.cut
    coins setup codec view failure allocation erased sign helper writer control initial before result.2 previous next result.1 supported
  have facts := record_frame coins setup codec view failure allocation erased helper initial before previous (recorded, current) platform called
  cases recorded with
  | fail error | div =>
      have stateEq := pure_state _ current platform result next continued
      exact False.elim (changed ((congrArg (fun state => state.world.2) stateEq).trans facts.2))
  | ok answer => cases answer with
    | Err prior =>
        have stateEq := pure_state _ current platform result next continued
        exact False.elim (changed ((congrArg (fun state => state.world.2) stateEq).trans facts.2))
    | Ok hashed =>
        have jointSupported : (.ok (.Ok hashed), (current, platform)) ∈ support
            ((RegistrationNativePlatformSourceSealTrace.joint
              (RegistrationNativePlatformSourceSealTrace.record coins setup codec view failure allocation erased helper initial)).run (before, previous)) := by
          change (.ok (.Ok hashed), (current, platform)) ∈ support
            ((fun result => (result.1.1, (result.1.2, result.2))) <$>
              ((RegistrationNativePlatformSourceSealTrace.record coins setup codec view failure allocation erased helper initial).run before).run previous)
          rw [support_map]
          exact ⟨((.ok (.Ok hashed), current), platform), called, rfl⟩
        obtain ⟨trace⟩ := RegistrationNativePlatformSourceSealTrace.run coins setup codec view failure allocation erased helper initial hashed
          (before, previous) (current, platform) jointSupported
        exact ⟨hashed, current, platform, called, trace.path,
          afterRecord_cache coins sign writer control hashed current platform result next continued, continued⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformSourceFrames

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceFrames.record_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceFrames.record_frame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceFrames.afterRecord_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceFrames.afterRecord_cache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceFrames.finish_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceFrames.finish_cache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceFrames.new_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceFrames.new_receipts
