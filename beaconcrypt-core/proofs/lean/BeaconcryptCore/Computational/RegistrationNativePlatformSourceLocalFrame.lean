-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerService
/-! Actual source completion leaves preserve agreement auxiliary state and request history. The proof follows every actual primitive, allocator, writer and signing leaf before composing the supplied-pending source tree. Full reached World and platform poststates are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceLocalFrame
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationWorldAgreement (State)
variable {n : Nat} {E Auxiliary Platform Value Next I KemSK Reader Response : Type} {base : OracleSpec I}
def fields (before : State n Auxiliary) := (before.auxiliary, before.requests)
def Keeps (work : StateT (State n Auxiliary) (StateT Platform ProbComp) Value) : Prop :=
  ∀ before previous result next, (result, next) ∈ support ((work.run before).run previous) → fields result.2 = fields before
private theorem pure_keeps (value : Value) : Keeps (pure value : StateT (State n Auxiliary) (StateT Platform ProbComp) Value) := by
  intro before previous result next supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
  rw [congrArg Prod.snd supported.1]
private theorem bind_keeps (work : StateT (State n Auxiliary) (StateT Platform ProbComp) Value)
    (next : Value → StateT (State n Auxiliary) (StateT Platform ProbComp) Next)
    (first : Keeps work) (rest : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
  intro before previous result platform supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨value, middle⟩, current⟩, reached, continued⟩ := supported
  exact (rest value middle current result platform continued).trans (first before previous (value, middle) current reached)
private theorem simulate_keeps {J : Type} {spec : OracleSpec J}
    (implementation : QueryImpl spec (StateT (State n Auxiliary) (StateT Platform ProbComp)))
    (allowed : ∀ query, Keeps (implementation query)) (work : OracleComp spec Value) : Keeps (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_keeps value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_keeps _ _ (allowed query) ih
private theorem shared_native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : MldsaSharedNative.Spec.Domain) (before : State n Auxiliary)
    (result : MldsaSharedNative.Spec.Range query × State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldRecords.shared setup codec query).run before)) : fields result.2 = fields before := by
  cases query with
  | inl query =>
      simp only [RegistrationWorldRecords.shared, StateT.run, support_map] at supported
      obtain ⟨inner, _called, same⟩ := supported
      cases same
      rfl
  | inr query =>
      simp only [RegistrationWorldRecords.shared, RegistrationWorldRecords.record, StateT.run, support_map] at supported
      obtain ⟨inner, _called, same⟩ := supported
      cases same
      rfl
private theorem shared_program (setup : Setup base KemSK) (codec : Codec Reader Response)
    (work : OracleComp MldsaSharedNative.Spec Value) (before : State n Auxiliary) (result : Value × State n Auxiliary)
    (supported : result ∈ support ((simulateQ (RegistrationWorldRecords.shared setup codec) work).run before)) : fields result.2 = fields before := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      exact (ih middle.1 middle.2 result continued).trans (shared_native setup codec query before middle reached)
/-- Every original instrumented first-record leaf retains both agreement coordinates. -/
theorem records (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (query : RegistrationRecordPrimitives.Spec.Domain) :
    Keeps (RegistrationNativePlatformServerCompletion.records (n := n) (Auxiliary := Auxiliary) coins setup codec query) := by
  intro before previous result next supported
  have actual := RegistrationNativePlatformHashReceipt.native_support coins _ result previous next supported
  simp only [RegistrationWorldRecords.handler, StateT.run, support_map] at actual
  obtain ⟨inner, called, same⟩ := actual
  cases same
  exact shared_program setup codec (RegistrationRecordPrimitives.callbacks setup.source query) before inner called
variable [primitive : AdapterSealPrimitive.Operations]
private theorem aead_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (plaintext : Slice U8) (associated : Option (Slice U8)) (nonce : primitive.Nonce) (key : primitive.Key) :
    Keeps (RegistrationNativePlatformSourceSeal.aead (n := n) (Auxiliary := Auxiliary) coins setup codec view failure plaintext associated nonce key) := by
  intro before previous result next supported
  change (result, next) ∈ support
    ((fun inner => ((.ok (RegistrationNativePlatformSourceSeal.detached failure inner.1.1), inner.1.2), inner.2)) <$>
      (simulateQ coins ((RegistrationWorldRecords.record setup codec
        (.inr (.inl (RegistrationNativePlatformSourceSeal.input view plaintext associated nonce key)))).run before)).run previous) at supported
  rw [support_map] at supported
  obtain ⟨⟨inner, platform⟩, called, same⟩ := supported
  have stateEq := congrArg (fun value => value.1.2) same
  rw [← stateEq]
  have actual := RegistrationNativePlatformHashReceipt.native_support coins _ inner previous platform called
  simp only [RegistrationWorldRecords.record, StateT.run, support_map] at actual
  obtain ⟨effect, _reached, same⟩ := actual
  cases same
  rfl
private theorem seal_query (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp)) (query : (AdapterSealNative.Spec E).Domain) :
    Keeps (RegistrationNativePlatformSourceSeal.handler (n := n) (Auxiliary := Auxiliary) coins setup codec view failure allocation query) := by
  cases query with
  | aead plaintext associated nonce key => exact aead_keeps coins setup codec view failure plaintext associated nonce key
  | reserve bytes capacity =>
      intro before previous result next supported
      simp only [RegistrationNativePlatformSourceSeal.handler, StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
      obtain ⟨⟨reply, platform⟩, _called, same⟩ := supported
      have stateEq := congrArg (fun value => value.1.2) same
      rw [← stateEq]
/-- The actual seal request includes every allocation and AEAD outcome while retaining both agreement coordinates. -/
theorem sealing (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp)) (request : record_effects.AeadSealRequest) :
    Keeps (RegistrationNativePlatformSourceSeal.sealing (n := n) (Auxiliary := Auxiliary) coins setup codec view failure allocation request) := by
  unfold RegistrationNativePlatformSourceSeal.sealing
  apply bind_keeps _ _ (simulate_keeps _ (seal_query coins setup codec view failure allocation) _)
  intro result
  apply bind_keeps
  · intro before previous returned next supported
    simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
    rw [congrArg Prod.snd supported.1]
    rfl
  · intro _
    exact pure_keeps _
omit primitive in
private theorem hash_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (erased transcript : commitment.CommitmentTranscript) :
    Keeps (RegistrationNativePlatformSourceSeal.hash (n := n) (Auxiliary := Auxiliary) coins setup codec erased transcript) := by
  unfold RegistrationNativePlatformSourceSeal.hash
  exact bind_keeps _ _ (records coins setup codec _) (fun _ => pure_keeps _)
omit primitive in
private theorem write_keeps (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (request : record_effects.RecordWriteRequest) : Keeps (RegistrationNativePlatformSourceBuild.write (n := n) helper request) := by
  intro before previous result next supported
  rw [RegistrationNativePlatformSourceBuild.write_joint, support_map] at supported
  obtain ⟨⟨reply, platform⟩, _called, same⟩ := supported
  have stateEq := congrArg (fun value => value.1.2) same
  rw [← stateEq]
  rfl
omit primitive in
private theorem outgoing_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) (query : RegistrationSigningShared.Spec.Domain) :
    Keeps (RegistrationNativePlatformServerCompletion.outgoing (n := n) (Auxiliary := Auxiliary) coins sign query) := by
  intro before previous result next supported
  have actual := RegistrationNativePlatformHashReceipt.native_support coins _ result previous next supported
  simp only [RegistrationNativePlatformServerCompletion.nativeOutgoing, StateT.run, support_map] at actual
  obtain ⟨inner, _called, same⟩ := actual
  cases same
  rfl
omit primitive in
private theorem encode_keeps (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (view : registration.SignedResponseView) : Keeps (RegistrationNativePlatformSourceBuild.encode (n := n) writer view) := by
  intro before previous result next supported
  rw [RegistrationNativePlatformSourceBuild.encode_run, StateT.run_map, support_map] at supported
  obtain ⟨⟨reply, platform⟩, _called, same⟩ := supported
  have stateEq := congrArg (fun value => value.1.2) same
  rw [← stateEq]
omit primitive in
private theorem effect_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Keeps (RegistrationNativePlatformPairedServerService.nativeEffects (Auxiliary := Auxiliary) coins query) := by
  intro before previous result next supported
  have actual := RegistrationNativePlatformHashReceipt.native_support coins _ result previous next supported
  simp only [RegistrationServerPublicationWorldCompiler.effect, StateT.run, support_map] at actual
  obtain ⟨inner, _called, same⟩ := actual
  cases same
  rfl
noncomputable def implementation (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp)) (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl (RegistrationNativePlatformCtxCompletionProgram.Spec n) (StateT (RegistrationServerRootCompiler.Local n) (StateT Platform ProbComp))
  | .records query => RegistrationNativePlatformServerCompletion.records coins setup codec query
  | .seal query => RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation query
  | .hash query => RegistrationNativePlatformSourceSeal.hash coins setup codec erased query
  | .write query => RegistrationNativePlatformSourceBuild.write helper query
  | .signing query => RegistrationNativePlatformServerCompletion.outgoing coins sign query
  | .encode view => RegistrationNativePlatformSourceBuild.encode writer view
  | .effect query => RegistrationNativePlatformPairedServerService.nativeEffects coins query
/-- The literal supplied-pending source completion retains agreement auxiliary state and history on every returned outcome. -/
theorem finish (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp)) (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    Keeps (RegistrationNativePlatformSourceBuild.finishSource (n := n) coins setup codec
      (RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation)
      (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) sign helper writer control pending) := by
  have free := simulate_keeps (implementation (n := n) coins setup codec view failure allocation erased sign helper writer)
    (fun query => by cases query with
      | records query => exact records coins setup codec query
      | «seal» query => exact sealing coins setup codec view failure allocation query
      | hash query => exact hash_keeps coins setup codec erased query
      | write query => exact write_keeps helper query
      | signing query => exact outgoing_keeps coins sign query
      | encode view => exact encode_keeps writer view
      | effect query => exact effect_keeps coins query)
    (RegistrationNativePlatformCtxCompletionProgram.program (n := n) control pending)
  rw [RegistrationNativePlatformCtxCompletionProgram.interpret] at free
  exact free
end BeaconcryptCore.Computational.RegistrationNativePlatformSourceLocalFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceLocalFrame.records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceLocalFrame.records

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceLocalFrame.sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceLocalFrame.sealing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceLocalFrame.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceLocalFrame.finish
