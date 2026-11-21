-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawMiddleRecords

/-! The raw compiler's public state consists only of registration replies, creation pins and the returned assignment counter. Record processing changes no part of that state, including on admission refusal or a failed native write. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawPublicState
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (Spec)
variable {ι KemSK Reader Response S : Type} {baseSpec : OracleSpec ι}

structure Public where
  log : PqxdhDeploymentCompile.Log
  lastId : Std.U64

def ofMemory (memory : CborAdmissionCompiler.Local) : Public := ⟨memory.copies.log, memory.lastId⟩

def toMemory (publicState : Public) : CborAdmissionCompiler.Local :=
  ⟨{ PqxdhDeploymentCompile.Local.empty with log := publicState.log }, publicState.lastId⟩

theorem of_to (publicState : Public) : ofMemory (toMemory publicState) = publicState := by
  cases publicState
  rfl

theorem server_local_log (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (copies : PqxdhDeploymentCompile.Local)
    (result : RawCtxServerMixed.SourceSpec.Range query × PqxdhDeploymentCompile.Local)
    (supported : result ∈ support ((PqxdhDeploymentCompile.serverLocal setup codec route query).run copies)) :
    result.2.log = copies.log := by
  cases target : PqxdhDeploymentCompile.serverTarget route query with
  | none =>
      simp only [PqxdhDeploymentCompile.serverLocal, StateT.run, target, bind_pure_comp, support_map] at supported
      obtain ⟨inner, _, rfl⟩ := supported
      rfl
  | some keyId =>
      simp only [PqxdhDeploymentCompile.serverLocal, StateT.run, target, mem_support_bind_iff,
        bind_pure_comp, support_map] at supported
      obtain ⟨kernel, _, associatedData, _, inner, _, rfl⟩ := supported
      rfl

theorem beacon_local_log (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain) (copies : PqxdhDeploymentCompile.Local)
    (result : RawCtxMixedOwner.SourceSpec.Range query × PqxdhDeploymentCompile.Local)
    (supported : result ∈ support ((PqxdhDeploymentCompile.beaconLocal setup codec index query).run copies)) :
    result.2.log = copies.log := by
  by_cases inside : index < copies.log.owners.length
  · simp only [PqxdhDeploymentCompile.beaconLocal, StateT.run, inside, ite_true,
      mem_support_bind_iff, bind_pure_comp, support_map] at supported
    obtain ⟨kernel, _, associatedData, _, inner, _, rfl⟩ := supported
    rfl
  · simp only [PqxdhDeploymentCompile.beaconLocal, StateT.run, inside, ite_false,
      support_pure, Set.mem_singleton_iff] at supported
    subst supported
    rfl

theorem server_send_public (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (keyId : Std.U64) (plaintext : Pqxdh.Bytes)
    (memory : CborAdmissionCompiler.Local)
    (result : Option RawCtxSourceSend.Encrypted × CborAdmissionCompiler.Local)
    (supported : result ∈ support ((CborAdmissionCompiler.serverSend setup codec route keyId plaintext).run memory)) :
    ofMemory result.2 = ofMemory memory := by
  simp only [CborAdmissionCompiler.serverSend, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨kernel, _, supported⟩ := supported
  cases kernel with
  | none =>
      simp only [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
  | some current =>
      dsimp only at supported
      split_ifs at supported
      · rw [support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        have kept := server_local_log setup codec route (.inl (plaintext, keyId)) _ inner member
        exact congrArg (fun log => Public.mk log memory.lastId) kept
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        rfl

theorem beacon_send_public (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (plaintext : Pqxdh.Bytes) (memory : CborAdmissionCompiler.Local)
    (result : Option RawCtxSourceSend.Encrypted × CborAdmissionCompiler.Local)
    (supported : result ∈ support ((CborAdmissionCompiler.beaconSend setup codec index plaintext).run memory)) :
    ofMemory result.2 = ofMemory memory := by
  unfold CborAdmissionCompiler.beaconSend at supported
  simp only [StateT.run] at supported
  split_ifs at supported
  · simp only [mem_support_bind_iff] at supported
    obtain ⟨kernel, _, supported⟩ := supported
    cases kernel <;> cases view : PqxdhDeploymentCompile.ownerView codec memory.copies.log index
    all_goals simp only [view] at supported
    all_goals first
      | (simp only [support_pure, Set.mem_singleton_iff] at supported; subst supported; rfl)
      | skip
    split_ifs at supported
    · rw [support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      have kept := beacon_local_log setup codec index (.inl plaintext) _ inner member
      exact congrArg (fun log => Public.mk log memory.lastId) kept
    · simp only [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    rfl

theorem admission_record_public (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : Spec.Domain)
    (record : CborSplitCompiler.recordCommand query = true) (memory : CborAdmissionCompiler.Local)
    (result : Spec.Range query × CborAdmissionCompiler.Local)
    (supported : result ∈ support ((CborAdmissionCompiler.compileImpl setup codec route query).run memory)) :
    ofMemory result.2 = ofMemory memory := by
  rcases query with coin | command
  · simp [CborSplitCompiler.recordCommand] at record
  · cases command
    all_goals try simp [CborSplitCompiler.recordCommand] at record
    case serverSend keyId plaintext => exact server_send_public setup codec route keyId plaintext memory result supported
    case beaconSend index plaintext => exact beacon_send_public setup codec index plaintext memory result supported
    case serverRaw raw =>
      simp only [CborAdmissionCompiler.compileImpl, CborAdmissionCompiler.liftExisting,
        PqxdhDeploymentCompile.compileImpl, StateT.run, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact congrArg (fun log => Public.mk log memory.lastId)
        (server_local_log setup codec route (.inr raw) memory.copies inner member)
    case beaconRaw index raw =>
      simp only [CborAdmissionCompiler.compileImpl, CborAdmissionCompiler.liftExisting,
        PqxdhDeploymentCompile.compileImpl, StateT.run, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact congrArg (fun log => Public.mk log memory.lastId)
        (beacon_local_log setup codec index (.inr raw) memory.copies inner member)

theorem raw_record_public (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (query : Spec.Domain)
    (record : CborSplitCompiler.recordCommand query = true) (memory : CborAdmissionCompiler.Local)
    (result : Spec.Range query × CborAdmissionCompiler.Local)
    (supported : result ∈ support ((CborRawCompile.compileImpl setup wire parse query).run memory)) :
    ofMemory result.2 = ofMemory memory := by
  rw [CborRawMiddleRecords.record_impl setup wire parse query record, CborSplitCompiler.compileImpl] at supported
  exact admission_record_public setup _ (CborRawCompile.route parse) query record memory result supported

/-- Any later interpretation preserves the public record frame, regardless of its private state and all adaptive oracle replies. -/
theorem interpreted_record_public
    (impl : QueryImpl (PqxdhDeploymentRecordCache.SourceSpec KemSK) (StateT S ProbComp))
    (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (query : Spec.Domain)
    (record : CborSplitCompiler.recordCommand query = true) (memory : CborAdmissionCompiler.Local) (state : S)
    (result : (Spec.Range query × CborAdmissionCompiler.Local) × S)
    (supported : result ∈ support ((simulateQ impl ((CborRawCompile.compileImpl setup wire parse query).run memory)).run
      state)) : ofMemory result.1.2 = ofMemory memory := by
  apply raw_record_public setup wire parse query record memory result.1
  apply OracleComp.support_simulateQ_run'_subset impl _ state
  rw [StateT.run'_eq, support_map]
  exact ⟨result, supported, rfl⟩

end BeaconcryptCore.Computational.CborRawPublicState

/-- info: 'BeaconcryptCore.Computational.CborRawPublicState.interpreted_record_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPublicState.interpreted_record_public

-- Exact dependency observations for all public helper theorems.

/-- info: 'BeaconcryptCore.Computational.CborRawPublicState.of_to' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPublicState.of_to

/-- info: 'BeaconcryptCore.Computational.CborRawPublicState.server_local_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPublicState.server_local_log

/-- info: 'BeaconcryptCore.Computational.CborRawPublicState.beacon_local_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPublicState.beacon_local_log

/-- info: 'BeaconcryptCore.Computational.CborRawPublicState.server_send_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPublicState.server_send_public

/-- info: 'BeaconcryptCore.Computational.CborRawPublicState.beacon_send_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPublicState.beacon_send_public

/-- info: 'BeaconcryptCore.Computational.CborRawPublicState.admission_record_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPublicState.admission_record_public

/-- info: 'BeaconcryptCore.Computational.CborRawPublicState.raw_record_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPublicState.raw_record_public
