import BeaconcryptCore.Computational.PqxdhInitialNativePath
import BeaconcryptCore.Computational.PqxdhInitialOriginPost
import BeaconcryptCore.Computational.PqxdhInitialSuppliedPositions

/-!
The original Server builder publishes only the kernel returned by its actual first send. Its source execution retains a path from the supplied zero-counter initial chain in the shared private cache, including through erase and serialization callbacks. Successful builder publications therefore already have a cached directional path before any later checker runs. The statements preserve the complete logged source state and all optional and Rust failure branches.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialOriginBuilderPath
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhInitialPendingPost PqxdhInitialNativeLog
open RawCtxSourceSendPath RawCtxCursorLineage
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The original builder send preserves its initial directional path in the actual logged cache, even when sealing fails. -/
theorem send_path (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialPendingPost.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (entry : KernelOf RatchetChain) (context : RawCtxSourceSend.SealContext)
    (state : PqxdhInitialNativeLog.State A N C)
    (result : (KernelOf RatchetChain × Option RawCtxSourceSend.Encrypted) × PqxdhInitialNativeLog.State A N C)
    (supported : result ∈ support ((simulateQ (handler source writer stage external)
      ((PqxdhInitialPendingPost.calls (S := S) (B := B)).send entry context)).run state))
    (root : RootOutput) (valid : Path root ⟨entry⟩ state.1.1.2.1) :
    Path root ⟨result.1.1⟩ result.2.1.1.2.1 := by
  have projected : (result.1, result.2.1.1) ∈ support
      ((simulateQ (RawCtxPendingNativeCalls.pending
        (RawCtxSourceSendPath.native source writer stage)
        (RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.publicLift))
        (RawCtxPendingOwnerQueries.calls.send entry context)).run state.1.1) := by
    rw [← PqxdhInitialNativePath.primitive_projection (S := S) (B := B) source writer stage external _ state,
      support_map]
    exact ⟨result, supported, rfl⟩
  change (result.1, result.2.1.1) ∈ support
    (((RawCtxGenericOwnerInterpretation.interpretedCalls
      (RawCtxPendingNativeCalls.pending (RawCtxSourceSendPath.native source writer stage)
        (RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.publicLift))
      RawCtxPendingOwnerQueries.calls).send entry context).run state.1.1) at projected
  rw [RawCtxPendingNativeCalls.calls_interpretation] at projected
  exact (RawCtxSourcePathCalls.send_call source writer stage entry context state.1.1 _ projected).2 root valid

abbrev BuildState (M P : Type) :=
  PqxdhInitialGenericPublication.State (KernelOf RatchetChain) M P (List Pqxdh.Bytes)

/-- Successful serialization publishes the same advanced sender whose derivation is already retained in the source cache. -/
theorem after_path (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialPendingPost.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (entry : KernelOf RatchetChain) (metadata : P) (before : BuildState M P)
    (state : PqxdhInitialNativeLog.State A N C)
    (result : (Option PqxdhServerRegistrationPublication.Response × BuildState M P) × PqxdhInitialNativeLog.State A N C)
    (supported : result ∈ support ((simulateQ (handler source writer stage external)
      (PqxdhInitialGenericPublication.afterInitialization (PqxdhInitialPendingPost.calls (S := S) (B := B))
        auxForward candidate authenticated entry metadata before)).run state))
    (root : RootOutput) (valid : Path root ⟨entry⟩ state.1.1.2.1)
    (response : PqxdhServerRegistrationPublication.Response) (returned : result.1.1 = some response) :
    ∃ peer, result.1.2.server.peers response.keyId = some peer ∧
      Path root ⟨peer.kernel⟩ result.2.1.1.2.1 := by
  simp only [PqxdhInitialGenericPublication.afterInitialization, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨sent, sentSupport, erased, erasedSupport, rest⟩ := supported
  have sentPath := send_path source writer stage external entry _ state sent sentSupport root valid
  have erasedPath := RawCtxSourceSendPath.path_extends root ⟨sent.1.1⟩ _ _ sentPath
    (PqxdhInitialNativePath.program_extends source writer stage external _ sent.2 erased erasedSupport)
  cases encrypted : sent.1.2 <;> simp only [encrypted, simulateQ_pure, StateT.run_pure,
    mem_support_pure_iff, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at rest
  · cases rest
    cases returned
  · obtain ⟨written, writtenSupport, rest⟩ := rest
    have writtenPath := RawCtxSourceSendPath.path_extends root ⟨sent.1.1⟩ _ _ erasedPath
      (PqxdhInitialNativePath.program_extends source writer stage external _ erased.2 written writtenSupport)
    cases serialized : written.1 <;> simp only [serialized, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff] at rest
    all_goals (cases rest; simp only [Option.some.injEq] at returned)
    all_goals cases returned
    exact ⟨⟨candidate.beacon_identity_public_key, sent.1.1, metadata⟩,
      Function.update_self _ _ _, writtenPath⟩

/-- Every admitted builder candidate publishes an already cached path; rejected allocation, identity, application and Rust branches remain unsuccessful. -/
theorem candidate_path (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialPendingPost.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (initial : RustM (KernelOf RatchetChain)) (candidate : pqxdh.ServerRegistrationCandidate)
    (data : Option Pqxdh.Bytes) (metadata : P) (before : BuildState M P)
    (state afterState : PqxdhInitialNativeLog.State A N C)
    (response : PqxdhServerRegistrationPublication.Response) (updated : BuildState M P)
    (supported : (ok (some response, updated), afterState) ∈ support
      ((simulateQ (handler source writer stage external)
        (PqxdhInitialGenericBuilder.candidate (PqxdhInitialPendingPost.calls (S := S) (B := B))
          auxForward initial candidate data metadata before)).run state))
    (root : RootOutput)
    (initialPath : ∀ entry, initial = ok entry → ∀ table, Path root ⟨entry⟩ table) :
    ∃ peer, updated.server.peers response.keyId = some peer ∧ Path root ⟨peer.kernel⟩ afterState.1.1.2.1 := by
  simp only [PqxdhInitialGenericBuilder.candidate, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨⟨valid, afterCheck⟩, _, supported⟩ := supported
  cases valid <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
    simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, RustM.ok.injEq,
    reduceCtorEq, false_and, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨reserved, afterReserve⟩, _, supported⟩ := supported
  cases reserved <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
    simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, RustM.ok.injEq,
    reduceCtorEq, false_and] at supported
  cases initialEq : initial <;> simp only [initialEq, PqxdhInitialGenericBuilder.continueRust,
    simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported
  split at supported <;> try simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
    Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at supported
  split at supported <;> simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
    Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨⟨allocated, afterAllocation⟩, _, supported⟩ := supported
  cases allocated <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
    simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, RustM.ok.injEq,
    reduceCtorEq, false_and] at supported
  cases binding : candidate.key_id_binding <;> simp only [binding, simulateQ_pure, StateT.run_pure,
    mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and, simulateQ_map, StateT.run_map,
    support_map] at supported
  obtain ⟨⟨⟨reply, output⟩, finalState⟩, actual, same⟩ := supported
  simp only [Prod.mk.injEq, RustM.ok.injEq] at same
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
  exact after_path source writer stage external candidate _ _ metadata before afterAllocation
    _ actual root (initialPath _ initialEq _) response rfl

/-- Current key allocation and Ready preparation preserve the source-backed successful publication path. -/
theorem ready_path (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialPendingPost.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (initial : RustM (KernelOf RatchetChain)) (binding : pqxdh.ServerBinding)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (metadata : P) (before : BuildState M P)
    (state afterState : PqxdhInitialNativeLog.State A N C)
    (response : PqxdhServerRegistrationPublication.Response) (updated : BuildState M P)
    (supported : (ok (some response, updated), afterState) ∈ support
      ((simulateQ (handler source writer stage external)
        (PqxdhInitialGenericBuilder.readyBuild source (PqxdhInitialPendingPost.calls (S := S) (B := B))
          auxForward initial binding ready metadata before)).run state))
    (root : RootOutput)
    (initialPath : ∀ entry, initial = ok entry → ∀ table, Path root ⟨entry⟩ table) :
    ∃ peer, updated.server.peers response.keyId = some peer ∧ Path root ⟨peer.kernel⟩ afterState.1.1.2.1 := by
  unfold PqxdhInitialGenericBuilder.readyBuild PqxdhInitialGenericBuilder.usedBuild at supported
  cases next : pqxdh.server_next_key_id before.control <;> simp only [next,
    PqxdhInitialGenericBuilder.continueRust, simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
    Prod.mk.injEq, reduceCtorEq, false_and] at supported
  rename_i nextResult
  cases nextResult <;> simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
    Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at supported
  split at supported <;> try simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
    Prod.mk.injEq, reduceCtorEq, false_and] at supported
  split at supported <;> try simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
    Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at supported
  exact candidate_path source writer stage external initial _ ready.application metadata before
    state afterState response updated supported root initialPath

/-- The complete source builder installs a peer with its actual first-send path in the full logged final cache. -/
theorem build_path (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialPendingPost.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (initial : RustM (KernelOf RatchetChain)) (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (before after : Front RatchetChain M P I D K S B)
    (state afterState : PqxdhInitialNativeLog.State A N C)
    (response : PqxdhServerRegistrationPublication.Response)
    (supported : ((ok (some response), after), afterState) ∈ support
      ((simulateQ (handler source writer stage external)
        ((PqxdhInitialPendingBuilder.build source initial sender index metadata ready).run before)).run state))
    (root : RootOutput)
    (initialPath : ∀ entry, initial = ok entry → ∀ table, Path root ⟨entry⟩ table) :
    ∃ peer, (after.roles.1.1 index).server.peers response.keyId = some peer ∧
      Path root ⟨peer.kernel⟩ afterState.1.1.2.1 := by
  change ((ok (some response), after), afterState) ∈ support
    ((simulateQ (handler source writer stage external)
      (PqxdhInitialPendingBuilder.reinstall index (PqxdhInitialPendingBuilder.consume index ready before) <$>
        PqxdhInitialGenericBuilder.readyBuild source PqxdhInitialPendingPost.calls auxForward initial
          ⟨(PqxdhInitialPendingBuilder.selected sender index (PqxdhInitialPendingBuilder.consume index ready before)).server.identity,
            (PqxdhInitialPendingBuilder.selected sender index (PqxdhInitialPendingBuilder.consume index ready before)).identityKeyId⟩
          ready metadata (PqxdhInitialPendingBuilder.selected sender index (PqxdhInitialPendingBuilder.consume index ready before)))).run state) at supported
  simp only [simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨⟨reply, finalState⟩, actual, same⟩ := supported
  cases reply <;> simp only [PqxdhInitialPendingBuilder.reinstall, Prod.mk.injEq,
    reduceCtorEq, false_and, RustM.ok.injEq] at same
  rename_i built
  rcases built with ⟨reply, updated⟩
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
  simpa only [PqxdhInitialPendingBuilder.install, Function.update_self] using
    ready_path source writer stage external initial _ ready metadata _ state finalState
      response updated actual root initialPath

/-- The actual supplied Server initializer starts its send path at counter zero under every existing private table. -/
theorem supplied_path (source : FixedHkdfSha512NoSaltSource)
    (supplied : pqxdh.concrete.InitialRatchetKdfResponse) (entry : ConcreteRatchetKernel)
    (initialized : PqxdhInitialReplyErasure.kernelOf false supplied = ok entry)
    (table : RawCtxKdfRequestTable.Table) :
    Path (RawCtxSelectedQueryTrace.rootVector entry.refined.send_chain) entry table := by
  obtain ⟨_, _, _, server, _, created, _, _, _, refined⟩ :=
    PqxdhInitialSuppliedPositions.pair_refines source.crypto supplied
  have same : server = entry := RustM.ok.inj (created.symm.trans initialized)
  subst entry
  refine ⟨[], ?_⟩
  rw [refined.sendSequence]
  rfl

/-- An actual supplied64 Server build derives its initialized path and publishes only an already derived sender state; no caller path premise remains. -/
theorem supplied_build (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialPendingPost.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (supplied : pqxdh.concrete.InitialRatchetKdfResponse) (entry : ConcreteRatchetKernel)
    (initialized : PqxdhInitialReplyErasure.kernelOf false supplied = ok entry)
    (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (before after : Front RatchetChain M P I D K S B)
    (state afterState : PqxdhInitialNativeLog.State A N C)
    (response : PqxdhServerRegistrationPublication.Response)
    (supported : ((ok (some response), after), afterState) ∈ support
      ((simulateQ (handler source writer stage external)
        ((PqxdhInitialPendingBuilder.build source
          ((fun kernel : ConcreteRatchetKernel => kernel.refined) <$> PqxdhInitialReplyErasure.kernelOf false supplied)
          sender index metadata ready).run before)).run state)) :
    ∃ peer, (after.roles.1.1 index).server.peers response.keyId = some peer ∧
      Path (RawCtxSelectedQueryTrace.rootVector entry.refined.send_chain) ⟨peer.kernel⟩ afterState.1.1.2.1 := by
  apply build_path source writer stage external _ sender index metadata ready before after state afterState response supported
  intro kernel returned table
  rw [initialized, RawCtxMaterialInterpretation.rust_map_ok] at returned
  cases RustM.ok.inj returned
  exact supplied_path source supplied entry initialized table

/-- Each newly recorded original builder publication has an already cached path from the actual supplied Server send half. -/
theorem recorded_cached {Origin : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialPendingPost.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (supplied : pqxdh.concrete.InitialRatchetKdfResponse) (entry : ConcreteRatchetKernel)
    (initialized : PqxdhInitialReplyErasure.kernelOf false supplied = ok entry)
    (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (before after : Front RatchetChain M P I D K S B)
    (state afterState : PqxdhInitialNativeLog.State A N C)
    (reply : RustM (Option PqxdhServerRegistrationPublication.Response))
    (supported : ((reply, after), afterState) ∈ support
      ((simulateQ (handler source writer stage external)
        ((PqxdhInitialPendingBuilder.build source
          ((fun kernel : ConcreteRatchetKernel => kernel.refined) <$> PqxdhInitialReplyErasure.kernelOf false supplied)
          sender index metadata ready).run before)).run state))
    (trace : PqxdhInitialOriginPost.Trace Origin S B) (origin recordedOrigin : Origin)
    (publication : RawCtxPublishedRecords.Publication S B)
    (recorded : (publication, recordedOrigin) ∈
      (PqxdhInitialOriginPost.afterBuilder trace after index origin reply).published)
    (new : (publication, recordedOrigin) ∉ trace.published) :
    RawCtxSourcePublishedPath.Cached (RawCtxSelectedQueryTrace.rootVector entry.refined.send_chain)
      publication.2 afterState.1.1.2.1 := by
  obtain ⟨response, peer, rfl, present, rfl, _⟩ :=
    PqxdhInitialOriginPost.builder_recorded trace after index origin reply publication recordedOrigin recorded new
  obtain ⟨actualPeer, actualPresent, path⟩ :=
    supplied_build source writer stage external supplied entry initialized sender index metadata ready
      before after state afterState response supported
  have same : actualPeer = peer := Option.some.inj (actualPresent.symm.trans present)
  subst peer
  obtain ⟨earlier, walked⟩ := path
  exact ⟨earlier, RawCtxSelectedQueryTrace.rootVector actualPeer.kernel.send_chain, walked⟩

end BeaconcryptCore.Computational.PqxdhInitialOriginBuilderPath

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginBuilderPath.send_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginBuilderPath.send_path
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginBuilderPath.after_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginBuilderPath.after_path
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginBuilderPath.candidate_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginBuilderPath.candidate_path
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginBuilderPath.ready_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginBuilderPath.ready_path
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginBuilderPath.build_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginBuilderPath.build_path
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginBuilderPath.supplied_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginBuilderPath.supplied_path
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginBuilderPath.supplied_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginBuilderPath.supplied_build
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginBuilderPath.recorded_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginBuilderPath.recorded_cached
