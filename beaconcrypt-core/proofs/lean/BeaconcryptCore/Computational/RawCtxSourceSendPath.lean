import BeaconcryptCore.Computational.RawCtxPublishedLineage
import BeaconcryptCore.Computational.RawCtxPendingNonKdfStore

/-!
The selected sender's original finite counter is linked to the actual retained private cache. A source send extends the cached directional path with its own complete response even if sealing fails. Private callback support, original exhaustion and all primitive state are retained. This is an operational publication-reach invariant, not an independent-input or secrecy assumption.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSourceSendPath
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectiveChainGame RawCtxCursorLineage RawCtxKdfRequestTable
variable {A : Type}

noncomputable def native (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat) :=
  RawCtxPendingSelectiveFamily.backend (Auxiliary := A) source writer stage ∘ₛ RawCtxServerServices.nativeLift

noncomputable def sendImpl (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat) :=
  (native (A := A) source writer stage ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter

def Path (root : RootOutput) (entry : ConcreteRatchetKernel) (cache : Table) : Prop :=
  ∃ earlier, walk cache entry.refined.control.send_sequence.val root =
    some (earlier, RawCtxSelectedQueryTrace.rootVector entry.refined.send_chain)

/-- The actual typed private request returns its full original selective response and complete cache/cursor update. -/
theorem private_call (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (request : SymmetricRatchetKdfRequest) (state : RawCtxPendingSelectiveFamily.State A) :
    (native source writer stage (.inl request)).run state =
      (fun result => (fullResponse result.1, (state.1, result.2))) <$>
        privateStep source stage (address request) state.2 := by
  simp [native, RawCtxPendingSelectiveFamily.backend, QueryImpl.compose, RawCtxServerServices.nativeLift,
    RawCtxSelectiveKdfFamily.compiler, handler, OracleSpec.query, StateT.run]
  change (((fun output => fullResponse output) <$> (show
    StateT (RawCtxPendingSelectiveFamily.State A) ProbComp FullOutput from fun state =>
      (fun result => (result.1, (state.1, result.2))) <$>
        privateStep source stage (address request) state.2)).run state) = _
  rw [StateT.run_map]
  change (fun reply => (fullResponse reply.1, reply.2)) <$>
    ((fun result => (result.1, (state.1, result.2))) <$> privateStep source stage (address request) state.2) = _
  simp only [Functor.map_map]

set_option backward.isDefEq.respectTransparency false in
/-- Actual post-derivation sealing preserves the complete private table and cursor through every optional primitive outcome. -/
theorem seal_store (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (pending : SendSeal RawCtxSourceSend.SealContext) (state : RawCtxPendingSelectiveFamily.State A)
    (result : Option RawCtxSourceSend.Encrypted × RawCtxPendingSelectiveFamily.State A)
    (supported : result ∈ support ((sendImpl source writer stage (.inr pending)).run state)) :
    result.2.2 = state.2 := by
  apply RawCtxPendingNonKdfStore.native_store source writer stage
    (simulateQ RawCtxMixedOwner.sendAdapter (RawCtxSourceSend.adapter (.inr pending)))
    (RawCtxPendingNonKdfStore.send_zero pending) state result
  simpa only [sendImpl, native, QueryImpl.compose, QueryImpl.simulateQ_compose] using supported

/-- The original send private branch invokes the actual shared private derivation handler exactly once. -/
theorem send_private (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (request : SymmetricRatchetKdfRequest) :
    sendImpl (A := A) source writer stage (.inl request) = native source writer stage (.inl request) := by
  simp [sendImpl, QueryImpl.compose, RawCtxSourceSend.adapter, RawCtxMixedOwner.sendAdapter,
    RawCtxMixedOwner.sendLift, RawCtxSourceSeal.nativeAdapter, OracleSpec.query]

/-- Actual retained bindings remain available to the sender after any source cache extension. -/
theorem path_extends (root : RootOutput) (entry : ConcreteRatchetKernel) (before after : Table)
    (valid : Path root entry before) (extension : Extends before after) : Path root entry after := by
  obtain ⟨earlier, walked⟩ := valid
  exact ⟨earlier, walk_extends before after extension _ _ _ walked⟩

/-- Source resumption installs exactly the next32 coordinate of the same retained complete response. -/
theorem resumed_chain (pending : SendKdf RawCtxSourceSend.SealContext) (output : FullOutput) :
    (RawCtxSourceSend.resumeSend pending (fullResponse output)).advanced.refined.send_chain =
      RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain output) := by
  obtain ⟨stepped, parsed, ready⟩ := RawCtxSourceSend.resumeSend_fields pending (fullResponse output)
  have decoded := RawCtxInterpretedReceive.decodeResponse_exact (fullResponse output)
  simp only [RawCtxInterpretedReceive.nativeStep, parsed, RawCtxMaterialInterpretation.rust_map_ok, RawCtxFreshChainCut.decoded_parts] at decoded
  have same := congrArg Prod.fst (RustM.ok.inj decoded)
  simpa only [ready] using same

private theorem chain_address (chain : RatchetChain) :
    address (RawCtxChainSend.nativeRequest chain) =
      RawCtxFirstParentRisk.inputAddress (RawCtxSelectedQueryTrace.rootVector chain) := by
  have info : PqxdhRefinement.absBytes ratchet.SYM_RATCHET_INFO = Pqxdh.INFO_R := by
    simpa only [pqxdh.SYM_RATCHET_INFO] using PqxdhRefinement.absBytes_SYM_RATCHET_INFO
  exact congrArg (fun domain => (⟨domain, PqxdhRefinement.absBytes chain.bytes⟩ : JointKdfAddress)) info

set_option backward.isDefEq.respectTransparency false in
/-- Every actual send retains all earlier cache bindings and extends its original directional path exactly when source admission advances, independently of the seal result. -/
theorem send_path (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (root : RootOutput) (entry : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext)
    (state : RawCtxPendingSelectiveFamily.State A) (valid : Path root entry state.2.1)
    (result : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) × RawCtxPendingSelectiveFamily.State A)
    (supported : result ∈ support ((simulateQ (sendImpl source writer stage)
      (RawCtxSourceSend.send entry context)).run state)) :
    Extends state.2.1 result.2.2.1 ∧ Path root result.1.1 result.2.2.1 := by
  by_cases exhausted : entry.refined.control.send_sequence = core.num.U64.MAX
  · rw [RawCtxSourceSend.send_exhausted entry context exhausted] at supported
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact ⟨fun _ _ known => known, valid⟩
  · obtain ⟨pending, response, afterKdf, entryEq, contextEq, inputEq, infoEq,
      kdf, sealed, readyEq, sequenceEq, rest⟩ :=
      RawCtxSourceSend.send_nonexhausted_support (sendImpl source writer stage) entry context state exhausted result supported
    rw [send_private, private_call, support_map] at kdf
    obtain ⟨⟨output, afterStore⟩, drawn, same⟩ := kdf
    cases same
    have unchanged := seal_store source writer stage (RawCtxSourceSend.resumeSend pending (fullResponse output))
      (state.1, afterStore) (result.1.2, result.2) sealed
    change result.2.2 = afterStore at unchanged
    rw [unchanged]
    have extension := private_extends source stage (address pending.request) state.2 (output, afterStore) drawn
    refine ⟨extension, ?_⟩
    obtain ⟨earlier, walked⟩ := valid
    have previous := walk_extends state.2.1 afterStore.1 extension _ _ _ walked
    have requested : address pending.request = RawCtxFirstParentRisk.inputAddress
        (RawCtxSelectedQueryTrace.rootVector entry.refined.send_chain) := by
      rw [← chain_address]
      simp only [address, RawCtxChainSend.nativeRequest, inputEq, infoEq]
    have installed : afterStore.1 (RawCtxFirstParentRisk.inputAddress
        (RawCtxSelectedQueryTrace.rootVector entry.refined.send_chain)) = some output := by
      have stored := congrArg (fun store : Store => store.1 (address pending.request))
        (private_state source stage (address pending.request) state.2 (output, afterStore) drawn)
      rw [← requested]
      simpa using stored
    have next : RawCtxSelectedQueryTrace.rootVector result.1.1.refined.send_chain =
        PqxdhOrderedChainHybrids.nextChain output := by
      rw [readyEq, resumed_chain, RawCtxSelectedQueryTrace.rootVector_concrete]
    refine ⟨earlier ++ [RawCtxSelectedQueryTrace.rootVector entry.refined.send_chain], ?_⟩
    rw [sequenceEq, next]
    simp [walk, previous, installed]

/-- The actual zero-counter constructor starts the selected send path at its supplied initial half under every preexisting private cache. -/
theorem initialized {AD PT CT : Type} (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (root : RootOutput) (receive : RatchetChain) (cache : Table) (entry : ConcreteRatchetKernel)
    (created : ConcreteRatchetKernel.new (RawCtxFreshChainCut.concreteChain root) receive = ok entry) :
    Path root entry cache := by
  obtain ⟨actual, built, refined, _⟩ := new_reachable cr (RawCtxFreshChainCut.concreteChain root) receive
  have same := RustM.ok.inj (built.symm.trans created)
  subst entry
  refine ⟨[], ?_⟩
  rw [refined.sendSequence, refined.sendChain, RawCtxSelectedQueryTrace.rootVector_concrete]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The original optional sealing reply carries the actual source pending sequence, regardless of primitive state and ciphertext value. -/
theorem seal_sequence (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (pending : SendSeal RawCtxSourceSend.SealContext) (state : RawCtxPendingSelectiveFamily.State A)
    (result : Option RawCtxSourceSend.Encrypted × RawCtxPendingSelectiveFamily.State A)
    (supported : result ∈ support ((sendImpl source writer stage (.inr pending)).run state))
    (reply : RawCtxSourceSend.Encrypted) (returned : result.1 = some reply) : reply.sequence = pending.sequence := by
  simp only [sendImpl, QueryImpl.apply_compose, RawCtxSourceSend.adapter,
    bind_pure_comp, simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨⟨ciphertext, after⟩, _, rfl⟩ := supported
  cases ciphertext with
  | none => cases returned
  | some ciphertext =>
    simp only [Option.map_some, Option.some.injEq] at returned
    subst reply
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- A successful original source reply names exactly the advanced sender counter in the same full supported execution. -/
theorem published_sequence (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (entry : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext) (state : RawCtxPendingSelectiveFamily.State A)
    (result : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) × RawCtxPendingSelectiveFamily.State A)
    (supported : result ∈ support ((simulateQ (sendImpl source writer stage) (RawCtxSourceSend.send entry context)).run state))
    (reply : RawCtxSourceSend.Encrypted) (returned : result.1.2 = some reply) :
    reply.sequence = result.1.1.refined.control.send_sequence := by
  by_cases exhausted : entry.refined.control.send_sequence = core.num.U64.MAX
  · rw [RawCtxSourceSend.send_exhausted entry context exhausted] at supported
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    cases returned
  · obtain ⟨pending, began, _, _, _, _, sequence, _, _, _⟩ := RawCtxSourceSend.beginSend_fields entry context exhausted
    rw [RawCtxSourceSend.send, began] at supported
    obtain ⟨response, afterKdf, sealed, afterSeal, _, sealReached, rfl⟩ :=
      RawCtxSourceSend.requested_support (sendImpl source writer stage) pending state result supported
    have actual := seal_sequence source writer stage (RawCtxSourceSend.resumeSend pending response)
      afterKdf (sealed, afterSeal) sealReached reply returned
    obtain ⟨stepped, _, ready⟩ := RawCtxSourceSend.resumeSend_fields pending response
    simpa only [ready, sequence] using actual

/-- Every actual successful publication leaves the entire initial-root path through that record's derivation in the real private cache; the later checker cannot supply a missing derivation. -/
theorem published_path (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (root : RootOutput) (entry : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext)
    (state : RawCtxPendingSelectiveFamily.State A) (valid : Path root entry state.2.1)
    (result : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) × RawCtxPendingSelectiveFamily.State A)
    (supported : result ∈ support ((simulateQ (sendImpl source writer stage) (RawCtxSourceSend.send entry context)).run state))
    (reply : RawCtxSourceSend.Encrypted) (returned : result.1.2 = some reply) :
    ∃ earlier, walk result.2.2.1 reply.sequence.val root =
      some (earlier, RawCtxSelectedQueryTrace.rootVector result.1.1.refined.send_chain) := by
  rw [published_sequence source writer stage entry context state result supported reply returned]
  exact (send_path source writer stage root entry context state valid result supported).2

end BeaconcryptCore.Computational.RawCtxSourceSendPath

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSendPath.private_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSendPath.private_call

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSendPath.seal_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSendPath.seal_store

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSendPath.send_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSendPath.send_private

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSendPath.path_extends' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSendPath.path_extends

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSendPath.resumed_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSendPath.resumed_chain

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSendPath.send_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSendPath.send_path

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSendPath.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSendPath.initialized

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSendPath.seal_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSendPath.seal_sequence

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSendPath.published_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSendPath.published_sequence

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceSendPath.published_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSendPath.published_path
