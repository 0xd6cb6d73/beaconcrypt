import BeaconcryptCore.Computational.PqxdhInitialSelectedBuilder
import BeaconcryptCore.Computational.RawCtxPendingNativeCallbacks

/-!
The analysis-only root-domain marker is removed through the actual typed source receive/send programs. Arbitrary KdfSpec inputs are not assumed to have the ratchet label. Complete source calls, first-send builders and optional publication preserve the original private lookup and all other shared effects.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSentinelSource
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedParentTable PqxdhInitialGenericProtocolBuilder
variable {A M P I D K : Type} {S B : Nat}

noncomputable def priorKdf (prior : Prior) :
    QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp) :=
  fun request => pure (RawCtxKdfRequestTable.fullResponse (prior (RawCtxKdfRequestTable.address request)))

/-- The unmarked retained private handler becomes the exact production private HKDF interface at the production lookup. -/
theorem prior_source (source : FixedHkdfSha512NoSaltSource) :
    priorKdf (A := A) (PqxdhJointKdf.productionStream source.crypto) = RawCtxSourceHkdf.kdfImpl source := by
  funext request
  rfl

private theorem non_kdf (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (left right : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (query : RawCtxMixedOwner.NativeSpec.Domain) (notKdf : query.isLeft = false) :
    RawCtxMixedShared.sharedImpl source.crypto writer left query =
      RawCtxMixedShared.sharedImpl source.crypto writer right query := by
  rcases query with request | (sealing | (opening | (bytes | frame)))
  · cases notKdf
  all_goals simp [RawCtxMixedShared.sharedImpl, RawCtxMixedShared.sharedAdapter, QueryImpl.compose, OracleSpec.query]
  all_goals rfl

private theorem typed_kdf (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (other target : RootOutput) (extra : NonceOutput) (chain : RatchetChain) :
    RawCtxMixedShared.sharedImpl source.crypto writer (retainedKdf (A := A) prior (RawCtxInitialSentinel.entry other extra) target)
      (.inl (RawCtxChainSend.nativeRequest chain)) =
      RawCtxMixedShared.sharedImpl source.crypto writer (priorKdf prior)
        (.inl (RawCtxChainSend.nativeRequest chain)) := by
  simp [RawCtxMixedShared.sharedImpl, QueryImpl.compose, RawCtxMixedShared.sharedAdapter, OracleSpec.query]
  change (pure (RawCtxSelectedParentSource.response prior (RawCtxInitialSentinel.entry other extra) target
    (RawCtxChainSend.nativeRequest chain)) : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp RatchetKdfResponse) =
      pure (RawCtxKdfRequestTable.fullResponse (prior (RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest chain))))
  rw [RawCtxSelectedParentSource.response, RawCtxInitialSentinel.lookup_private]

/-- Every actual typed pending source callback ignores the analysis marker; all non-KDF effects and public replies remain unchanged. -/
theorem pending_marker (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (other target : RootOutput) (extra : NonceOutput)
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)) :
    RawCtxPendingNativeCalls.pending
      (RawCtxMixedShared.sharedImpl source.crypto writer (retainedKdf prior (RawCtxInitialSentinel.entry other extra) target)) publicCalls =
      RawCtxPendingNativeCalls.pending (RawCtxMixedShared.sharedImpl source.crypto writer (priorKdf prior)) publicCalls := by
  funext query
  rcases query with (request | opening) | ((request | sealing) | publicQuery)
  · rw [RawCtxPendingNativeCallbacks.receive_kdf, RawCtxPendingNativeCallbacks.receive_kdf, typed_kdf]
  · exact RawCtxPendingNativeCallbacks.non_kdf _ _ publicCalls (non_kdf source writer _ _) _ rfl
  · rw [RawCtxPendingNativeCallbacks.send_kdf, RawCtxPendingNativeCallbacks.send_kdf, typed_kdf]
  · exact RawCtxPendingNativeCallbacks.non_kdf _ _ publicCalls (non_kdf source writer _ _) _ rfl
  · exact RawCtxPendingNativeCallbacks.non_kdf _ _ publicCalls (non_kdf source writer _ _) _ rfl

/-- Every complete native source send ignores the marker, including KDF resumption, failed seal, advanced kernel and shared poststate. -/
theorem send_marker (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (other target : RootOutput) (extra : NonceOutput)
    (kernel : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext) :
    simulateQ ((RawCtxMixedShared.sharedImpl source.crypto writer (retainedKdf (A := A) prior (RawCtxInitialSentinel.entry other extra) target)
      ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter) (RawCtxSourceSend.send kernel context) =
      simulateQ ((RawCtxMixedShared.sharedImpl source.crypto writer (priorKdf prior)
        ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter) (RawCtxSourceSend.send kernel context) := by
  cases kernel with
  | mk kernel =>
      rw [RawCtxGenericNativeCalls.send_realized, RawCtxGenericNativeCalls.send_realized,
        ← RawCtxPendingNativeCalls.send_call _ (RawCtxSelectedParentOwner.publicImpl source writer),
        ← RawCtxPendingNativeCalls.send_call _ (RawCtxSelectedParentOwner.publicImpl source writer), pending_marker]

/-- Every complete native source receive ignores the marker, preserving skips, cache use, optional plaintext, rejection and rollback. -/
theorem receive_marker (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (other target : RootOutput) (extra : NonceOutput)
    (kernel : ConcreteRatchetKernel) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    simulateQ ((RawCtxMixedShared.sharedImpl source.crypto writer (retainedKdf (A := A) prior (RawCtxInitialSentinel.entry other extra) target)
      ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter) (RawCtxOwnerOracle.receive kernel sequence context) =
      simulateQ ((RawCtxMixedShared.sharedImpl source.crypto writer (priorKdf prior)
        ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter) (RawCtxOwnerOracle.receive kernel sequence context) := by
  cases kernel with
  | mk kernel =>
      rw [RawCtxGenericNativeCalls.receive_realized, RawCtxGenericNativeCalls.receive_realized,
        ← RawCtxPendingNativeCalls.receive_call _ (RawCtxSelectedParentOwner.publicImpl source writer),
        ← RawCtxPendingNativeCalls.receive_call _ (RawCtxSelectedParentOwner.publicImpl source writer), pending_marker]

/-- The unmarked private source lookup realizes the hidden-half builder from the first send, with no source marker binding and no callback-compatibility premise. -/
theorem selected_build (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (other target : RootOutput) (extra : NonceOutput)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (initial : RustM RawCtxSelectedChain.Kernel) (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready)
    (state : PqxdhInitialGenericProtocol.State RawCtxSelectedChain.Kernel M P I D K A S B) :
    (PqxdhInitialPrivateKdf.build source writer (priorKdf prior)
      (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target) <$> initial)
      aux sender index metadata ready).run
      (PqxdhInitialGenericProtocol.native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) state) =
      Prod.map id (PqxdhInitialGenericProtocol.native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target))) <$>
        (build source (RawCtxSelectedParentCalls.labelCalls source writer prior (RawCtxInitialSentinel.entry other extra)
          (RawCtxSelectedParentCalls.childResponse prior (RawCtxInitialSentinel.entry other extra) target)) aux initial
          sender index metadata ready).run state := by
  apply build_native
  intro kernel context
  rw [← send_marker source writer prior other target extra, ← retained_backend]
  exact PqxdhInitialGenericPublication.selected_send source writer prior (RawCtxInitialSentinel.entry other extra) target kernel context

/-- The actual default private-HKDF initializer service reaches the selected-half builder before its first ciphertext, from the complete original pre-draw source state. -/
theorem supplied_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (second : Bool) (other target : RootOutput) (extra : NonceOutput)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    simulateQ (PqxdhInitialReplyErasure.supplied (RawCtxSelectedInitialConstructor.response64
      (RawCtxInitialSentinelSampler.join second other target)))
      ((PqxdhInitialServiceBuilder.protocolBuild source writer aux sender index metadata ready).run state) =
      Prod.map id (PqxdhInitialGenericProtocol.native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target))) <$>
        (build source (RawCtxSelectedParentCalls.labelCalls source writer (PqxdhJointKdf.productionStream source.crypto)
          (RawCtxInitialSentinel.entry other extra)
          (RawCtxSelectedParentCalls.childResponse (PqxdhJointKdf.productionStream source.crypto) (RawCtxInitialSentinel.entry other extra) target))
          aux (RawCtxInitialSentinelSampler.labelInitial second false other)
          sender index metadata (PqxdhInitialBuilderCut.eraseRoot ready)).run
            (PqxdhInitialGenericProtocol.fromNative PqxdhInitialSelectedBuilder.knownKernel state) := by
  rw [PqxdhInitialSuppliedBuilder.protocol_supplied, ← PqxdhInitialPrivateKdf.build_source,
    PqxdhInitialSelectedBuilder.kernel_response, ← prior_source]
  simpa only [PqxdhInitialSelectedBuilder.known_state] using selected_build source writer
    (PqxdhJointKdf.productionStream source.crypto) other target extra aux
    (RawCtxInitialSentinelSampler.labelInitial second false other) sender index metadata
    (PqxdhInitialBuilderCut.eraseRoot ready)
    (PqxdhInitialGenericProtocol.fromNative PqxdhInitialSelectedBuilder.knownKernel state)

end BeaconcryptCore.Computational.PqxdhInitialSentinelSource

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSentinelSource.prior_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSentinelSource.prior_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSentinelSource.pending_marker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSentinelSource.pending_marker

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSentinelSource.send_marker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSentinelSource.send_marker

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSentinelSource.receive_marker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSentinelSource.receive_marker

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSentinelSource.selected_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSentinelSource.selected_build

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSentinelSource.supplied_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSentinelSource.supplied_source
