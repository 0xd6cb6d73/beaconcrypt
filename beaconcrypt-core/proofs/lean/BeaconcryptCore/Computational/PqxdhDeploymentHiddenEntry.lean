-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels
import BeaconcryptCore.Computational.PqxdhDeploymentHiddenLayout
import BeaconcryptCore.Computational.PqxdhServerAuthEntryServices

/-!
# Hidden-entry wrappers with the item 2 service signatures

The hidden-entry build and finish of the common deployment experiment, as instances of the two hidden fields of `PqxdhServerAuthEntryFactor.Services` (item 2 plan section 18). `buildFactor` and `finishFactor` are the factor forms at the 108-byte value `joinOutput m seed` assembled from the environment material and the world seed; `buildFactor_services` and `finishFactor_services` identify them with the fields of `PqxdhServerAuthEntryFactor.factorServices`. `finishPointed` is the erased finish that reports the opening input it discards, `finishErasedSvc` forgets that report, and `finishFactor_pointed` shows that the factor-form finish is the pointed finish followed by the completion of one CTX-cache point, the form `LazyOracleDiscard.discard_erase` erases.

The CTX-obliviousness of the wrappers (critique M5) is proved from one fact about the native primitives (`nativeImpl_commutes`): every KDF, hash, seal and opening request of the shared primitive interpreter commutes, in law, with completing any point of the lazily sampled CTX cache. Hence the factor-form build (`buildFactor_commutes_ctx`), the factor-form finish (`finishFactor_commutes_ctx`) and the erased finish (`finishErased_commutes_ctx`) commute with such completions.

The accounting of the finish-time receive (owner ruling of CE plan section 25) is `finish_accounting`: on every raw input the receive of a hidden finish issues at most 51 chain-step KDF requests and at most one opening request, and the hidden finish with the real HKDF and the BLAKE2b opening left as a CTX-oracle query issues at most one BLAKE2b query. `erased_le` shows that the erased finish issues no more queries of any kind than the factor-form finish under any primitive interpreter, and `erased_reject` that on a raw whose decoded sequence is not one it calls no primitive at all.

These are equalities of programs, equalities in law of the lazy CTX cache and query bounds. They make no authentication, secrecy or independence claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry
open PqxdhServerAuthSendFactor (Kernel Factor resolve)
open RawCtxSelectedChain (Slot)
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentHiddenLayout (Material joinOutput)
open PqxdhDeploymentHiddenKernels (ctxLens openPoint finishErased factoredBody SeqOne discardedInput)
open LazyOracleDiscard (Commutes StateLens CacheLens)

/-- The hidden-build service type of item 2's services (`PqxdhServerAuthEntryFactor.Services.hiddenBuild`). -/
abbrev HiddenBuild := PqxdhServerRelatedRootConsumer.Returned → Option Pqxdh.Bytes →
  PqxdhServerAuthEntryFactor.ServerState →
    StateT PqxdhServerAuthEntryFactor.SealState ProbComp
      (RustM (Option PqxdhServerRegistrationPublication.Response × PqxdhServerAuthEntryFactor.ServerState))

/-- The hidden-finish service type of item 2's services (`PqxdhServerAuthEntryFactor.Services.hiddenAfter`). -/
abbrev HiddenAfter (Response : Type) := PqxdhPhase2DhMetadata.Prepared Response →
  StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp (Option PqxdhBeaconPhase2Publication.Staged)

section Wrappers
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- The factor-form hidden build at the 108-byte value assembled from the material and the seed: the logged factored Server build. -/
noncomputable def buildFactor (m : Material) (seed : PqxdhRecordLiftSeed.Seed) : HiddenBuild := fun token payload server =>
  PqxdhServerAuthLoggedSendFactor.factored (fun entry _ _ => pure (entry, .None))
    (PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks) setup.source
    (PqxdhServerAuthLoggedSendFactor.loggedAux setup codec checks)
    (PqxdhServerAuthCtxMaterial.factor (joinOutput m seed)) token.pending payload () server

/-- The factor-form hidden build is the hidden-build field of item 2's factor services at `joinOutput m seed`. -/
theorem buildFactor_services (context : PqxdhServerAuthEntryFactor.Context KemSK) (m : Material)
    (seed : PqxdhRecordLiftSeed.Seed) :
    buildFactor setup codec checks m seed =
      (PqxdhServerAuthEntryFactor.factorServices setup codec checks context (joinOutput m seed)).hiddenBuild := rfl

/-- The factor-form hidden finish at the 108-byte value assembled from the material and the seed: the factored Beacon tail with the native primitives. -/
noncomputable def finishFactor (m : Material) (seed : PqxdhRecordLiftSeed.Seed) : HiddenAfter Response := fun pending =>
  PqxdhServerAuthBeaconFactor.factored (PqxdhServerAuthBeaconFactor.nativePrim setup codec)
    (fun entry _ => pure (entry, none)) setup.source (fun response => pure (codec.application response))
    codec.frameRead (PqxdhPhase2DhRootConsumer.cleared pending)
    (PqxdhServerAuthCtxMaterial.factor (joinOutput m seed))

/-- The factor-form hidden finish is the hidden-finish field of item 2's factor services at `joinOutput m seed`. -/
theorem finishFactor_services (context : PqxdhServerAuthEntryFactor.Context KemSK) (m : Material)
    (seed : PqxdhRecordLiftSeed.Seed) :
    finishFactor setup codec m seed =
      (PqxdhServerAuthEntryFactor.factorServices setup codec checks context (joinOutput m seed)).hiddenAfter := rfl

/-- The erased hidden finish in pointed form: a raw whose decoded sequence is not one makes no primitive call, and the step reports the opening input it discarded. -/
noncomputable def finishPointed (m : Material) (seed : PqxdhRecordLiftSeed.Seed)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) :
    StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp
      (Option PqxdhBeaconPhase2Publication.Staged × Option RawCtxWholeOwner.OpenInput) :=
  finishErased (PqxdhServerAuthBeaconFactor.nativePrim setup codec) (fun entry _ => pure (entry, none)) setup.source
    (fun response => pure (codec.application response)) codec.frameRead (PqxdhPhase2DhRootConsumer.cleared pending)
    (PqxdhServerAuthCtxMaterial.factor (joinOutput m seed))

/-- The erased hidden finish with the service type: the pointed finish without its report. -/
noncomputable def finishErasedSvc (m : Material) (seed : PqxdhRecordLiftSeed.Seed) : HiddenAfter Response :=
  fun pending => Prod.fst <$> finishPointed setup codec m seed pending

/-- C7 local part at the service level: the factor-form hidden finish is the pointed finish followed by the completion of the CTX point of the opening it discarded. -/
theorem finishFactor_pointed (m : Material) (seed : PqxdhRecordLiftSeed.Seed)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (state : RawCtxSharedPrimitive.SharedState Unit) :
    (finishFactor setup codec m seed pending).run state =
      (finishPointed setup codec m seed pending).run state >>= fun r =>
        (r.1.1, ·) <$> ctxLens.completeOpt (spec := CtxRomAuth.CtxRO) (r.1.2.bind openPoint) r.2 :=
  PqxdhDeploymentHiddenKernels.finish_pointed_native setup codec _ setup.source _ codec.frameRead _ _ state

/-- Item 2's services with the factor-form hidden entry at `joinOutput m seed`. -/
noncomputable def factorSvc (context : PqxdhServerAuthEntryFactor.Context KemSK) (m : Material)
    (seed : PqxdhRecordLiftSeed.Seed) :
    PqxdhServerAuthEntryFactor.Services Response PqxdhServerAuthEntryFactor.HiddenTable :=
  PqxdhServerAuthEntryFactor.factorServices setup codec checks context (joinOutput m seed)

/-- Item 2's services with the erased hidden finish: only the hidden-finish field differs from `factorSvc`. -/
noncomputable def erasedSvc (context : PqxdhServerAuthEntryFactor.Context KemSK) (m : Material)
    (seed : PqxdhRecordLiftSeed.Seed) :
    PqxdhServerAuthEntryFactor.Services Response PqxdhServerAuthEntryFactor.HiddenTable :=
  { factorSvc setup codec checks context m seed with hiddenAfter := finishErasedSvc setup codec m seed }

/-- The two service instances share their derivation, table and build fields. -/
theorem erasedSvc_fields (context : PqxdhServerAuthEntryFactor.Context KemSK) (m : Material)
    (seed : PqxdhRecordLiftSeed.Seed) :
    (erasedSvc setup codec checks context m seed).derive = (factorSvc setup codec checks context m seed).derive ∧
      (erasedSvc setup codec checks context m seed).table = (factorSvc setup codec checks context m seed).table ∧
      (erasedSvc setup codec checks context m seed).hiddenBuild = buildFactor setup codec checks m seed ∧
      (erasedSvc setup codec checks context m seed).hiddenAfter = finishErasedSvc setup codec m seed :=
  ⟨rfl, rfl, rfl, rfl⟩

end Wrappers


/-! ### CTX-obliviousness of the native primitives and of the wrappers (critique M5) -/

/-- The CTX-cache lens of a shared primitive state with any auxiliary component. -/
abbrev sharedLens (Auxiliary : Type) : CacheLens CtxRomAuth.CtxRO (RawCtxSharedPrimitive.SharedState Auxiliary) :=
  StateLens.snd Auxiliary CtxRomAuth.CtxRO.QueryCache

/-- The native BLAKE2b request is the lazy query on the focused CTX cache, with the digest returned as bytes. -/
theorem openingImpl_hash {Auxiliary : Type} (c : Pqxdh.Crypto) (bytes : Pqxdh.Bytes) :
    RawCtxSharedPrimitive.openingImpl (Auxiliary := Auxiliary) c (.inl bytes) =
      (fun digest => some (List.Vector.toList digest)) <$>
        (sharedLens Auxiliary).query (spec := CtxRomAuth.CtxRO) ((), bytes) := by
  apply StateT.ext
  rintro ⟨auxiliary, cache⟩
  rw [StateT.run_map]
  simp only [RawCtxSharedPrimitive.openingImpl, StateLens.query, StateLens.snd, StateT.run, Functor.map_map]
  rw [map_eq_bind_pure_comp]
  rfl

/-- Every request of the shared native primitive interpreter (real HKDF, BLAKE2b on the shared cache, base opening) commutes with completions of the CTX cache. -/
theorem nativeImpl_commutes {Auxiliary : Type} (c : Pqxdh.Crypto) (source : FixedHkdfSha512NoSaltSource)
    (query : RawCtxSourceOpen.NativeSpec.Domain) :
    Commutes (sharedLens Auxiliary)
      (RawCtxSharedPrimitive.nativeImpl c (RawCtxSourceHkdf.kdfImpl source) query) := by
  rcases query with request | bytes | input
  · exact LazyOracleDiscard.commutes_pure _ _
  · change Commutes (sharedLens Auxiliary) (RawCtxSharedPrimitive.openingImpl c (.inl bytes))
    rw [openingImpl_hash]
    exact LazyOracleDiscard.commutes_map _ _ (LazyOracleDiscard.commutes_query _ _)
  · exact LazyOracleDiscard.commutes_pure _ _

/-- Any adapter into the shared native primitives keeps every request commuting with completions of the CTX cache. -/
theorem compose_commutes {Auxiliary ι' : Type} {spec' : OracleSpec ι'} (c : Pqxdh.Crypto)
    (source : FixedHkdfSha512NoSaltSource) (adapter : QueryImpl spec' (OracleComp RawCtxSourceOpen.NativeSpec))
    (query : spec'.Domain) :
    Commutes (sharedLens Auxiliary)
      ((RawCtxSharedPrimitive.nativeImpl c (RawCtxSourceHkdf.kdfImpl source) ∘ₛ adapter) query) := by
  rw [QueryImpl.apply_compose]
  exact LazyOracleDiscard.commutes_simulateQ _ _ (nativeImpl_commutes c source) _

/-- The Server registration interpreter commutes with completions of the CTX cache whenever its auxiliary callbacks do. -/
theorem registrationImpl_commutes {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (auxCommutes : ∀ query, Commutes (sharedLens Auxiliary) (aux query))
    (query : PqxdhServerRegistrationPublication.NativeSpec.Domain) :
    Commutes (sharedLens Auxiliary)
      (PqxdhRegistrationProtocolState.registrationImpl source writer aux query) := by
  rcases query with request | request
  · change Commutes (sharedLens Auxiliary)
      ((RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) ∘ₛ
        RawCtxMixedOwner.sendLift) request)
    rw [QueryImpl.apply_compose]
    exact LazyOracleDiscard.commutes_simulateQ _ _
      (fun query => compose_commutes source.crypto source (RawCtxMixedShared.sharedAdapter source.crypto writer) query) _
  · exact auxCommutes request

/-- The Server's response-tail callbacks are stateless. -/
theorem tailAux_commutes {Auxiliary Reader Response : Type} (codec : Codec Reader Response) (checks : Checks)
    (query : PqxdhServerRegistrationPublication.AuxSpec.Domain) :
    Commutes (sharedLens Auxiliary) (PqxdhServerAuthExperiment.tailAux (A := Auxiliary) codec checks query) := by
  cases query <;> exact LazyOracleDiscard.commutes_pure _ _

section Native
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- The native response tail commutes with completions of the CTX cache. -/
theorem nativeTail_commutes {Auxiliary : Type} (query : PqxdhServerRegistrationPublication.TailSpec.Domain) :
    Commutes (sharedLens Auxiliary) (PqxdhServerAuthExperiment.nativeTail (A := Auxiliary) setup codec checks query) := by
  simp only [PqxdhServerAuthExperiment.nativeTail]
  rw [QueryImpl.apply_compose]
  exact LazyOracleDiscard.commutes_simulateQ _ _
    (registrationImpl_commutes setup.source codec.frameWrite _ (tailAux_commutes codec checks)) _

/-- The logged native response tail commutes with completions of the CTX cache: the seal log is a frame. -/
theorem tailImpl_commutes (query : PqxdhServerRegistrationPublication.TailSpec.Domain) :
    Commutes (sharedLens (List RawCtxSourceSend.SealContext)) (PqxdhServerAuthExperiment.tailImpl setup codec checks query) := by
  rcases query with (request | input) | query
  · exact nativeTail_commutes setup codec checks _
  · refine LazyOracleDiscard.commutes_bind _ (nativeTail_commutes setup codec checks _) (fun sealed => ?_)
    dsimp only
    split
    · refine LazyOracleDiscard.commutes_bind (sharedLens (List RawCtxSourceSend.SealContext)) ?_
        (fun _ => LazyOracleDiscard.commutes_pure _ _)
      refine LazyOracleDiscard.commutes_frame _ _ (fun state cache => ?_)
      simp only [StateT.run_modify, StateLens.snd, map_pure]
    · exact LazyOracleDiscard.commutes_pure _ _
  · exact nativeTail_commutes setup codec checks _

end Native

section Build
variable {σ ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec ι₀}
  [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)] {Metadata PeerMetadata Consumed : Type}
  (L : CacheLens spec₀ σ)

/-- A Rust result continuation commutes with completions when every continuation does. -/
theorem continueRust_commutes {α β : Type} (result : RustM α) (next : α → StateT σ ProbComp (RustM β))
    (hnext : ∀ value, Commutes L (next value)) :
    Commutes L (PqxdhInitialGenericBuilder.continueRust result next) := by
  cases result with
  | ok value => exact hnext value
  | fail error => exact LazyOracleDiscard.commutes_pure L _
  | div => exact LazyOracleDiscard.commutes_pure L _

/-- The first send and Phase 2 writing of a build commute with completions when the callbacks do. -/
theorem afterInitialization_commutes (calls : RawCtxChainOwner.Calls Kernel (StateT σ ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT σ ProbComp))
    (send : ∀ entry context, Commutes L (calls.send entry context)) (auxCommutes : ∀ query, Commutes L (aux query))
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (kernel : Kernel)
    (metadata : PeerMetadata) (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed) :
    Commutes L (PqxdhInitialGenericPublication.afterInitialization calls aux candidate authenticated kernel metadata
      state) := by
  unfold PqxdhInitialGenericPublication.afterInitialization
  refine LazyOracleDiscard.commutes_bind L (send _ _) (fun sent => ?_)
  rcases sent with ⟨advanced, encrypted⟩
  refine LazyOracleDiscard.commutes_bind L (auxCommutes _) (fun _ => ?_)
  cases encrypted with
  | none => exact LazyOracleDiscard.commutes_pure L _
  | some encrypted =>
      refine LazyOracleDiscard.commutes_bind L (auxCommutes _) (fun serialized => ?_)
      cases serialized with
      | none => exact LazyOracleDiscard.commutes_pure L _
      | some serialized => exact LazyOracleDiscard.commutes_pure L _

/-- The candidate admission and first send of a build commute with completions when the callbacks do. -/
theorem candidate_commutes (calls : RawCtxChainOwner.Calls Kernel (StateT σ ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT σ ProbComp))
    (send : ∀ entry context, Commutes L (calls.send entry context)) (auxCommutes : ∀ query, Commutes L (aux query))
    (initial : RustM Kernel) (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed) :
    Commutes L (PqxdhInitialGenericBuilder.candidate calls aux initial candidate data metadata state) := by
  unfold PqxdhInitialGenericBuilder.candidate
  refine LazyOracleDiscard.commutes_bind L (auxCommutes _) (fun valid => ?_)
  by_cases hvalid : (!valid) = true
  · simp only [hvalid, ite_true]
    exact LazyOracleDiscard.commutes_pure L _
  · simp only [hvalid, Bool.false_eq_true, ite_false]
    refine LazyOracleDiscard.commutes_bind L (auxCommutes _) (fun reserved => ?_)
    by_cases hreserved : (!reserved) = true
    · simp only [hreserved, ite_true]
      exact LazyOracleDiscard.commutes_pure L _
    · simp only [hreserved, Bool.false_eq_true, ite_false]
      refine continueRust_commutes L _ _ (fun kernel => ?_)
      split
      · exact LazyOracleDiscard.commutes_pure L _
      · split
        · refine LazyOracleDiscard.commutes_bind L (auxCommutes _) (fun allocated => ?_)
          by_cases hallocated : (!allocated) = true
          · simp only [hallocated, ite_true]
            exact LazyOracleDiscard.commutes_pure L _
          · simp only [hallocated, Bool.false_eq_true, ite_false]
            refine continueRust_commutes L _ _ (fun binding => ?_)
            exact LazyOracleDiscard.commutes_map L _
              (afterInitialization_commutes L calls aux send auxCommutes _ _ _ _ _)
        · exact LazyOracleDiscard.commutes_pure L _

/-- The generic Server build commutes with completions of a lensed cache whenever its send and auxiliary callbacks do. -/
theorem genericBuild_commutes (calls : RawCtxChainOwner.Calls Kernel (StateT σ ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT σ ProbComp))
    (send : ∀ entry context, Commutes L (calls.send entry context)) (auxCommutes : ∀ query, Commutes L (aux query))
    (initial : RustM Kernel) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed) :
    Commutes L (PqxdhServerAuthSendFactor.genericBuild calls aux initial pending data metadata state) := by
  unfold PqxdhServerAuthSendFactor.genericBuild
  refine continueRust_commutes L _ _ (fun next => ?_)
  cases next with
  | Err error => exact LazyOracleDiscard.commutes_pure L _
  | Ok next =>
      refine continueRust_commutes L _ _ (fun prepared => ?_)
      cases prepared with
      | Err error => exact LazyOracleDiscard.commutes_pure L _
      | Ok candidate => exact candidate_commutes L calls aux send auxCommutes _ _ _ _ _

end Build

section Factor
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- M5: the factor-form hidden build commutes with completions of the CTX cache of its seal state. -/
theorem buildFactor_commutes_ctx (m : Material) (seed : PqxdhRecordLiftSeed.Seed)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState) :
    Commutes (sharedLens (List RawCtxSourceSend.SealContext)) (buildFactor setup codec checks m seed token payload server) := by
  unfold buildFactor PqxdhServerAuthLoggedSendFactor.factored
  refine LazyOracleDiscard.commutes_map _ _ (genericBuild_commutes _ _ _ (fun entry context => ?_)
    (fun query => tailImpl_commutes setup codec checks (.inr query)) _ _ _ _ _)
  refine LazyOracleDiscard.commutes_simulateQ _ _ (fun query => ?_) _
  rcases query with slot | pending
  · exact LazyOracleDiscard.commutes_pure _ _
  · simp only [PqxdhServerAuthSendFactor.primLabels]
    rw [QueryImpl.apply_compose]
    exact LazyOracleDiscard.commutes_simulateQ _ _ (fun query => tailImpl_commutes setup codec checks (.inl query)) _

/-- M5: the factor-form hidden finish commutes with completions of the CTX cache. -/
theorem finishFactor_commutes_ctx (m : Material) (seed : PqxdhRecordLiftSeed.Seed)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) :
    Commutes ctxLens (finishFactor setup codec m seed pending) := by
  unfold finishFactor
  rw [PqxdhDeploymentHiddenKernels.factored_body]
  refine LazyOracleDiscard.commutes_bind ctxLens (LazyOracleDiscard.commutes_pure ctxLens _) (fun raw => ?_)
  cases raw with
  | none => exact LazyOracleDiscard.commutes_pure ctxLens _
  | some raw =>
      exact PqxdhDeploymentHiddenKernels.factoredBody_commutes setup codec _ setup.source codec.frameRead _ _ raw

/-- M5: the erased hidden finish commutes with completions of the CTX cache. -/
theorem finishErased_commutes_ctx (m : Material) (seed : PqxdhRecordLiftSeed.Seed)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) :
    Commutes ctxLens (finishErasedSvc setup codec m seed pending) :=
  PqxdhDeploymentHiddenKernels.finishErased_commutes setup codec _ setup.source _
    (fun _ => LazyOracleDiscard.commutes_pure ctxLens _) codec.frameRead _ _

/-- The pointed hidden finish without its report commutes with completions of the CTX cache (the `oblivious` premise of the engine). -/
theorem finishPointed_commutes_ctx (m : Material) (seed : PqxdhRecordLiftSeed.Seed)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) :
    Commutes ctxLens (Prod.fst <$> finishPointed setup codec m seed pending) :=
  finishErased_commutes_ctx setup codec m seed pending

end Factor

/-! ### Accounting of the finish-time receive (CE plan section 25) -/

/-- The labelled receive interface of the finish-time receive: chain-step KDF requests (left) and opening requests (right). -/
abbrev RequestSpec := RawCtxChainReceive.ReceiveSpec Slot Slot RatchetMaterial RawCtxWholeOwner.OpenContext
  RawCtxWholeOwner.Decrypted

/-- Receive calls that leave every KDF and opening request of the labelled receive as a query; the finish-time receive never sends. -/
noncomputable def requestCalls : RawCtxChainOwner.Calls Kernel (OracleComp RequestSpec) where
  receive entry target context := RawCtxChainReceive.execute entry target context
  send entry _ := pure (entry, none)

/-- The finish-time receive of a hidden finish on one raw input, from the hidden Beacon's initial local owner, with its requests left as queries. -/
noncomputable def finishRequests {Response : Type} (decode : RawCtxReceive.FrameDecoder)
    (prepared : PqxdhBeaconPhase2Preparation.Prepared Response) (value : Factor) (raw : Pqxdh.Bytes) :
    OracleComp RequestSpec (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxChainOwner.State Kernel Unit) :=
  (RawCtxChainOwner.rawReceive requestCalls decode raw).run
    (PqxdhServerAuthBeaconFactor.localState (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate)
      (PqxdhServerAuthBeaconFactor.initial value.2))

/-- The finish body runs the finish-time receive requests under the labelled primitive interpreter: every KDF request is answered by the selected chain step and every opening by one primitive call. -/
theorem factoredBody_requests {m : Type → Type} [Monad m] [LawfulMonad m] {Response : Type}
    (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (sendCall : Kernel → RawCtxSourceSend.SealContext → m (Kernel × Option RawCtxSourceSend.Encrypted))
    (source : FixedHkdfSha512NoSaltSource) (decode : RawCtxReceive.FrameDecoder)
    (prepared : PqxdhBeaconPhase2Preparation.Prepared Response) (value : Factor) (raw : Pqxdh.Bytes) :
    factoredBody prim sendCall source decode prepared value raw =
      (fun result => PqxdhBeaconPhase2Publication.afterOpening
          (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate) (resolve result.2.kernel) result.1) <$>
        simulateQ (PqxdhServerAuthBeaconFactor.primLabels prim source value.1)
          (finishRequests decode prepared value raw) := by
  simp only [factoredBody, finishRequests, RawCtxChainOwner.rawReceive, StateT.run]
  split
  · simp only [simulateQ_pure, map_pure, pure_bind]
  · split
    · simp only [simulateQ_pure, map_pure, pure_bind]
    · split
      · simp only [simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind, map_bind, map_pure, requestCalls,
          PqxdhServerAuthBeaconFactor.primCalls]
      · simp only [simulateQ_pure, map_pure, pure_bind]

/-- Owner ruling (CE plan section 25), receive level: on every raw input the finish-time receive of a hidden finish issues at most 51 chain-step KDF requests and at most one opening request. -/
theorem requests_bound {Response : Type} (decode : RawCtxReceive.FrameDecoder)
    (prepared : PqxdhBeaconPhase2Preparation.Prepared Response) (value : Factor) (raw : Pqxdh.Bytes) :
    (finishRequests decode prepared value raw).IsQueryBoundP (fun request => request.isLeft = true) 51 ∧
      (finishRequests decode prepared value raw).IsQueryBoundP (fun request => request.isRight = true) 1 := by
  simp only [finishRequests, RawCtxChainOwner.rawReceive, StateT.run]
  split
  · exact ⟨trivial, trivial⟩
  · split
    · exact ⟨trivial, trivial⟩
    · split
      · simp only [requestCalls, bind_pure_comp, isQueryBoundP_map_iff]
        exact ⟨RawCtxChainReceiveBounds.receive_bound _ _ _, RawCtxChainReceiveBounds.program_open_bound _⟩
      · exact ⟨trivial, trivial⟩

/-- The primitive interpreter with the real HKDF and the BLAKE2b opening left as a CTX-oracle query. -/
noncomputable def romPrim (c : Pqxdh.Crypto) :
    QueryImpl RawCtxWholeOwner.PrimitiveSpec (OracleComp CtxRomAuth.CtxRO)
  | .inl request => pure (RawCtxSourceHkdf.response c request)
  | .inr input => simulateQ (RawCtxSourceOpen.romAdapter c) (RawCtxSourceOpen.openInput input)

/-- The native primitive interpreter is the ROM-level interpreter with BLAKE2b answered by the lazily sampled CTX cache. -/
theorem nativePrim_rom {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (query : RawCtxWholeOwner.PrimitiveSpec.Domain) :
    PqxdhServerAuthBeaconFactor.nativePrim setup codec query =
      ctxLens.lift (simulateQ CtxRomAuth.ctxRandomOracle (romPrim setup.source.crypto query)) := by
  rcases query with request | input
  · rw [PqxdhServerAuthBeaconFactor.native_kdf]
    apply StateT.ext
    rintro ⟨auxiliary, cache⟩
    simp only [romPrim, simulateQ_pure, StateT.run_pure]
    rfl
  · exact PqxdhDeploymentHiddenKernels.nativePrim_open setup codec input

/-- A primitive opening makes at most one BLAKE2b query. -/
theorem opening_hash_bound (c : Pqxdh.Crypto) (input : RawCtxWholeOwner.OpenInput) :
    (romPrim c (.inr input)).IsTotalQueryBound 1 := by
  simp only [romPrim, RawCtxSourceOpen.openInput]
  split
  · exact trivial
  · split
    · rw [RawCtxSourceOpen.openSlices_rom, isTotalQueryBound_query_bind_iff]
      exact ⟨Nat.one_pos, fun _ => trivial⟩
    · exact trivial

/-- A simulation whose source makes at most `n` queries satisfying `p`, each implemented with at most one query, and whose other queries are implemented without queries, makes at most `n` queries. -/
theorem simulateQ_total_of_boundP {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {α : Type}
    (impl : QueryImpl spec₁ (OracleComp spec₂)) (p : ι₁ → Prop) [DecidablePred p]
    (costly : ∀ t, p t → (impl t).IsTotalQueryBound 1) (free : ∀ t, ¬ p t → (impl t).IsTotalQueryBound 0)
    (oa : OracleComp spec₁ α) (n : ℕ) (bound : oa.IsQueryBoundP p n) :
    (simulateQ impl oa).IsTotalQueryBound n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => simp only [simulateQ_pure]; exact trivial
  | query_bind t next ih =>
      rw [isQueryBoundP_query_bind_iff] at bound
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
      by_cases ht : p t
      · have positive : 0 < n := bound.1.resolve_left (not_not.mpr ht)
        have rest : ∀ u, (simulateQ impl (next u)).IsTotalQueryBound (n - 1) := fun u => ih u (n - 1) (by
          simpa only [ht, ite_true] using bound.2 u)
        simpa only [Nat.add_sub_cancel' positive] using isTotalQueryBound_bind (costly t ht) rest
      · have rest : ∀ u, (simulateQ impl (next u)).IsTotalQueryBound n := fun u => ih u n (by
          simpa only [ht, ite_false] using bound.2 u)
        simpa only [Nat.zero_add] using isTotalQueryBound_bind (free t ht) rest

/-- A query bound of a bind bounds its prefix. -/
theorem isQueryBoundP_of_bind_left {ι₀ : Type} {spec₀ : OracleSpec ι₀} {α β : Type} {p : ι₀ → Prop}
    [DecidablePred p] {oa : OracleComp spec₀ α} {ob : α → OracleComp spec₀ β} {n : ℕ}
    (bound : (oa >>= ob).IsQueryBoundP p n) : oa.IsQueryBoundP p n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => exact trivial
  | query_bind t next ih =>
      rw [bind_assoc, isQueryBoundP_query_bind_iff] at bound
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨bound.1, fun u => ih u (bound.2 u)⟩

section Hash
variable {Response : Type}

/-- Owner ruling (CE plan section 25), BLAKE2b: with the real HKDF and the BLAKE2b opening as a CTX-oracle query, a hidden finish makes at most one BLAKE2b query on every application reply and every path. -/
theorem finish_hash_bound (c : Pqxdh.Crypto)
    (sendCall : Kernel → RawCtxSourceSend.SealContext →
      OracleComp CtxRomAuth.CtxRO (Kernel × Option RawCtxSourceSend.Encrypted))
    (source : FixedHkdfSha512NoSaltSource) (application : Response → OracleComp CtxRomAuth.CtxRO (Option Pqxdh.Bytes))
    (silent : ∀ response, (application response).IsTotalQueryBound 0) (decode : RawCtxReceive.FrameDecoder)
    (prepared : PqxdhBeaconPhase2Preparation.Prepared Response) (value : Factor) :
    (PqxdhServerAuthBeaconFactor.factored (romPrim c) sendCall source application decode prepared value).IsTotalQueryBound 1 := by
  rw [PqxdhDeploymentHiddenKernels.factored_body]
  refine (isTotalQueryBound_bind (n₂ := 1) (silent prepared.response) (fun raw => ?_)).mono (by omega)
  cases raw with
  | none => exact trivial
  | some raw =>
      dsimp only
      rw [factoredBody_requests]
      refine (isQueryBound_map_iff _ _ _ _ _).2 ?_
      refine simulateQ_total_of_boundP _ (fun request => request.isRight = true) (fun request costly => ?_)
        (fun request free => ?_) _ 1 (requests_bound decode prepared value raw).2
      · rcases request with slot | opening
        · simp at costly
        · simp only [PqxdhServerAuthBeaconFactor.primLabels, QueryImpl.apply_compose, RawCtxWholeOwner.adapter]
          split
          · exact trivial
          · simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
            refine isTotalQueryBound_bind (n₁ := 1) (n₂ := 0) (opening_hash_bound c _) (fun _ => ?_)
            exact trivial
      · rcases request with slot | opening
        · exact trivial
        · simp at free

/-- The finish-time receive accounting of the owner ruling (CE plan section 25), per candidate receive of a hidden finish: at most 51 chain-step KDF requests, at most one opening request and, with the BLAKE2b opening as a CTX-oracle query, at most one BLAKE2b query. -/
theorem finish_accounting (c : Pqxdh.Crypto) (source : FixedHkdfSha512NoSaltSource) (application : Response → Option Pqxdh.Bytes)
    (decode : RawCtxReceive.FrameDecoder) (prepared : PqxdhBeaconPhase2Preparation.Prepared Response)
    (value : Factor) (raw : Pqxdh.Bytes) :
    (finishRequests decode prepared value raw).IsQueryBoundP (fun request => request.isLeft = true) 51 ∧
      (finishRequests decode prepared value raw).IsQueryBoundP (fun request => request.isRight = true) 1 ∧
        (PqxdhServerAuthBeaconFactor.factored (romPrim c) (fun entry _ => pure (entry, none)) source
          (fun response => pure (application response)) decode prepared value).IsTotalQueryBound 1 :=
  ⟨(requests_bound decode prepared value raw).1, (requests_bound decode prepared value raw).2,
    finish_hash_bound c _ source (fun response => pure (application response)) (fun _ => trivial) decode prepared value⟩

end Hash

section Erased
variable {Response : Type}

/-- Under any primitive interpreter that counts queries, the erased hidden finish issues no more queries of any kind than the factor-form hidden finish. -/
theorem erased_le {ι₀ : Type} {spec₀ : OracleSpec ι₀} (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec (OracleComp spec₀))
    (sendCall : Kernel → RawCtxSourceSend.SealContext → OracleComp spec₀ (Kernel × Option RawCtxSourceSend.Encrypted))
    (source : FixedHkdfSha512NoSaltSource) (application : Response → OracleComp spec₀ (Option Pqxdh.Bytes))
    (decode : RawCtxReceive.FrameDecoder) (prepared : PqxdhBeaconPhase2Preparation.Prepared Response)
    (value : Factor) (p : ι₀ → Prop) [DecidablePred p] (n : ℕ)
    (bound : (PqxdhServerAuthBeaconFactor.factored prim sendCall source application decode prepared value).IsQueryBoundP p n) :
    (Prod.fst <$> finishErased prim sendCall source application decode prepared value).IsQueryBoundP p n := by
  rw [isQueryBoundP_map_iff]
  rw [PqxdhDeploymentHiddenKernels.finish_erase_local] at bound
  exact isQueryBoundP_of_bind_left bound

/-- The total-count form of `erased_le`. -/
theorem erased_total_le {ι₀ : Type} {spec₀ : OracleSpec ι₀}
    (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec (OracleComp spec₀))
    (sendCall : Kernel → RawCtxSourceSend.SealContext → OracleComp spec₀ (Kernel × Option RawCtxSourceSend.Encrypted))
    (source : FixedHkdfSha512NoSaltSource) (application : Response → OracleComp spec₀ (Option Pqxdh.Bytes))
    (decode : RawCtxReceive.FrameDecoder) (prepared : PqxdhBeaconPhase2Preparation.Prepared Response)
    (value : Factor) (n : ℕ)
    (bound : (PqxdhServerAuthBeaconFactor.factored prim sendCall source application decode prepared value).IsTotalQueryBound n) :
    (Prod.fst <$> finishErased prim sendCall source application decode prepared value).IsTotalQueryBound n := by
  rw [PqxdhDeploymentHiddenKernels.finish_erase_local] at bound
  exact (isQueryBound_map_iff _ _ _ _ _).2 (IsTotalQueryBound.of_bind_left bound)

/-- On a raw input whose decoded sequence is not one, the erased hidden finish calls no primitive at all, in any monad: it rejects and reports the discarded opening input. -/
theorem erased_reject {m : Type → Type} [Monad m] [LawfulMonad m] (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (sendCall : Kernel → RawCtxSourceSend.SealContext → m (Kernel × Option RawCtxSourceSend.Encrypted))
    (source : FixedHkdfSha512NoSaltSource) (decode : RawCtxReceive.FrameDecoder)
    (prepared : PqxdhBeaconPhase2Preparation.Prepared Response) (value : Factor) (raw : Pqxdh.Bytes)
    (notOne : SeqOne decode raw = false) :
    finishErased prim sendCall source (fun _ => pure (some raw)) decode prepared value =
      pure (none, discardedInput source decode prepared value raw) := by
  simp only [finishErased, pure_bind, notOne, Bool.false_eq_true, ite_false]

end Erased

/-- With the native primitives, the erased hidden finish on an application reply whose decoded sequence is not one leaves the shared state, including the CTX cache, unchanged. -/
theorem finishErasedSvc_reject {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (m : Material) (seed : PqxdhRecordLiftSeed.Seed)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (raw : Pqxdh.Bytes)
    (fetched : codec.application (PqxdhPhase2DhRootConsumer.cleared pending).response = some raw)
    (notOne : SeqOne codec.frameRead raw = false) :
    finishErasedSvc setup codec m seed pending = pure none := by
  simp only [finishErasedSvc, finishPointed, finishErased, fetched, pure_bind, notOne, Bool.false_eq_true,
    ite_false, map_pure]

end BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.buildFactor_services' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.buildFactor_services

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.finishFactor_services' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.finishFactor_services

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.finishFactor_pointed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.finishFactor_pointed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.erasedSvc_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.erasedSvc_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.openingImpl_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.openingImpl_hash

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.nativeImpl_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.nativeImpl_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.compose_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.compose_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.registrationImpl_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.registrationImpl_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.tailAux_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.tailAux_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.nativeTail_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.nativeTail_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.tailImpl_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.tailImpl_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.continueRust_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.continueRust_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.afterInitialization_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.afterInitialization_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.candidate_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.candidate_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.genericBuild_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.genericBuild_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.buildFactor_commutes_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.buildFactor_commutes_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.finishFactor_commutes_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.finishFactor_commutes_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.finishErased_commutes_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.finishErased_commutes_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.finishPointed_commutes_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.finishPointed_commutes_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.factoredBody_requests' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.factoredBody_requests

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.requests_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.requests_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.nativePrim_rom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.nativePrim_rom

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.opening_hash_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.opening_hash_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.simulateQ_total_of_boundP' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.simulateQ_total_of_boundP

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.isQueryBoundP_of_bind_left' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.isQueryBoundP_of_bind_left

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.finish_hash_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.finish_hash_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.finish_accounting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.finish_accounting

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.erased_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.erased_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.erased_total_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.erased_total_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.erased_reject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.erased_reject

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.finishErasedSvc_reject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry.finishErasedSvc_reject
