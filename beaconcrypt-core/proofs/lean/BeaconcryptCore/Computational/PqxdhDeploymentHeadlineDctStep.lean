-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctCommit
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace

/-!
# CE-12 D-ct: the per-command step facts of the split handler

Every command of the split handler (`PqxdhDeploymentBackend.handlerWith … (PqxdhDeploymentIdealDefer.idealSplit t p)`) keeps every entry of the R1 table and of the BLAKE2b cache, every cached slot material and every allocated slot, and moves the ideal backend only as the selected accept, the marked build and owner k's challenge finish allow (`step_facts`). These are the frame facts of the D-ct invariant (`PqxdhDeploymentHeadlineDctInvariant`, design section 4.4; they replace the design's `Grows`, `step_grows` and `mark_fresh` and add the early-phase session facts of design risk 3).

- Native growth. `NGrows s s'`: the R1 table and the CTX cache of the native shared state only gain entries. `GrowsW work`: every run of a native program grows the state. It is closed under `pure` and `bind` and holds for coins, local state steps that keep the CTX cache, CTX programs that grow their cache, the BLAKE2b oracle, the root callbacks (`growsW_sourceRoot`, `growsW_romRootBytes`) and the route-R1 Extract family (`romImpl_grows`: a lazily sampled table read or a real HMAC evaluation). The CTX cache grows under the shared record primitives (`sharedImpl_grows`, `sharedNative_grows`, `run_ctx_grows`), the Server's response tail (`nativeTail_grows`, `tailImpl_grows`, `tailRun_grows`) and the Beacon's opening primitives (`nativePrim_grows`, `beaconLabels_grows`, `chainRaw_grows`).
- The native commands: the raw accept (`client_grows`, `accept_grows`), the build (`build_grows`), the public HMAC (`familyHmac_grows`, `hmac_grows`), the Beacon finish (`beaconNative_grows`, `callbacks_growsW`, `run_callbacks_growsW`, `finish_grows`, `onShared_grows`), the record steps (`serverStep_grows`, `beaconStep_grows`) and every query of the native deployment handler (`nativeHandler_grows`). The hidden steps: the marked build at any value (`buildHidden_grows`), owner k's challenge finish (`finishErased_grows`, `hiddenAfter_grows`, `groupCE_grows`, `slotRun_nGrows`, `finishChallenge_grows`) and the selected accept (`tailCE_grows`, `opaqueTail_grows`: the marker tail installs the accept's own game state first; `acceptActive_grows`, `acceptInactive_grows`, `acceptExposed_grows`); the selected accept marks only its own session index, the session counter before the call (`tailCE_mark`, `acceptExposed_mark`).
- The slot state. `SlotGrows`: the allocator and the material cache only gain entries, the counter does not decrease and a full allocator is kept (`slotLazy_grows`, `slotRun_grows`, `slotRunX_facts`).
- Step facts. `ProgFacts` for the slot programs of the ideal registration (`progFacts_quiet`, `realQuiet_facts`, `createProg_facts`, `acceptProg_facts`, `realBuild_facts`, `buildProg_facts`, `finishProg_facts`) and `StepFacts` for the split handler (`stepFacts_refl`, `stepFacts_quiet`, `stepFacts_slot`, `serverInstall_core`, `beaconInstall_core`, `step_facts`): the native shared state and the slot state grow; the accept counter does not decrease; the mark changes only at the selected ordinal, and a new mark is at the session counter before the step; and up to the selected ordinal, with no mark and an inactive selected accept, a step sets no mark, keeps the selected accept inactive, does not lower the session counter and adds pending tokens only below the new counter (the native footprints `PqxdhDeploymentHeadlineCtTrace.nativeAccept_footprint`, `nativeBuild_footprint`, `native_kept`, and `PqxdhRegistrationSchedule.owner_fields`).

Support facts only; no assumption is used.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhDeploymentBackend (XState)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-! ### Growth of the native shared state -/

section Native

/-- The R1 table and the CTX cache only gain entries. -/
def NGrows (before after : NativeState KemSK) : Prop :=
  (∀ u v, before.1.cache u = some v → after.1.cache u = some v) ∧
    ∀ i d, before.2.ctx i = some d → after.2.ctx i = some d

theorem nGrows_refl (state : NativeState KemSK) : NGrows state state :=
  ⟨fun _ _ found => found, fun _ _ found => found⟩

theorem nGrows_trans {first second third : NativeState KemSK} (one : NGrows first second)
    (two : NGrows second third) : NGrows first third :=
  ⟨fun u v found => two.1 u v (one.1 u v found), fun i d found => two.2 i d (one.2 i d found)⟩

/-- Every run of a native program grows the native shared state. -/
def GrowsW {α : Type} (work : NativeGame KemSK α) : Prop :=
  ∀ state, ∀ result ∈ support (work.run state), NGrows state result.2

theorem growsW_pure {α : Type} (value : α) : GrowsW (pure value : NativeGame KemSK α) := by
  intro state result member
  rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
  subst member
  exact nGrows_refl state

theorem growsW_bind {α β : Type} {work : NativeGame KemSK α} {next : α → NativeGame KemSK β}
    (first : GrowsW work) (rest : ∀ value, GrowsW (next value)) : GrowsW (work >>= next) := by
  intro state result member
  rw [StateT.run_bind, mem_support_bind_iff] at member
  obtain ⟨middle, middleMember, resultMember⟩ := member
  exact nGrows_trans (first state middle middleMember) (rest middle.1 middle.2 result resultMember)

theorem growsW_coins {α : Type} (work : ProbComp α) : GrowsW (PqxdhServerAuthNative.nativeCoins (KemSK := KemSK) work) := by
  intro state result member
  change result ∈ support ((fun value => (value, state)) <$> work) at member
  rw [support_map] at member
  obtain ⟨_, _, rfl⟩ := member
  exact nGrows_refl state

theorem growsW_local {α : Type} (step : PqxdhServerAuthExperiment.GameState KemSK → α × PqxdhServerAuthExperiment.GameState KemSK)
    (keeps : ∀ game, (step game).2.ctx = game.ctx) : GrowsW (PqxdhServerAuthNative.localState step) := by
  intro state result member
  change result ∈ support (pure ((step state.2).1, (state.1, (step state.2).2)) : ProbComp _) at member
  rw [support_pure, Set.mem_singleton_iff] at member
  subst member
  exact ⟨fun _ _ found => found, fun i d found => by rw [keeps]; exact found⟩

theorem growsW_ctx {α : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α)
    (grows : ∀ cache, ∀ result ∈ support (work.run ((), cache)), ∀ i d, cache i = some d → result.2.2 i = some d) :
    GrowsW (PqxdhServerAuthNative.nativeCtx (KemSK := KemSK) work) := by
  intro state result member
  change result ∈ support ((fun r => (r.1, (state.1, { state.2 with ctx := r.2.2 }))) <$>
    work.run ((), state.2.ctx)) at member
  rw [support_map] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  exact ⟨fun _ _ found => found, grows state.2.ctx inner innerMember⟩

theorem growsW_hash (bytes : Pqxdh.Bytes) : GrowsW (PqxdhServerAuthNative.nativeHash (KemSK := KemSK) bytes) := by
  intro state result member
  change result ∈ support ((fun r => (r.1, (state.1, { state.2 with ctx := r.2 }))) <$>
    (CtxRomAuth.ctxRandomOracle ((), bytes)).run state.2.ctx) at member
  rw [support_map] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  exact ⟨fun _ _ found => found, fun i d found =>
    PqxdhRecordFactsBindingEvidence.hash_grows _ _ inner innerMember found⟩

theorem growsW_sourceRoot (hmac : PqxdhSecretInputKdf.HmacSha512) (input : beaconcrypt_core.pqxdh.RootKeyInput) :
    GrowsW (PqxdhServerAuthNative.sourceRoot (KemSK := KemSK) hmac input) := by
  intro state result member
  obtain ⟨grown, same, -⟩ := PqxdhDeploymentHeadlineDctFinish.sourceRoot_read hmac input state result member
  exact ⟨grown, fun i d found => by rw [same]; exact found⟩

theorem growsW_romRootBytes (hmac : PqxdhSecretInputKdf.HmacSha512) (message : PqxdhJointDhExtractFamily.Message)
    (bytes : Pqxdh.Bytes) :
    GrowsW (PqxdhServerAuthNative.romRootBytes (A := PqxdhServerAuthExperiment.GameState KemSK) hmac message bytes) := by
  intro state result member
  change result ∈ support ((fun r : PqxdhSecretInputKdf.HmacBlock × PqxdhSecretInputKdf.HmacOracle.QueryCache =>
    (PqxdhSecretInputKdf.expandRoot hmac r.1,
      ((⟨state.1.history ++ [.derive message (some r.1),
          .publicHmac r.1 PqxdhSecretInputKdf.rootExpandInput (hmac.eval r.1 PqxdhSecretInputKdf.rootExpandInput)],
        r.2⟩ : PqxdhJointDhExtractFamily.State), state.2))) <$>
    (PqxdhSecretInputKdf.HmacOracle.randomOracle bytes).run state.1.cache) at member
  rw [support_map] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  exact ⟨fun u v found => QueryImpl.withCaching_cache_le _ _ _ _ innerMember found, fun _ _ found => found⟩

/-- Every request of the route-R1 Extract family keeps or extends the table cache. -/
theorem romImpl_grows (hmac : PqxdhSecretInputKdf.HmacSha512) (joint : PqxdhJointIdentity.Primitives)
    (dh : PqxdhJointGapDh.DhInterface joint) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (query : PqxdhJointDhExtractFamily.Spec.Domain)
    (state : PqxdhJointDhExtractFamily.State) :
    ∀ result ∈ support ((PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar query).run state),
      ∀ u v, state.cache u = some v → result.2.cache u = some v := by
  intro result member u v found
  rcases query with coin | request
  · simp only [PqxdhExtractRomFamily.romImpl, StateT.run, support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff] at member
    obtain ⟨_, _, rfl⟩ := member
    exact found
  · cases request with
    | sign message =>
        simp only [PqxdhExtractRomFamily.romImpl, StateT.run, support_pure, Set.mem_singleton_iff] at member
        subst member
        exact found
    | publicHmac key message =>
        simp only [PqxdhExtractRomFamily.romImpl, StateT.run] at member
        split_ifs at member
        · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at member
          obtain ⟨inner, innerMember, rfl⟩ := member
          exact QueryImpl.withCaching_cache_le _ _ _ _ innerMember found
        · rw [support_pure, Set.mem_singleton_iff] at member
          subst member
          exact found
    | derive message =>
        simp only [PqxdhExtractRomFamily.romImpl, StateT.run] at member
        split at member
        · rw [support_pure, Set.mem_singleton_iff] at member
          subst member
          exact found
        · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at member
          obtain ⟨inner, innerMember, rfl⟩ := member
          exact QueryImpl.withCaching_cache_le _ _ _ _ innerMember found

end Native

/-! ### Growth of the CTX cache under the record primitives -/

section Ctx
variable {A : Type}

/-- A whole simulation keeps or extends the CTX cache when every request does. -/
theorem run_ctx_grows {κ α : Type} {spec : OracleSpec κ}
    (impl : QueryImpl spec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (step : ∀ query state, ∀ result ∈ support ((impl query).run state), state.2 ≤ result.2.2)
    (program : OracleComp spec α) (state : RawCtxSharedPrimitive.SharedState A) :
    ∀ result ∈ support ((simulateQ impl program).run state), state.2 ≤ result.2.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query impl (fun current => state.2 ≤ current.2)
    (fun query current held result member => le_trans held (step query current result member)) program state
    le_rfl

/-- Every request of the shared native record primitives keeps or extends the CTX cache. -/
theorem sharedImpl_grows (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (query : RawCtxMixedOwner.NativeSpec.Domain)
    (before : RawCtxSharedPrimitive.SharedState A)
    (result : RawCtxMixedOwner.NativeSpec.Range query × RawCtxSharedPrimitive.SharedState A)
    (supported : result ∈ support ((RawCtxMixedShared.sharedImpl c writer (RawCtxSourceHkdf.kdfImpl source)
      query).run before)) :
    before.2 ≤ result.2.2 := by
  rcases query with request | (sealing | (opening | (bytes | frame)))
  all_goals simp only [RawCtxMixedShared.sharedImpl, QueryImpl.compose, RawCtxMixedShared.sharedAdapter,
    simulateQ_pure, simulateQ_spec_query, RawCtxSharedPrimitive.nativeImpl, RawCtxSharedPrimitive.openingImpl,
    RawCtxSourceHkdf.kdfImpl, StateT.run, support_pure, Set.mem_singleton_iff, bind_pure_comp, support_map] at supported
  all_goals first | change result ∈ support (pure (_, before) : ProbComp _) at supported | skip
  case inr.inr.inr.inl =>
    obtain ⟨hashed, reached, rfl⟩ := supported
    exact PqxdhRecordFactsBindingEvidence.hash_grows ((), bytes) before.2 hashed reached
  all_goals simpa only [support_pure, Set.mem_singleton_iff] using supported ▸ (le_refl before.2)

/-- Every request of the Server's native response tail keeps or extends the CTX cache. -/
theorem nativeTail_grows {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (query : PqxdhServerRegistrationPublication.TailSpec.Domain) (before : RawCtxSharedPrimitive.SharedState A) :
    ∀ result ∈ support ((PqxdhServerAuthExperiment.nativeTail (A := A) setup codec checks query).run before),
      before.2 ≤ result.2.2 := by
  refine run_ctx_grows _ (fun request state result member => ?_) _ before
  rcases request with request | request
  · change result ∈ support ((simulateQ (RawCtxMixedShared.sharedImpl setup.source.crypto codec.frameWrite
      (RawCtxSourceHkdf.kdfImpl setup.source)) (RawCtxMixedOwner.sendLift request)).run state) at member
    exact run_ctx_grows _ (fun query state result member =>
      sharedImpl_grows setup.source.crypto codec.frameWrite setup.source query state result member) _ state result member
  · change result ∈ support ((PqxdhServerAuthExperiment.tailAux codec checks request).run state) at member
    cases request <;>
    · simp only [PqxdhServerAuthExperiment.tailAux, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact le_rfl

end Ctx

section Tail
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- Every request of the Server's logging tail keeps or extends the CTX cache. -/
theorem tailImpl_grows (query : PqxdhServerRegistrationPublication.TailSpec.Domain)
    (before : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    ∀ result ∈ support ((PqxdhServerAuthExperiment.tailImpl setup codec checks query).run before),
      before.2 ≤ result.2.2 := by
  intro result member
  rcases query with (request | input) | request
  · exact nativeTail_grows setup codec checks _ before result member
  · change result ∈ support ((do
      let sealed ← PqxdhServerAuthExperiment.nativeTail setup codec checks (.inl (.inr input))
      if sealed.isSome then modify fun state => (state.1 ++ [input.context], state.2)
      pure sealed).run before) at member
    rw [StateT.run_bind, mem_support_bind_iff] at member
    obtain ⟨sealed, sealedMember, member⟩ := member
    have grown := nativeTail_grows setup codec checks _ before sealed sealedMember
    split_ifs at member
    · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at member
      subst member
      exact grown
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact grown
  · exact nativeTail_grows setup codec checks _ before result member

/-- A whole program on the Server's logging tail keeps or extends the CTX cache. -/
theorem tailRun_grows {α : Type} (program : OracleComp PqxdhServerRegistrationPublication.TailSpec α)
    (before : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    ∀ result ∈ support ((simulateQ (PqxdhServerAuthExperiment.tailImpl setup codec checks) program).run before),
      before.2 ≤ result.2.2 :=
  run_ctx_grows _ (tailImpl_grows setup codec checks) program before

/-- The native build grows the native shared state. -/
theorem build_grows (session : ℕ) (payload : Option Pqxdh.Bytes) :
    GrowsW (PqxdhServerAuthNative.nativeBuild setup codec checks session payload) := by
  intro state result member
  unfold PqxdhServerAuthNative.nativeBuild at member
  rw [PqxdhDeploymentBackend.nativeGet_bind] at member
  split at member
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact nGrows_refl state
  · rw [PqxdhDeploymentBackend.nativeCoins_bind, mem_support_bind_iff] at member
    obtain ⟨built, builtMember, member⟩ := member
    simp only [PqxdhServerAuthNative.nativeSet, StateT.run] at member
    subst member
    exact ⟨fun _ _ found => found, fun i d found => tailRun_grows setup codec checks _ _ built builtMember found⟩

/-- The marked build with the erased hidden services at any value grows the native shared state. -/
theorem buildHidden_grows (value : PqxdhServerAuthKeySchedule.Output) (session : ℕ) (payload : Option Pqxdh.Bytes) :
    GrowsW (PqxdhDeploymentIdealSteps.buildHidden (KemSK := KemSK)
      (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks value) session payload) := by
  intro state result member
  unfold PqxdhDeploymentIdealSteps.buildHidden at member
  rw [PqxdhDeploymentBackend.nativeGet_bind] at member
  split at member
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact nGrows_refl state
  · rename_i token _
    rw [PqxdhDeploymentBackend.nativeCoins_bind, mem_support_bind_iff] at member
    obtain ⟨built, builtMember, member⟩ := member
    simp only [PqxdhServerAuthNative.nativeSet, StateT.run] at member
    subst member
    change built ∈ support ((PqxdhServerAuthLoggedSendFactor.factored (fun entry _ _ => pure (entry, .None))
      (fun request => PqxdhServerAuthExperiment.tailImpl setup codec checks (.inl request)) setup.source
      (fun request => PqxdhServerAuthExperiment.tailImpl setup codec checks (.inr request))
      (PqxdhServerAuthCtxMaterial.factor value) token.pending payload () state.2.server).run ([], state.2.ctx))
      at builtMember
    rw [PqxdhDeploymentSplitFactor.factored_free] at builtMember
    exact ⟨fun _ _ found => found, fun i d found => tailRun_grows setup codec checks _ _ built builtMember found⟩

end Tail

/-! ### The native commands -/

section Commands
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- The accept core's root derivation grows the native shared state. -/
theorem client_grows (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (control : beaconcrypt_core.pqxdh.ServerState) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes PqxdhBeaconPhase2Preparation.Word32) :
    GrowsW (PqxdhServerAuthNative.nativeClient (KemSK := KemSK) hmac index control binding input) := by
  unfold PqxdhServerAuthNative.nativeClient
  split
  · exact growsW_pure _
  · exact growsW_pure _
  · exact growsW_pure _
  · refine growsW_bind ?_ fun _ => growsW_bind (growsW_local _ fun _ => rfl) fun _ => growsW_pure _
    unfold PqxdhServerAuthNative.loggedRoot PqxdhServerAuthNative.romRoot
    exact growsW_bind (growsW_romRootBytes _ _ _) fun _ => growsW_bind (growsW_local _ fun _ => rfl) fun _ =>
      growsW_pure _

/-- The native raw accept grows the native shared state. -/
theorem accept_grows (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (raw : Pqxdh.Bytes) : GrowsW (PqxdhServerAuthNative.nativeAccept setup codec checks seed scalar raw) := by
  intro state result member
  unfold PqxdhServerAuthNative.nativeAccept at member
  rw [PqxdhDeploymentBackend.nativeGet_bind, PqxdhDeploymentBackend.nativeCoins_bind, mem_support_bind_iff] at member
  obtain ⟨collected, _, member⟩ := member
  rw [PqxdhDeploymentBackend.nativeSet_run_bind] at member
  split at member
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨fun _ _ found => found, fun _ _ found => found⟩
  · rw [StateT.run_bind, mem_support_bind_iff] at member
    obtain ⟨returned, returnedMember, member⟩ := member
    have one := client_grows _ _ _ _ _ _ returned returnedMember
    split at member
    · have two := growsW_bind (growsW_local _ fun _ => rfl) (fun _ => growsW_pure _) _ result member
      exact nGrows_trans (nGrows_trans ⟨fun _ _ found => found, fun _ _ found => found⟩ one) two
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact nGrows_trans ⟨fun _ _ found => found, fun _ _ found => found⟩ one

/-- The route-R1 public HMAC request of the native state grows it. -/
theorem familyHmac_grows (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) :
    GrowsW (PqxdhServerRelatedRootConsumer.familyImpl (A := PqxdhServerAuthExperiment.GameState KemSK)
      (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction)
      (.inr (.publicHmac key message))) := by
  intro state result member
  change result ∈ support ((fun r => (r.1, (r.2, state.2))) <$> ((PqxdhExtractRomFamily.romImpl setup.hmac setup.joint
    setup.dh seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction) (.inr (.publicHmac key message))).run state.1)
    at member
  rw [support_map] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  simp only [QueryImpl.apply_compose, PqxdhJointDhExtractRoot.reduction, simulateQ_spec_query] at innerMember
  refine ⟨fun u v found => ?_, fun _ _ found => found⟩
  exact romImpl_grows setup.hmac setup.joint setup.dh seed scalar (.inr (.publicHmac key message)) state.1 inner
    innerMember u v found

/-- The native public HMAC grows the native shared state. -/
theorem hmac_grows (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) :
    GrowsW (PqxdhServerAuthNative.nativeHmac setup seed scalar key message) := by
  unfold PqxdhServerAuthNative.nativeHmac
  split_ifs
  · exact growsW_bind (growsW_local _ fun _ => rfl) fun _ => familyHmac_grows setup seed scalar key message
  · exact familyHmac_grows setup seed scalar key message

/-- The Beacon's native tail primitives keep or extend the CTX cache. -/
theorem beaconNative_grows (query : (PqxdhBeaconPhase2Publication.NativeTailSpec Response).Domain)
    (before : RawCtxSharedPrimitive.SharedState Unit) :
    ∀ result ∈ support ((PqxdhServerAuthExperiment.beaconNative setup codec query).run before),
      before.2 ≤ result.2.2 := by
  intro result member
  rcases query with query | (input | request | response)
  · rcases query with request | (bytes | input)
    · simp only [PqxdhServerAuthExperiment.beaconNative, RawCtxSharedPrimitive.nativeImpl, RawCtxSourceHkdf.kdfImpl,
        StateT.run] at member
      change result ∈ support (pure (_, before) : ProbComp _) at member
      rw [support_pure, Set.mem_singleton_iff] at member
      subst member
      exact le_rfl
    · simp only [PqxdhServerAuthExperiment.beaconNative, RawCtxSharedPrimitive.nativeImpl,
        RawCtxSharedPrimitive.openingImpl, StateT.run, bind_pure_comp, support_map] at member
      obtain ⟨hashed, reached, rfl⟩ := member
      exact PqxdhRecordFactsBindingEvidence.hash_grows ((), bytes) before.2 hashed reached
    · simp only [PqxdhServerAuthExperiment.beaconNative, RawCtxSharedPrimitive.nativeImpl,
        RawCtxSharedPrimitive.openingImpl, StateT.run, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact le_rfl
  all_goals
    simp only [PqxdhServerAuthExperiment.beaconNative, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact le_rfl

/-- Every native callback of the Beacon finish grows the native shared state. -/
theorem callbacks_growsW (query : (PqxdhBeaconPhase2Publication.NativeSpec PqxdhJointIdentity.IdentitySeed
      PqxdhJointGapDh.ScalarBytes (PqxdhKemIndCca.MlKem768PublicKey × KemSK) PqxdhJointIdentity.IdentitySeed
      Response).Domain) :
    GrowsW (PqxdhRegistrationSchedule.callbacks setup codec query) := by
  rcases query with query | query
  · exact growsW_coins _
  · rcases query with query | (input | request | response)
    · exact growsW_ctx _ fun cache result member => beaconNative_grows setup codec (.inl query) ((), cache) result member
    · exact growsW_sourceRoot setup.hmac input
    · exact growsW_ctx _ fun cache result member =>
        beaconNative_grows setup codec (.inr (.initial request)) ((), cache) result member
    · exact growsW_ctx _ fun cache result member =>
        beaconNative_grows setup codec (.inr (.application response)) ((), cache) result member

/-- A whole program on the native callbacks of the Beacon finish grows the native shared state. -/
theorem run_callbacks_growsW {α : Type}
    (program : OracleComp (PqxdhBeaconPhase2Publication.NativeSpec PqxdhJointIdentity.IdentitySeed
      PqxdhJointGapDh.ScalarBytes (PqxdhKemIndCca.MlKem768PublicKey × KemSK) PqxdhJointIdentity.IdentitySeed
      Response) α) :
    GrowsW (simulateQ (PqxdhRegistrationSchedule.callbacks setup codec) program) := fun state =>
  OracleComp.simulateQ_run_preserves_inv_of_query (PqxdhRegistrationSchedule.callbacks setup codec)
    (fun after => NGrows state after)
    (fun query middle grown next member => nGrows_trans grown (callbacks_growsW setup codec query middle next member))
    program state (nGrows_refl state)

/-- The source schedule's finish grows the native shared state. -/
theorem finish_grows (index : ℕ) (raw : Pqxdh.Bytes) (state : PqxdhRegistrationSchedule.State KemSK) :
    ∀ result ∈ support ((PqxdhRegistrationSchedule.finish setup codec index raw).run state),
      NGrows state.shared result.2.shared := by
  intro result member
  cases found : state.owners[index]? with
  | none =>
      rw [PqxdhRegistrationSchedule.finish_missing setup codec index raw state found, support_pure,
        Set.mem_singleton_iff] at member
      subst member
      exact nGrows_refl _
  | some owner =>
      change result ∈ support (PqxdhRegistrationSchedule.finish setup codec index raw state) at member
      rw [PqxdhRegistrationSchedule.finish_source setup codec index raw state owner found, support_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      exact run_callbacks_growsW setup codec _ _ inner innerMember

/-- A native program lifted to the registration state grows its shared part when the program grows the native state. -/
theorem onShared_grows {α : Type} (work : NativeGame KemSK α) (grows : GrowsW work)
    (state : PqxdhRegistrationSchedule.State KemSK) :
    ∀ result ∈ support ((PqxdhRegistrationSchedule.onShared work).run state), NGrows state.shared result.2.shared := by
  intro result member
  change result ∈ support ((fun r => (r.1, { state with shared := r.2 })) <$> work state.shared) at member
  rw [support_map] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  exact grows state.shared inner innerMember

end Commands

/-! ### The slot state under the allocator in front of the lazy service -/

section Slots

/-- The allocator and the material cache only gain entries, the allocator's counter does not decrease, and a full allocator is kept. -/
def SlotGrows (before after : PqxdhRegistrationJointKemSecondEntry.Alloc PqxdhDeploymentIdealSlots.Coord 2 ×
    (PqxdhDeploymentIdealKernel.MatCache 2 × PqxdhDeploymentIdealKernel.SeedCache 2)) : Prop :=
  (∀ c j, before.1.1 c = some j → after.1.1 c = some j) ∧ before.1.2 ≤ after.1.2 ∧
    (2 ≤ before.1.2 → after.1.1 = before.1.1) ∧ ∀ j m, before.2.1 j = some m → after.2.1 j = some m

theorem slotGrows_refl (state : PqxdhRegistrationJointKemSecondEntry.Alloc PqxdhDeploymentIdealSlots.Coord 2 ×
    (PqxdhDeploymentIdealKernel.MatCache 2 × PqxdhDeploymentIdealKernel.SeedCache 2)) : SlotGrows state state :=
  ⟨fun _ _ found => found, le_rfl, fun _ => rfl, fun _ _ found => found⟩

theorem slotGrows_trans {first second third : PqxdhRegistrationJointKemSecondEntry.Alloc PqxdhDeploymentIdealSlots.Coord 2 ×
    (PqxdhDeploymentIdealKernel.MatCache 2 × PqxdhDeploymentIdealKernel.SeedCache 2)}
    (one : SlotGrows first second) (two : SlotGrows second third) : SlotGrows first third :=
  ⟨fun c j found => two.1 c j (one.1 c j found), le_trans one.2.1 two.2.1,
    fun full => (two.2.2.1 (le_trans full one.2.1)).trans (one.2.2.1 full),
    fun j m found => two.2.2.2 j m (one.2.2.2 j m found)⟩

/-- One request of the allocator in front of the lazy service grows the slot state. -/
theorem slotLazy_grows (query : PqxdhDeploymentIdealSlots.SlotSpec.Domain)
    (state : PqxdhRegistrationJointKemSecondEntry.Alloc PqxdhDeploymentIdealSlots.Coord 2 ×
      (PqxdhDeploymentIdealKernel.MatCache 2 × PqxdhDeploymentIdealKernel.SeedCache 2)) :
    ∀ r ∈ support ((PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentIdealKernel.lazyDummy query).run
      state), SlotGrows state r.2 := by
  intro r member
  rcases query with coin | point
  · rw [PqxdhRegistrationJointKemSecondEntry.slot_coin, support_map] at member
    obtain ⟨_, _, rfl⟩ := member
    exact slotGrows_refl state
  · rcases found : state.1.1 point with _ | slot
    · by_cases room : state.1.2 < 2
      · rw [PqxdhDeploymentIdealDefer.slotImpl_lazy_new point state found room, support_map] at member
        obtain ⟨inner, innerMember, rfl⟩ := member
        refine ⟨fun c j present => ?_, Nat.le_succ _, fun full => absurd room (by omega), fun j m present =>
          QueryImpl.withCaching_cache_le _ _ _ _ innerMember present⟩
        have ne : c ≠ point := by
          rintro rfl
          rw [found] at present
          cases present
        simpa only [Function.update_of_ne ne] using present
      · simp only [PqxdhRegistrationJointKemSecondEntry.slotImpl, QueryImpl.add_apply_inr, StateT.run_mk, found, room,
          _root_.dite_false, support_map] at member
        obtain ⟨answer, -, rfl⟩ := member
        exact slotGrows_refl state
    · rw [PqxdhDeploymentIdealDefer.slotImpl_lazy_found point state slot found, support_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      exact ⟨fun _ _ present => present, le_rfl, fun _ => rfl, fun j m present =>
        QueryImpl.withCaching_cache_le _ _ _ _ innerMember present⟩

/-- A whole slot client run through the allocator in front of the lazy service grows the slot state. -/
theorem slotRun_grows {α : Type} (work : OracleComp PqxdhDeploymentIdealSlots.SlotSpec α)
    (state : PqxdhRegistrationJointKemSecondEntry.Alloc PqxdhDeploymentIdealSlots.Coord 2 ×
      (PqxdhDeploymentIdealKernel.MatCache 2 × PqxdhDeploymentIdealKernel.SeedCache 2)) :
    ∀ r ∈ support ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentIdealKernel.lazyDummy)
      work).run state), SlotGrows state r.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query _ (fun after => SlotGrows state after)
    (fun query middle grown next member => slotGrows_trans grown (slotLazy_grows query middle next member))
    work state (slotGrows_refl state)

/-- A slot step run by `slotRunX` through the lazy service: its reply and deployment state are those of the slot step on the detached state, its ideal backend is the slot step's, and the slot state grows. -/
theorem slotRunX_facts {β : Type}
    (step : StateT (XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2) (OracleComp PqxdhDeploymentIdealSlots.SlotSpec) β)
    (x : XState KemSK PqxdhDeploymentIdealSteps.SplitBk 2) (result : β × XState KemSK PqxdhDeploymentIdealSteps.SplitBk 2)
    (member : result ∈ support ((PqxdhDeploymentIdealKernel.slotRunX PqxdhDeploymentIdealKernel.lazyDummy step).run x)) :
    ∃ inner, inner ∈ support (step.run (PqxdhDeploymentIdealKeys.detachX x)) ∧ result.1 = inner.1 ∧
      result.2.base = inner.2.base ∧ result.2.backend.2.2 = inner.2.backend ∧
      SlotGrows (x.backend.2.1, (x.backend.1, x.seeds)) (result.2.backend.2.1, (result.2.backend.1, result.2.seeds)) := by
  change result ∈ support ((fun r => (r.1, PqxdhDeploymentIdealKeys.attachX r.2.1 r.2.2.1 r.2.2.2)) <$>
    (PqxdhDeploymentIdealErase.onPair PqxdhDeploymentIdealKernel.lazyDummy step).run
      (PqxdhDeploymentIdealKeys.detachX x, (x.backend.2.1, (x.backend.1, x.seeds)))) at member
  rw [support_map] at member
  obtain ⟨paired, pairedMember, rfl⟩ := member
  rw [PqxdhDeploymentIdealErase.onPair_run, support_map] at pairedMember
  obtain ⟨simulated, simulatedMember, rfl⟩ := pairedMember
  refine ⟨simulated.1, ?_, rfl, rfl, rfl, slotRun_grows _ _ simulated simulatedMember⟩
  apply OracleComp.support_simulateQ_run'_subset
    (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentIdealKernel.lazyDummy)
    (step.run (PqxdhDeploymentIdealKeys.detachX x)) (x.backend.2.1, (x.backend.1, x.seeds))
  rw [StateT.run'_eq, support_map]
  exact ⟨simulated, simulatedMember, rfl⟩

end Slots

/-! ### The Beacon's opening primitives and the hidden finish -/

section Opening
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- Every request of the shared native receive primitives keeps or extends the CTX cache. -/
theorem sharedNative_grows {A : Type} (c : Pqxdh.Crypto) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (query : RawCtxSourceOpen.NativeSpec.Domain) (before : RawCtxSharedPrimitive.SharedState A) :
    ∀ result ∈ support ((RawCtxSharedPrimitive.nativeImpl c (RawCtxSourceHkdf.kdfImpl source) query).run before),
      before.2 ≤ result.2.2 := by
  intro result member
  rcases query with request | (bytes | input)
  · simp only [RawCtxSharedPrimitive.nativeImpl, RawCtxSourceHkdf.kdfImpl, StateT.run] at member
    change result ∈ support (pure (_, before) : ProbComp _) at member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact le_rfl
  · simp only [RawCtxSharedPrimitive.nativeImpl, RawCtxSharedPrimitive.openingImpl, StateT.run, bind_pure_comp,
      support_map] at member
    obtain ⟨hashed, reached, rfl⟩ := member
    exact PqxdhRecordFactsBindingEvidence.hash_grows ((), bytes) before.2 hashed reached
  · simp only [RawCtxSharedPrimitive.nativeImpl, RawCtxSharedPrimitive.openingImpl, StateT.run] at member
    change result ∈ support (pure (_, before) : ProbComp _) at member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact le_rfl

/-- Every request of the Beacon's native primitive interpreter keeps or extends the CTX cache. -/
theorem nativePrim_grows (query : RawCtxWholeOwner.PrimitiveSpec.Domain)
    (before : RawCtxSharedPrimitive.SharedState Unit) :
    ∀ result ∈ support ((PqxdhServerAuthBeaconFactor.nativePrim setup codec query).run before),
      before.2 ≤ result.2.2 := by
  intro result member
  change result ∈ support ((simulateQ (RawCtxSharedPrimitive.nativeImpl setup.source.crypto
    (RawCtxSourceHkdf.kdfImpl setup.source)) (RawCtxSourceOpen.nativeAdapter query)).run before) at member
  exact run_ctx_grows _ (sharedNative_grows setup.source.crypto setup.source) _ before result member

/-- Every request of the labelled Beacon receive over the native primitives keeps or extends the CTX cache. -/
theorem beaconLabels_grows (challenge : beaconcrypt_core.ratchet.RatchetKdfResponse)
    (query : (RawCtxChainReceive.ReceiveSpec RawCtxSelectedChain.Slot RawCtxSelectedChain.Slot
      beaconcrypt_core.ratchet.RatchetMaterial RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted).Domain)
    (before : RawCtxSharedPrimitive.SharedState Unit) :
    ∀ result ∈ support ((PqxdhServerAuthBeaconFactor.primLabels (PqxdhServerAuthBeaconFactor.nativePrim setup codec)
      setup.source challenge query).run before), before.2 ≤ result.2.2 := by
  intro result member
  rcases query with slot | pending
  · simp only [PqxdhServerAuthBeaconFactor.primLabels, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact le_rfl
  · simp only [PqxdhServerAuthBeaconFactor.primLabels, QueryImpl.apply_compose] at member
    exact run_ctx_grows _ (nativePrim_grows setup codec) _ before result member

/-- A raw receive of a chain owner keeps or extends the CTX cache when its receive call does. -/
theorem chainRaw_grows {Kernel Metadata : Type}
    (calls : RawCtxChainOwner.Calls Kernel (StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp))
    (grows : ∀ entry target context state, ∀ result ∈ support ((calls.receive entry target context).run state),
      state.2 ≤ result.2.2)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (owner : RawCtxChainOwner.State Kernel Metadata)
    (before : RawCtxSharedPrimitive.SharedState Unit) :
    ∀ result ∈ support (((RawCtxChainOwner.rawReceive calls decode raw).run owner).run before), before.2 ≤ result.2.2 := by
  intro result supported
  change result ∈ support ((if raw.isEmpty then pure (RawCtxChainOwner.publish owner (owner.kernel, .None)) else
    match decode raw with
    | none => pure (RawCtxChainOwner.publish owner (owner.kernel, .None))
    | some frame =>
      if RawCtxReceive.ValidFrame owner.expectedSender owner.associatedData frame then do
        let result ← calls.receive owner.kernel frame.sequence ⟨raw, frame, owner.associatedData⟩
        pure (RawCtxChainOwner.publish owner result)
      else pure (RawCtxChainOwner.publish owner (owner.kernel, .None)) :
        StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp _).run before) at supported
  have kept : ∀ value, result ∈ support ((pure value : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp _).run
      before) → before.2 ≤ result.2.2 := by
    intro value member
    rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact le_rfl
  split at supported
  · exact kept _ supported
  · split at supported
    · exact kept _ supported
    · split at supported
      · rw [StateT.run_bind, mem_support_bind_iff] at supported
        obtain ⟨received, member, published⟩ := supported
        rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at published
        subst published
        exact grows _ _ _ before received member
      · exact kept _ supported

/-- The erased hidden finish over the native primitives keeps or extends the CTX cache. -/
theorem finishErased_grows (challenge : PqxdhServerAuthSendFactor.Factor)
    (prepared : PqxdhBeaconPhase2Preparation.Prepared Response) (before : RawCtxSharedPrimitive.SharedState Unit) :
    ∀ result ∈ support ((PqxdhDeploymentHiddenKernels.finishErased (PqxdhServerAuthBeaconFactor.nativePrim setup codec)
      (fun entry _ => pure (entry, none)) setup.source (fun response => pure (codec.application response))
      codec.frameRead prepared challenge).run before), before.2 ≤ result.2.2 := by
  intro result member
  unfold PqxdhDeploymentHiddenKernels.finishErased at member
  simp only [pure_bind] at member
  split at member
  · rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact le_rfl
  · split_ifs at member
    · rw [StateT.run_map, support_map] at member
      obtain ⟨body, bodyMember, rfl⟩ := member
      unfold PqxdhDeploymentHiddenKernels.factoredBody at bodyMember
      rw [StateT.run_bind, mem_support_bind_iff] at bodyMember
      obtain ⟨received, receivedMember, finalMember⟩ := bodyMember
      rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at finalMember
      subst finalMember
      exact chainRaw_grows _ (fun entry target context state result member =>
        run_ctx_grows _ (beaconLabels_grows setup codec challenge.1) _ state result member) _ _ _ before received
        receivedMember
    · rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact le_rfl

end Opening

/-! ### The hidden steps -/

section Hidden
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- A slot client on the native state with an auxiliary component: every run grows the native state when every request does. -/
theorem slotRun_nGrows {κ α σ : Type} {spec : OracleSpec κ}
    (impl : QueryImpl spec (StateT (NativeState KemSK × σ) (OracleComp PqxdhDeploymentIdealSlots.SlotSpec)))
    (step : ∀ query state, ∀ result ∈ support ((impl query).run state), NGrows state.1 result.2.1)
    (work : OracleComp spec α) (state : NativeState KemSK × σ) :
    ∀ result ∈ support ((simulateQ impl work).run state), NGrows state.1 result.2.1 :=
  PqxdhDeploymentIdealEnvFacts.run_keepsGood impl (fun _ => False) (fun current => NGrows state.1 current.1)
    (fun query current _ held result member => nGrows_trans held (step query current result member)) work
    (isQueryBoundP_false work 0) state (nGrows_refl state.1)

/-- The erased hidden finish service, lifted to the native state, grows it. -/
theorem hiddenAfter_grows (value : PqxdhServerAuthKeySchedule.Output)
    (pending : PqxdhRegistrationJointKemPostSkeleton.Pending Response) :
    GrowsW (PqxdhServerAuthNative.nativeCtx (KemSK := KemSK)
      ((PqxdhDeploymentIdealSteps.erasedHidden setup codec checks value).hiddenAfter
        (PqxdhRegistrationJointKemPostSkeleton.embed pending))) := by
  refine growsW_ctx _ fun cache result member => ?_
  change result ∈ support ((Prod.fst <$> PqxdhDeploymentHiddenEntry.finishPointed setup codec
    (PqxdhDeploymentHiddenLayout.splitOutput value).1 (PqxdhDeploymentHiddenLayout.splitOutput value).2
    (PqxdhRegistrationJointKemPostSkeleton.embed pending)).run ((), cache)) at member
  rw [StateT.run_map, support_map] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  exact finishErased_grows setup codec _ _ ((), cache) inner innerMember

/-- The CE-native grouped finish grows the native state. -/
theorem groupCE_grows (pending : PqxdhRegistrationJointKemPostSkeleton.Pending Response)
    (state : NativeState KemSK × Option PqxdhDeploymentIdealSlots.Coord) :
    ∀ result ∈ support ((PqxdhDeploymentIdealSteps.groupCE setup codec (PqxdhDeploymentIdealSteps.erasedHidden setup
      codec checks) pending).run state), NGrows state.1 result.2.1 := by
  intro result member
  change result ∈ support (PqxdhDeploymentIdealSteps.groupCE setup codec (PqxdhDeploymentIdealSteps.erasedHidden setup
    codec checks) pending state) at member
  unfold PqxdhDeploymentIdealSteps.groupCE at member
  split at member
  · split_ifs at member
    · rw [mem_support_bind_iff] at member
      obtain ⟨value, -, member⟩ := member
      rw [mem_support_bind_iff] at member
      obtain ⟨inner, innerMember, member⟩ := member
      rw [support_pure, Set.mem_singleton_iff] at member
      subst member
      rw [OracleComp.support_liftComp] at innerMember
      exact hiddenAfter_grows setup codec checks value pending state.1 inner innerMember
    · rw [support_pure, Set.mem_singleton_iff] at member
      subst member
      exact nGrows_refl _
  · rw [support_map, OracleComp.support_liftComp] at member
    obtain ⟨inner, innerMember, rfl⟩ := member
    refine growsW_bind ?_ (fun root => ?_) state.1 inner innerMember
    · unfold PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot
      split
      · exact growsW_sourceRoot _ _
      · exact growsW_pure _
    · split
      · exact growsW_pure _
      · refine growsW_ctx _ fun cache result member => run_ctx_grows _ (fun query before result member => ?_) _ _
          result member
        rcases query with query | (input | request | response)
        · exact beaconNative_grows setup codec (.inl query) before result member
        · simp only [PqxdhRegistrationJointKemPostSkeleton.tailNative, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at member
          subst member
          exact le_rfl
        · exact beaconNative_grows setup codec (.inr (.initial request)) before result member
        · exact beaconNative_grows setup codec (.inr (.application response)) before result member

/-- Owner k's challenge finish grows the shared native state. -/
theorem finishChallenge_grows (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (index : ℕ) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationSchedule.State KemSK × Option PqxdhDeploymentIdealSlots.Coord) :
    ∀ result ∈ support ((PqxdhDeploymentIdealSteps.finishChallenge setup codec
      (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks) challenge index raw).run state),
      NGrows state.1.shared result.2.1.shared := by
  intro result member
  change result ∈ support (match state.1.owners[index]? with
    | none => pure (none, state)
    | some owner => do
        let result ← (simulateQ (PqxdhDeploymentIdealSteps.ownerImplCE setup codec
          (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks) challenge)
          (PqxdhDeploymentIdealSteps.groupedOwnerCE (Response := Response) raw owner)).run (state.1.shared, state.2)
        pure (result.1.1, (({ shared := result.2.1, owners := state.1.owners.set index result.1.2 } :
          PqxdhRegistrationSchedule.State KemSK), result.2.2))) at member
  split at member
  · rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact nGrows_refl _
  · rw [mem_support_bind_iff] at member
    obtain ⟨inner, innerMember, member⟩ := member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    refine slotRun_nGrows _ (fun query current result member => ?_) _ _ inner innerMember
    rcases query with query | pending
    · change result ∈ support ((fun reply => (reply, current)) <$> PqxdhDeploymentIdealSteps.liftS
        (PqxdhDeploymentIdealSteps.preparationCE setup codec challenge query)) at member
      rw [support_map] at member
      obtain ⟨_, _, rfl⟩ := member
      exact nGrows_refl _
    · exact groupCE_grows setup codec checks pending current result member

end Hidden

/-! ### The selected accept -/

section Selected
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- Every request of the selected accept's marker tail other than an install grows the native state. -/
theorem tailCE_grows (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (query : (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).Domain)
    (notInstall : ∀ game, query ≠ .inr (.install game))
    (state : NativeState KemSK × Option (ℕ × PqxdhDeploymentIdealSlots.Coord)) :
    ∀ result ∈ support ((PqxdhDeploymentIdealSteps.tailCE hmac index query).run state),
      NGrows state.1 result.2.1 := by
  intro result member
  rcases query with (input | aux) | mutation
  · cases shared : input.shared with
    | challenge =>
        simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run, shared, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at member
        obtain ⟨_, _, rfl⟩ := member
        exact nGrows_refl _
    | known secret =>
        simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run, shared, support_map,
          OracleComp.support_liftComp] at member
        obtain ⟨inner, innerMember, rfl⟩ := member
        unfold PqxdhRegistrationJointKemOpaqueClient.romRoot at innerMember
        exact (growsW_bind (growsW_romRootBytes _ _ _) fun _ => growsW_bind (growsW_local _ fun _ => rfl) fun _ =>
          growsW_pure _) state.1 inner innerMember
  · simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run, support_map, OracleComp.support_liftComp] at member
    obtain ⟨inner, innerMember, rfl⟩ := member
    cases aux with
    | eraseShared => exact growsW_pure () state.1 inner innerMember
    | eraseInput => exact growsW_pure () state.1 inner innerMember
    | consume rid => exact growsW_local _ (fun _ => rfl) state.1 inner innerMember
  · simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run, support_map, OracleComp.support_liftComp] at member
    obtain ⟨inner, innerMember, rfl⟩ := member
    cases mutation with
    | install game => exact absurd rfl (notInstall game)
    | publish at_ token => exact growsW_local _ (fun _ => rfl) state.1 inner innerMember

/-- The selected accept's marker tail from its own game state grows the native state. -/
theorem opaqueTail_grows (hmac : PqxdhSecretInputKdf.HmacSha512) (serverKeyId : Std.U64)
    (publicIdentity : PqxdhJointIdentity.PublicIdentity) (s : NativeState KemSK)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes)
    (mark : Option (ℕ × PqxdhDeploymentIdealSlots.Coord)) :
    ∀ result ∈ support ((simulateQ (PqxdhDeploymentIdealSteps.tailCE hmac s.2.sessions)
      (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity s.2 collected)).run (s, mark)),
      NGrows s result.2.1 := by
  intro result member
  unfold PqxdhRegistrationJointKemOpaqueTail.tail at member
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at member
  obtain ⟨installed, installedMember, member⟩ := member
  simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run, support_map, OracleComp.support_liftComp,
    PqxdhRegistrationJointKemOpaqueTail.mutation, PqxdhServerAuthNative.nativeSet, PqxdhServerAuthNative.localState,
    support_pure, Set.mem_image, Set.mem_singleton_iff] at installedMember
  obtain ⟨_, rfl, rfl⟩ := installedMember
  split at member
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨fun _ _ found => found, fun _ _ found => found⟩
  · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
    obtain ⟨returned, returnedMember, member⟩ := member
    rw [← QueryImpl.simulateQ_compose] at returnedMember
    have first := slotRun_nGrows _ (fun query current result member => by
      simp only [QueryImpl.apply_compose, PqxdhRegistrationJointKemOpaqueTail.forward, simulateQ_spec_query] at member
      exact tailCE_grows hmac s.2.sessions (.inl query) (fun _ wrong => by cases wrong) current result member)
      _ _ returned returnedMember
    have base := nGrows_trans (⟨fun _ _ found => found, fun _ _ found => found⟩ : NGrows s _) first
    split at member
    · simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
      obtain ⟨published, publishedMember, rfl⟩ := member
      exact nGrows_trans base (tailCE_grows hmac s.2.sessions _ (fun _ wrong => by cases wrong) _ published
        publishedMember)
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact base

/-- The selected accept on a key match grows the native state. -/
theorem acceptActive_grows (seed : PqxdhJointIdentity.IdentitySeed) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (verified : PqxdhServerRootPreparation.Verified Reader) (s : NativeState KemSK) :
    ∀ result ∈ support ((PqxdhDeploymentIdealSteps.acceptActive setup codec checks seed challenge verified).run s),
      NGrows s result.2 := by
  intro result member
  change result ∈ support (PqxdhDeploymentIdealSteps.acceptActive setup codec checks seed challenge verified s) at member
  unfold PqxdhDeploymentIdealSteps.acceptActive at member
  rw [mem_support_bind_iff] at member
  obtain ⟨pre, _, member⟩ := member
  split at member
  · rw [mem_support_bind_iff] at member
    obtain ⟨tailed, tailedMember, member⟩ := member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    rw [OracleComp.support_liftComp] at tailedMember
    simp only [PqxdhRegistrationJointServerAccept.tail, PqxdhServerAuthNative.nativeSet, StateT.run, bind_pure_comp]
      at tailedMember
    obtain ⟨_, rfl, rfl⟩ := tailedMember
    exact ⟨fun _ _ found => found, fun _ _ found => found⟩
  · rw [mem_support_bind_iff] at member
    obtain ⟨prepared, _, member⟩ := member
    rw [mem_support_bind_iff] at member
    obtain ⟨answer, answerMember, member⟩ := member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact opaqueTail_grows _ _ _ s _ none answer answerMember

/-- The LQ-F logged accept as a slot client grows the native state. -/
theorem acceptInactive_grows (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes) (s : NativeState KemSK) :
    ∀ result ∈ support ((PqxdhDeploymentIdealSteps.acceptInactive setup codec checks seed raw).run s),
      NGrows s result.2 := by
  intro result member
  change result ∈ support ((fun r : (Option ℕ × Option PqxdhJointGapDh.ScalarBytes) × NativeState KemSK =>
    ((r.1, (false, none)), r.2)) <$> PqxdhDeploymentIdealSteps.liftS
      ((PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw).run s)) at member
  rw [support_map, OracleComp.support_liftComp] at member
  obtain ⟨logged, loggedMember, rfl⟩ := member
  have native : ((logged.1.1, logged.2) : Option ℕ × NativeState KemSK) ∈ support
      ((PqxdhServerAuthNative.nativeAccept setup codec checks seed PqxdhRegistrationSchedule.observationScalar raw).run
        s) := by
    rw [← PqxdhDeploymentLaterServerNative.acceptLogged_fst, support_map]
    exact ⟨logged, loggedMember, rfl⟩
  exact accept_grows setup codec checks seed _ raw s _ native

/-- The selected accept with its encapsulation exposed grows the native state. -/
theorem acceptExposed_grows (seed : PqxdhJointIdentity.IdentitySeed) (chosen : PqxdhLiveKemReservation.Pair KemSK)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes) (s : NativeState KemSK) :
    ∀ result ∈ support ((PqxdhDeploymentIdealSteps.acceptExposed setup codec checks seed chosen challenge raw).run s),
      NGrows s result.2 := by
  intro result member
  unfold PqxdhDeploymentIdealSteps.acceptExposed at member
  split at member
  · split_ifs at member
    · exact acceptActive_grows setup codec checks seed challenge _ s result member
    · exact acceptInactive_grows setup codec checks seed raw s result member
  · exact acceptInactive_grows setup codec checks seed raw s result member

/-- The selected accept's marker tail marks only the given session index. -/
theorem tailCE_mark {α : Type} (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (work : OracleComp (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK) α)
    (state : NativeState KemSK × Option (ℕ × PqxdhDeploymentIdealSlots.Coord))
    (holds : ∀ i c, state.2 = some (i, c) → i = index) :
    ∀ result ∈ support ((simulateQ (PqxdhDeploymentIdealSteps.tailCE hmac index) work).run state),
      ∀ i c, result.2.2 = some (i, c) → i = index := by
  refine PqxdhDeploymentIdealEnvFacts.run_keepsGood _ (fun _ => False)
    (fun current => ∀ i c, current.2 = some (i, c) → i = index) (fun query current _ held result member => ?_) work
    (isQueryBoundP_false work 0) state holds
  rcases query with (input | aux) | mutation
  · cases shared : input.shared with
    | challenge =>
        simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run, shared, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at member
        obtain ⟨_, _, rfl⟩ := member
        intro i c found
        simp only [Option.some.injEq, Prod.mk.injEq] at found
        exact found.1.symm
    | known secret =>
        simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run, shared, support_map] at member
        obtain ⟨_, _, rfl⟩ := member
        exact held
  · simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run, support_map] at member
    obtain ⟨_, _, rfl⟩ := member
    exact held
  · simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run, support_map] at member
    obtain ⟨_, _, rfl⟩ := member
    exact held

/-- The selected accept marks only its own session index, the session counter before the call. -/
theorem acceptExposed_mark (seed : PqxdhJointIdentity.IdentitySeed) (chosen : PqxdhLiveKemReservation.Pair KemSK)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes) (s : NativeState KemSK) :
    ∀ result ∈ support ((PqxdhDeploymentIdealSteps.acceptExposed setup codec checks seed chosen challenge raw).run s),
      ∀ i c, result.1.2.2 = some (i, c) → i = s.2.sessions := by
  intro result member
  have inactive : result ∈ support ((PqxdhDeploymentIdealSteps.acceptInactive setup codec checks seed raw).run s) →
      ∀ i c, result.1.2.2 = some (i, c) → i = s.2.sessions := by
    intro inactiveMember i c found
    rw [(PqxdhDeploymentIdealKeymatch.acceptInactive_facts setup codec checks seed raw s result inactiveMember).2.1]
      at found
    cases found
  unfold PqxdhDeploymentIdealSteps.acceptExposed at member
  split at member
  · split_ifs at member
    · change result ∈ support (PqxdhDeploymentIdealSteps.acceptActive setup codec checks seed challenge _ s) at member
      unfold PqxdhDeploymentIdealSteps.acceptActive at member
      rw [mem_support_bind_iff] at member
      obtain ⟨pre, _, member⟩ := member
      split at member
      · rw [mem_support_bind_iff] at member
        obtain ⟨_, _, member⟩ := member
        rw [support_pure, Set.mem_singleton_iff] at member
        subst member
        intro i c found
        cases found
      · rw [mem_support_bind_iff] at member
        obtain ⟨_, _, member⟩ := member
        rw [mem_support_bind_iff] at member
        obtain ⟨answer, answerMember, member⟩ := member
        rw [support_pure, Set.mem_singleton_iff] at member
        subst member
        exact tailCE_mark _ _ _ (s, none) (fun _ _ found => by cases found) answer answerMember
    · exact inactive member
  · exact inactive member

end Selected

/-! ### The native deployment handler -/

section Deployment
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder)

/-- A Server record step grows the native shared state. -/
theorem serverStep_grows (query : RawCtxServerMixed.SourceSpec.Domain) (state : PqxdhDeploymentNative.State KemSK) :
    ∀ result ∈ support ((PqxdhDeploymentNative.serverStep setup codec route query).run state),
      NGrows state.native.shared result.2.native.shared := by
  intro result member
  change result ∈ support (do
    let result ← (PqxdhDeploymentNative.record setup codec (PqxdhDeploymentNative.logged
      ((RawCtxServerMixed.serverImpl (PqxdhDeploymentNative.senderId state) route codec.frameRead query).run
        (PqxdhDeploymentNative.serverView state)))).run state.native
    pure (result.1.1.1, PqxdhDeploymentNative.produce (PqxdhDeploymentNative.serverTag query) result.1.2
      (PqxdhDeploymentNative.withServer { state with native := result.2 } result.1.1.2))) at member
  rw [mem_support_bind_iff] at member
  obtain ⟨recorded, recordedMember, member⟩ := member
  rw [support_pure, Set.mem_singleton_iff] at member
  subst member
  have grown := onShared_grows _ (growsW_ctx _ fun cache result member =>
    run_ctx_grows _ (fun query state result member => sharedImpl_grows setup.source.crypto codec.frameWrite setup.source
      query state result member) _ _ result member) state.native recorded recordedMember
  exact ⟨grown.1, grown.2⟩

/-- A Beacon record step grows the native shared state. -/
theorem beaconStep_grows (index : ℕ) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : PqxdhDeploymentNative.State KemSK) :
    ∀ result ∈ support ((PqxdhDeploymentNative.beaconStep setup codec index query).run state),
      NGrows state.native.shared result.2.native.shared := by
  intro result member
  change result ∈ support (PqxdhDeploymentNative.beaconStep setup codec index query state) at member
  unfold PqxdhDeploymentNative.beaconStep at member
  split at member
  · rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact nGrows_refl _
  · rw [mem_support_bind_iff] at member
    obtain ⟨recorded, recordedMember, member⟩ := member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    have grown := onShared_grows _ (growsW_ctx _ fun cache result member =>
      run_ctx_grows _ (fun query state result member => sharedImpl_grows setup.source.crypto codec.frameWrite
        setup.source query state result member) _ _ result member) state.native recorded recordedMember
    exact ⟨grown.1, grown.2⟩

/-- Every query of the native deployment handler grows the native shared state. -/
theorem nativeHandler_grows (seed : PqxdhJointIdentity.IdentitySeed) (query : PqxdhDeploymentInterface.Spec.Domain)
    (state : PqxdhDeploymentNative.State KemSK) :
    ∀ result ∈ support ((PqxdhDeploymentNative.handler setup codec checks route seed query).run state),
      NGrows state.native.shared result.2.native.shared := by
  intro result member
  have viaNative : ∀ {α : Type} (work : PqxdhRegistrationSchedule.Game KemSK α),
      (∀ native, ∀ inner ∈ support (work.run native), NGrows native.shared inner.2.shared) →
      ∀ result ∈ support ((PqxdhDeploymentNative.onNative work).run state),
        NGrows state.native.shared result.2.native.shared := by
    intro _ work grows result member
    obtain ⟨inner, innerMember, rfl⟩ := PqxdhDeploymentEligibility.onNative_support work state result member
    exact grows state.native inner innerMember
  have kept : ∀ {α : Type} (work : PqxdhRegistrationSchedule.Game KemSK α),
      (∀ native, ∀ inner ∈ support (work.run native), inner.2.shared = native.shared) →
      ∀ native, ∀ inner ∈ support (work.run native), NGrows native.shared inner.2.shared := by
    intro _ work same native inner member
    rw [same native inner member]
    exact nGrows_refl _
  rcases query with coin | command
  · simp only [PqxdhDeploymentNative.handler, StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at member
    obtain ⟨_, _, rfl⟩ := member
    exact nGrows_refl _
  · cases command with
    | create pin keyId =>
        change result ∈ support ((match PqxdhDeploymentInterface.parsePin pin with
          | none => pure none
          | some word => some <$> PqxdhDeploymentNative.onNative (PqxdhRegistrationSchedule.handler setup codec checks
              seed (.inr (.create word keyId)))).run state) at member
        split at member
        · rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
          subst member
          exact nGrows_refl _
        · rw [StateT.run_map, support_map] at member
          obtain ⟨inner, innerMember, rfl⟩ := member
          refine viaNative _ (kept _ fun native created createdMember => ?_) inner innerMember
          change created ∈ support ((PqxdhRegistrationSchedule.create setup _ keyId).run native) at createdMember
          simp only [PqxdhRegistrationSchedule.create, StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set,
            StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
            at createdMember
          obtain ⟨_, _, _, _, _, _, rfl⟩ := createdMember
          rfl
    | bundle index =>
        refine viaNative _ (kept _ fun native bundled bundledMember => ?_) result member
        change bundled ∈ support ((PqxdhRegistrationSchedule.bundle setup codec index).run native) at bundledMember
        cases found : native.owners[index]? with
        | none =>
            simp only [PqxdhRegistrationSchedule.bundle, StateT.run_bind, StateT.run_get, pure_bind, found,
              StateT.run_pure, support_pure, Set.mem_singleton_iff] at bundledMember
            rw [bundledMember]
        | some owner =>
            change bundled ∈ support (PqxdhRegistrationSchedule.bundle setup codec index native) at bundledMember
            rw [PqxdhRegistrationSchedule.bundle_source setup codec index native owner found, support_map] at bundledMember
            obtain ⟨_, _, rfl⟩ := bundledMember
            rfl
    | accept raw =>
        exact viaNative _ (fun native inner member =>
          onShared_grows _ (accept_grows setup codec checks _ _ raw) native inner member) result member
    | build session payload =>
        exact viaNative _ (fun native inner member =>
          onShared_grows _ (build_grows setup codec checks session payload) native inner member) result member
    | finish owner raw =>
        exact viaNative _ (fun native inner member => finish_grows setup codec owner raw native inner member) result
          member
    | hmac key message =>
        exact viaNative _ (fun native inner member =>
          onShared_grows _ (hmac_grows setup _ _ key message) native inner member) result member
    | hash bytes =>
        exact viaNative _ (fun native inner member => onShared_grows _ (growsW_hash bytes) native inner member) result
          member
    | serverSend keyId plaintext =>
        exact serverStep_grows setup codec route (.inl (plaintext, keyId)) state result member
    | serverRaw raw => exact serverStep_grows setup codec route (.inr raw) state result member
    | beaconSend owner plaintext => exact beaconStep_grows setup codec owner (.inl plaintext) state result member
    | beaconRaw owner raw => exact beaconStep_grows setup codec owner (.inr raw) state result member

end Deployment

/-! ### The step facts of the slot programs -/

section Prog
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder) {count : ℕ} (t : PqxdhDeploymentIdealParams.Target count)
  (p : PqxdhDeploymentIdealParams.Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

/-- What one slot step does to the deployment state and the ideal backend: the native shared state grows; the accept counter does not decrease; the mark changes only at the selected ordinal, and a new mark is at the session counter before the step; and up to the selected ordinal, with no mark and an inactive selected accept, the step sets no mark, keeps the selected accept inactive, does not lower the session counter and adds pending tokens only below the new counter. -/
structure ProgFacts (y z : XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2) : Prop where
  grows : NGrows y.base.native.shared z.base.native.shared
  accepts : y.backend.accepts ≤ z.backend.accepts
  marks : y.backend.accepts ≠ t.accept → z.backend.marks = y.backend.marks
  fresh : ∀ s c, z.backend.marks = some (s, c) → y.backend.marks = some (s, c) ∨ s = y.base.native.shared.2.sessions
  early : y.backend.accepts ≤ t.accept → y.backend.marks = none → y.backend.active = false →
    z.backend.accepts ≤ t.accept →
    z.backend.marks = none ∧ z.backend.active = false ∧
      y.base.native.shared.2.sessions ≤ z.base.native.shared.2.sessions ∧
      ∀ s, (z.base.native.shared.2.pending s).isSome = true →
        (y.base.native.shared.2.pending s).isSome = true ∨ s < z.base.native.shared.2.sessions

/-- A step that grows the native state and keeps the ideal backend, the session counter and the pending tokens. -/
theorem progFacts_quiet (y z : XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2)
    (grows : NGrows y.base.native.shared z.base.native.shared) (backend : z.backend = y.backend)
    (sessions : z.base.native.shared.2.sessions = y.base.native.shared.2.sessions)
    (pending : z.base.native.shared.2.pending = y.base.native.shared.2.pending) : ProgFacts t y z := by
  refine ⟨grows, by rw [backend], fun _ => by rw [backend], fun s c marked => Or.inl (by rw [← backend]; exact marked),
    fun _ marks active _ => ⟨by rw [backend]; exact marks, by rw [backend]; exact active, by rw [sessions],
      fun s found => Or.inl (by rw [← pending]; exact found)⟩⟩

/-- The real registration handler on a quiet command (bundle, HMAC, finish) as a slot step. -/
theorem realQuiet_facts (query : PqxdhRecordLiftInterface.EnvQuery)
    (quiet : match query.val with
      | .bundle _ | .hmac _ _ | .finish _ _ => True
      | _ => False)
    (y : XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2)
    (z : PqxdhRecordLiftInterface.EnvSpec.Range query × XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2)
    (member : z ∈ support ((PqxdhDeploymentIdealSteps.onSlots (PqxdhDeploymentIdealSteps.realRegAt setup codec route
      checks created query)).run y)) : ProgFacts t y z.2 := by
  change z ∈ support (OracleComp.liftComp ((PqxdhDeploymentIdealSteps.realRegAt setup codec route checks created
    query).run y) PqxdhDeploymentIdealSlots.SlotSpec) at member
  rw [OracleComp.support_liftComp] at member
  obtain ⟨native, backend⟩ := PqxdhDeploymentIdealKeymatch.realRegAt_support setup codec route checks created query y z
    member
  have grows := nativeHandler_grows setup codec checks route created.seed _ y.base _ native
  rcases query with ⟨command, allowed⟩
  cases command with
  | bundle k =>
      have lowered := PqxdhDeploymentIdealKeymatch.onNative_native _ y.base z.1 z.2.base native
      have shared := PqxdhRegistrationSchedule.owner_fields setup codec checks created.seed (.inr (.bundle k)) trivial
        y.base.native _ lowered
      exact progFacts_quiet t y z.2 grows backend (by rw [shared]) (by rw [shared])
  | hmac key message =>
      obtain ⟨-, sessions, pending⟩ := PqxdhDeploymentHeadlineCtTrace.native_kept setup codec checks route created.seed
        (.inr (.hmac key message)) trivial y.base _ native
      exact progFacts_quiet t y z.2 grows backend sessions pending
  | finish owner raw =>
      obtain ⟨-, sessions, pending⟩ := PqxdhDeploymentHeadlineCtTrace.native_kept setup codec checks route created.seed
        (.inr (.finish owner raw)) trivial y.base _ native
      exact progFacts_quiet t y z.2 grows backend sessions pending
  | _ => exact False.elim quiet

/-- The create of the ideal registration keeps the native shared state and the ideal backend. -/
theorem createProg_facts (hidden : PqxdhServerAuthKeySchedule.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (pin : Pqxdh.Bytes) (keyId : Std.U64) (y : XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2)
    (z : Option ℕ × XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2)
    (member : z ∈ support ((PqxdhDeploymentIdealSteps.idealProg setup codec route checks t p hidden created
      ⟨.create pin keyId, trivial⟩).run y)) : ProgFacts t y z.2 := by
  change z ∈ support (PqxdhDeploymentIdealSteps.liftS ((PqxdhDeploymentIdealSteps.createReg setup (p.pool t) pin
    keyId).run y)) at member
  rw [OracleComp.support_liftComp] at member
  have based := PqxdhDeploymentIdealCut.onBase_base (match PqxdhDeploymentInterface.parsePin pin with
    | none => pure none
    | some word => some <$> PqxdhDeploymentNative.onNative (PqxdhDeploymentIdealSteps.createPool setup (p.pool t) word
        keyId)) y
  have step : (z.1, z.2.base) ∈ support ((match PqxdhDeploymentInterface.parsePin pin with
      | none => pure none
      | some word => some <$> PqxdhDeploymentNative.onNative (PqxdhDeploymentIdealSteps.createPool setup (p.pool t) word
          keyId) : StateT (PqxdhDeploymentNative.State KemSK) ProbComp (Option ℕ)).run y.base) := by
    rw [← based.1, support_map]
    exact ⟨z, member, rfl⟩
  have shared : z.2.base.native.shared = y.base.native.shared := by
    cases parsed : PqxdhDeploymentInterface.parsePin pin with
    | none =>
        simp only [parsed, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at step
        rw [step.2]
    | some word =>
        simp only [parsed, StateT.run_map] at step
        rw [support_map] at step
        obtain ⟨native, nativeMember, same⟩ := step
        simp only [Prod.mk.injEq] at same
        rw [← same.2]
        obtain ⟨reached, reachedMember, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ y.base native nativeMember
        exact (PqxdhDeploymentIdealKeymatch.createPool_facts setup (p.pool t) word keyId y.base.native reached
          reachedMember).1
  exact progFacts_quiet t y z.2 (by rw [shared]; exact nGrows_refl _) (based.2 z member).1 (by rw [shared])
    (by rw [shared])

/-- The raw accept of the ideal registration. -/
theorem acceptProg_facts (raw : Pqxdh.Bytes) (y : XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2)
    (z : Option ℕ × XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2)
    (member : z ∈ support ((PqxdhDeploymentIdealSteps.acceptStep setup codec route checks t p created raw).run y)) :
    ProgFacts t y z.2 := by
  have accepts := PqxdhDeploymentIdealSteps.acceptStep_accepts setup codec route checks t p created raw y z member
  change z ∈ support (PqxdhDeploymentIdealSteps.acceptStep setup codec route checks t p created raw y) at member
  unfold PqxdhDeploymentIdealSteps.acceptStep at member
  by_cases selected : y.backend.accepts = t.accept
  · simp only [selected, ↓reduceIte] at member
    rw [support_map] at member
    obtain ⟨inner, innerMember, rfl⟩ := member
    refine ⟨acceptExposed_grows setup codec checks _ _ _ raw _ inner innerMember, by rw [accepts]; omega,
      fun other => absurd selected other, fun s c marked => Or.inr ?_, fun _ _ _ late => ?_⟩
    · exact acceptExposed_mark setup codec checks _ _ _ raw _ inner innerMember s c marked
    · rw [accepts] at late
      omega
  · simp only [selected, ↓reduceIte] at member
    change z ∈ support (OracleComp.liftComp _ PqxdhDeploymentIdealSlots.SlotSpec) at member
    rw [OracleComp.support_liftComp] at member
    obtain ⟨native, backend⟩ := PqxdhDeploymentIdealKeymatch.realRegAt_support setup codec route checks created
      ⟨.accept raw, trivial⟩ _ z member
    have lowered := PqxdhDeploymentIdealKeymatch.onNative_native
      (PqxdhRegistrationSchedule.onShared (PqxdhServerAuthNative.nativeAccept setup codec checks created.seed
        PqxdhRegistrationSchedule.observationScalar raw)) _ z.1 z.2.base native
    change (z.1, z.2.base.native) ∈ support ((fun result => (result.1, { y.base.native with shared := result.2 })) <$>
      (PqxdhServerAuthNative.nativeAccept setup codec checks created.seed PqxdhRegistrationSchedule.observationScalar
        raw).run y.base.native.shared) at lowered
    rw [support_map] at lowered
    obtain ⟨inner, innerMember, same⟩ := lowered
    have sharedEq : z.2.base.native.shared = inner.2 := by
      have := congrArg (fun r => r.2.shared) same
      exact this.symm
    have grows := accept_grows setup codec checks _ _ raw _ inner innerMember
    obtain ⟨sessions, others, -, -⟩ := PqxdhDeploymentHeadlineCtTrace.nativeAccept_footprint setup codec checks
      created.seed raw _ inner innerMember
    refine ⟨by rw [sharedEq]; exact grows, by rw [accepts]; omega, fun _ => by rw [backend], fun s c marked => Or.inl
      (by rw [backend] at marked; exact marked), fun _ marks active _ => ⟨by rw [backend]; exact marks,
        by rw [backend]; exact active, by rw [sharedEq, sessions]; omega, fun s found => ?_⟩⟩
    rw [sharedEq] at found
    by_cases at_ : s = y.base.native.shared.2.sessions
    · right
      rw [sharedEq, sessions, at_]
      omega
    · left
      rw [others s at_] at found
      exact found

/-- The real build of the slot program. -/
theorem realBuild_facts (session : ℕ) (payload : Option Pqxdh.Bytes) (y : XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2)
    (z : (Option PqxdhServerRegistrationPublication.Response × Option PqxdhDeploymentIdealSlots.Coord) ×
      XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2)
    (member : z ∈ support ((fun r : Option PqxdhServerRegistrationPublication.Response ×
      XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2 => ((r.1, none), r.2)) <$> OracleComp.liftComp
      ((PqxdhDeploymentIdealSteps.realRegAt setup codec route checks created ⟨.build session payload, trivial⟩).run y)
        PqxdhDeploymentIdealSlots.SlotSpec)) : ProgFacts t y z.2 := by
  rw [support_map, OracleComp.support_liftComp] at member
  obtain ⟨q, qMember, rfl⟩ := member
  obtain ⟨native, backend⟩ := PqxdhDeploymentIdealKeymatch.realRegAt_support setup codec route checks created
    ⟨.build session payload, trivial⟩ y q qMember
  have lowered := PqxdhDeploymentIdealKeymatch.onNative_native
    (PqxdhRegistrationSchedule.onShared (PqxdhServerAuthNative.nativeBuild setup codec checks session payload))
    y.base q.1 q.2.base native
  change (q.1, q.2.base.native) ∈ support ((fun result => (result.1, { y.base.native with shared := result.2 })) <$>
    (PqxdhServerAuthNative.nativeBuild setup codec checks session payload).run y.base.native.shared) at lowered
  rw [support_map] at lowered
  obtain ⟨inner, innerMember, same⟩ := lowered
  have sharedEq : q.2.base.native.shared = inner.2 := (congrArg (fun r => r.2.shared) same).symm
  have grows := build_grows setup codec checks session payload _ inner innerMember
  obtain ⟨sessions, others, consumed, -⟩ := PqxdhDeploymentHeadlineCtTrace.nativeBuild_footprint setup codec checks
    created.seed session payload _ inner innerMember
  refine ⟨by rw [sharedEq]; exact grows, by rw [backend], fun _ => by rw [backend], fun s c marked => Or.inl
    (by rw [backend] at marked; exact marked), fun _ marks active _ => ⟨by rw [backend]; exact marks,
      by rw [backend]; exact active, by rw [sharedEq, sessions], fun s found => Or.inl ?_⟩⟩
  rw [sharedEq] at found
  by_cases at_ : s = session
  · subst at_
    rw [consumed] at found
    cases found
  · rw [others s at_] at found
    exact found

/-- The build step of the split core with the erased hidden services. -/
theorem buildProg_facts (session : ℕ) (payload : Option Pqxdh.Bytes) (y : XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2)
    (z : (Option PqxdhServerRegistrationPublication.Response × Option PqxdhDeploymentIdealSlots.Coord) ×
      XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2)
    (member : z ∈ support ((PqxdhDeploymentIdealKernel.buildStepC setup codec checks route
      (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks) created session payload).run y)) :
    ProgFacts t y z.2 := by
  change z ∈ support (match y.backend.marks with
    | some (index, coords) =>
        if index = session ∧ (y.base.native.shared.2.pending session).isSome then
          (PqxdhDeploymentIdealKernel.buildHiddenC (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks) session
            payload coords).run y
        else (fun r : Option PqxdhServerRegistrationPublication.Response × XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2 =>
          ((r.1, none), r.2)) <$> PqxdhDeploymentIdealSteps.onSlots
          (PqxdhDeploymentIdealSteps.realRegAt setup codec route checks created ⟨.build session payload, trivial⟩) y
    | none => (fun r : Option PqxdhServerRegistrationPublication.Response × XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2 =>
        ((r.1, none), r.2)) <$> PqxdhDeploymentIdealSteps.onSlots
        (PqxdhDeploymentIdealSteps.realRegAt setup codec route checks created ⟨.build session payload, trivial⟩) y)
    at member
  split at member
  · rename_i index coords markedEq
    split_ifs at member with guard
    · unfold PqxdhDeploymentIdealKernel.buildHiddenC at member
      rw [PqxdhDeploymentIdealErase.readAt_bind_run, mem_support_bind_iff] at member
      obtain ⟨value, -, member⟩ := member
      change z ∈ support (OracleComp.liftComp (((fun r => (r, some coords)) <$> PqxdhDeploymentIdealErase.buildFocus
        (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks value) session payload coords).run y)
          PqxdhDeploymentIdealSlots.SlotSpec) at member
      rw [OracleComp.support_liftComp, StateT.run_map, support_map] at member
      obtain ⟨b, bMember, rfl⟩ := member
      unfold PqxdhDeploymentIdealErase.buildFocus at bMember
      simp only [StateT.run] at bMember
      rw [support_map] at bMember
      obtain ⟨h, hMember, rfl⟩ := bMember
      refine ⟨buildHidden_grows setup codec checks value session payload _ h hMember, le_rfl, fun _ => rfl,
        fun s c marked => Or.inl marked, fun _ marks _ _ => ?_⟩
      rw [markedEq] at marks
      cases marks
    · exact realBuild_facts setup codec checks route t created session payload y z member
  · exact realBuild_facts setup codec checks route t created session payload y z member

/-- The finish step of the split core with the erased hidden services. -/
theorem finishProg_facts (owner : ℕ) (raw : Pqxdh.Bytes) (y : XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2)
    (z : (Option Pqxdh.Bytes × Option PqxdhDeploymentIdealSlots.Coord) × XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2)
    (member : z ∈ support ((PqxdhDeploymentIdealKernel.finishStepC setup codec checks route t p
      (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks) created owner raw).run y)) :
    ProgFacts t y z.2 := by
  change z ∈ support (PqxdhDeploymentIdealKernel.finishStepC setup codec checks route t p
    (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks) created owner raw y) at member
  unfold PqxdhDeploymentIdealKernel.finishStepC at member
  split_ifs at member with guard
  · change z ∈ support ((fun r => ((r.1, r.2.2), PqxdhDeploymentIdealKernel.assembleF y owner r.2)) <$>
      (PqxdhDeploymentIdealSteps.finishChallenge setup codec (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks)
        p.challenge owner raw).run (y.base.native, none)) at member
    rw [support_map] at member
    obtain ⟨r, rMember, rfl⟩ := member
    refine ⟨finishChallenge_grows setup codec checks p.challenge owner raw _ r rMember, le_rfl, fun _ => rfl,
      fun s c marked => Or.inl marked, fun _ _ active _ => ?_⟩
    rw [guard.1] at active
    cases active
  · change z ∈ support ((fun r => ((r.1, none), r.2)) <$> PqxdhDeploymentIdealSteps.onSlots
      (PqxdhDeploymentIdealSteps.realRegAt setup codec route checks created ⟨.finish owner raw, trivial⟩) y) at member
    rw [support_map] at member
    obtain ⟨q, qMember, rfl⟩ := member
    exact realQuiet_facts setup codec checks route t created ⟨.finish owner raw, trivial⟩ trivial y q qMember

end Prog

/-! ### The step facts of the split handler -/

section Split
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder) {count : ℕ} (t : PqxdhDeploymentIdealParams.Target count)
  (p : PqxdhDeploymentIdealParams.Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

/-- What one command of the split handler does to the extended state: the native shared state and the slot state grow, and the ideal backend moves as `ProgFacts` says. -/
structure StepFacts (x y : XState KemSK PqxdhDeploymentIdealSteps.SplitBk 2) : Prop where
  grows : NGrows x.base.native.shared y.base.native.shared
  slots : SlotGrows (x.backend.2.1, (x.backend.1, x.seeds)) (y.backend.2.1, (y.backend.1, y.seeds))
  accepts : x.backend.2.2.accepts ≤ y.backend.2.2.accepts
  marks : x.backend.2.2.accepts ≠ t.accept → y.backend.2.2.marks = x.backend.2.2.marks
  fresh : ∀ s c, y.backend.2.2.marks = some (s, c) →
    x.backend.2.2.marks = some (s, c) ∨ s = x.base.native.shared.2.sessions
  early : x.backend.2.2.accepts ≤ t.accept → x.backend.2.2.marks = none → x.backend.2.2.active = false →
    y.backend.2.2.accepts ≤ t.accept →
    y.backend.2.2.marks = none ∧ y.backend.2.2.active = false ∧
      x.base.native.shared.2.sessions ≤ y.base.native.shared.2.sessions ∧
      ∀ s, (y.base.native.shared.2.pending s).isSome = true →
        (x.base.native.shared.2.pending s).isSome = true ∨ s < y.base.native.shared.2.sessions

theorem stepFacts_refl (x : XState KemSK PqxdhDeploymentIdealSteps.SplitBk 2) : StepFacts t x x :=
  ⟨nGrows_refl _, slotGrows_refl _, le_rfl, fun _ => rfl, fun _ _ marked => Or.inl marked,
    fun _ marks active _ => ⟨marks, active, le_rfl, fun _ found => Or.inl found⟩⟩

/-- A step that keeps the backend and the seed table, grows the native shared state and keeps the session counter and the pending tokens. -/
theorem stepFacts_quiet (x y : XState KemSK PqxdhDeploymentIdealSteps.SplitBk 2)
    (grows : NGrows x.base.native.shared y.base.native.shared) (backend : y.backend = x.backend) (seeds : y.seeds = x.seeds)
    (sessions : y.base.native.shared.2.sessions = x.base.native.shared.2.sessions)
    (pending : y.base.native.shared.2.pending = x.base.native.shared.2.pending) : StepFacts t x y := by
  refine ⟨grows, by rw [backend, seeds]; exact slotGrows_refl _, by rw [backend], fun _ => by rw [backend],
    fun s c marked => Or.inl (by rw [← backend]; exact marked), fun _ marks active _ => ⟨by rw [backend]; exact marks,
      by rw [backend]; exact active, by rw [sessions], fun s found => Or.inl (by rw [← pending]; exact found)⟩⟩

/-- A slot step run by `slotRunX` through the lazy service moves the extended state as its slot program says. -/
theorem stepFacts_slot {β : Type}
    (step : StateT (XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2) (OracleComp PqxdhDeploymentIdealSlots.SlotSpec) β)
    (x : XState KemSK PqxdhDeploymentIdealSteps.SplitBk 2) (result : β × XState KemSK PqxdhDeploymentIdealSteps.SplitBk 2)
    (member : result ∈ support ((PqxdhDeploymentIdealKernel.slotRunX PqxdhDeploymentIdealKernel.lazyDummy step).run x))
    (facts : ∀ inner ∈ support (step.run (PqxdhDeploymentIdealKeys.detachX x)),
      ProgFacts t (PqxdhDeploymentIdealKeys.detachX x) inner.2) : StepFacts t x result.2 := by
  obtain ⟨inner, innerMember, -, baseEq, coreEq, slots⟩ := slotRunX_facts step x result member
  have prog := facts inner innerMember
  refine ⟨by rw [baseEq]; exact prog.grows, slots, by rw [coreEq]; exact prog.accepts,
    fun other => by rw [coreEq]; exact prog.marks other,
    fun s c marked => prog.fresh s c (by rw [← coreEq]; exact marked), fun before marks active late => ?_⟩
  have early := prog.early before marks active (by rw [← coreEq]; exact late)
  rw [coreEq, baseEq]
  exact early

/-- The hidden Server install keeps the session counter, the pending tokens and the ideal backend. -/
theorem serverInstall_core
    (mid installed : (Option PqxdhServerRegistrationPublication.Response × Option PqxdhDeploymentIdealSlots.Coord) ×
      XState KemSK PqxdhDeploymentIdealSteps.SplitBk 2)
    (member : installed ∈ support (PqxdhDeploymentIdealDefer.serverInstall mid)) :
    installed.2.base.native.shared.2.sessions = mid.2.base.native.shared.2.sessions ∧
      installed.2.base.native.shared.2.pending = mid.2.base.native.shared.2.pending ∧
      installed.2.backend.2.2 = mid.2.backend.2.2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · unfold PqxdhDeploymentIdealDefer.serverInstall PqxdhDeploymentIdealDefer.xInstall at member
    split at member
    · rw [support_pure, Set.mem_singleton_iff] at member
      subst member
      rfl
    · split at member
      · rw [support_pure, Set.mem_singleton_iff] at member
        subst member
        rfl
      · split at member
        · rw [support_map] at member
          obtain ⟨_, _, rfl⟩ := member
          simp only [PqxdhDeploymentIdealKernel.buildApply, PqxdhDeploymentIdealKeys.attachX,
            PqxdhDeploymentIdealKeys.detachX, PqxdhDeploymentIdealKernel.peerFix]
          all_goals (split <;> rfl)
        · rw [support_pure, Set.mem_singleton_iff] at member
          subst member
          rfl

/-- The hidden Beacon install keeps the slot state and the ideal backend. -/
theorem beaconInstall_core (owner : ℕ)
    (mid installed : (Option Pqxdh.Bytes × Option PqxdhDeploymentIdealSlots.Coord) ×
      XState KemSK PqxdhDeploymentIdealSteps.SplitBk 2)
    (member : installed ∈ support (PqxdhDeploymentIdealDefer.beaconInstall owner mid)) :
    installed.2.backend = mid.2.backend := by
  unfold PqxdhDeploymentIdealDefer.beaconInstall PqxdhDeploymentIdealDefer.xInstall at member
  split at member
  · rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    rfl
  · split at member
    · rw [support_pure, Set.mem_singleton_iff] at member
      subst member
      rfl
    · split at member
      · rw [support_map] at member
        obtain ⟨_, _, rfl⟩ := member
        rfl
      · rw [support_pure, Set.mem_singleton_iff] at member
        subst member
        rfl

/-- Every query of the split handler moves the extended state as `StepFacts` says. -/
theorem step_facts (query : PqxdhDeploymentInterface.Spec.Domain) (x : XState KemSK PqxdhDeploymentIdealSteps.SplitBk 2)
    (result : PqxdhDeploymentInterface.Spec.Range query × XState KemSK PqxdhDeploymentIdealSteps.SplitBk 2)
    (member : result ∈ support ((PqxdhDeploymentBackend.handlerWith setup codec route
      (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created) query).run x)) :
    StepFacts t x result.2 := by
  have viaBase : ∀ q : PqxdhDeploymentInterface.Spec.Domain,
      (match q with
        | .inr (.create _ _) | .inr (.bundle _) | .inr (.accept _) | .inr (.build _ _) => False
        | _ => True) →
      ∀ r ∈ support ((PqxdhDeploymentBackend.onBase (PqxdhDeploymentNative.handler setup codec checks route
        created.seed q)).run x), StepFacts t x r.2 := by
    intro q kind r rMember
    have based := PqxdhDeploymentIdealCut.onBase_base (PqxdhDeploymentNative.handler setup codec checks route
      created.seed q) x
    have native : (r.1, r.2.base) ∈ support ((PqxdhDeploymentNative.handler setup codec checks route created.seed
        q).run x.base) := by
      rw [← based.1, support_map]
      exact ⟨r, rMember, rfl⟩
    obtain ⟨backend, seeds⟩ := based.2 r rMember
    obtain ⟨-, sessions, pending⟩ := PqxdhDeploymentHeadlineCtTrace.native_kept setup codec checks route created.seed q
      kind x.base _ native
    exact stepFacts_quiet t x r.2 (nativeHandler_grows setup codec checks route created.seed q x.base _ native) backend
      seeds sessions pending
  rcases query with coin | command
  · simp only [PqxdhDeploymentBackend.handlerWith, StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at member
    obtain ⟨_, _, rfl⟩ := member
    exact stepFacts_refl t x
  · cases command with
    | create pin keyId =>
        change result ∈ support ((PqxdhDeploymentIdealKeys.slotCoreX (PqxdhDeploymentIdealSteps.idealProg setup codec
          route checks t p (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks)) PqxdhDeploymentIdealKernel.lazyDummy
            created ⟨.create pin keyId, trivial⟩).run x) at member
        rw [PqxdhDeploymentIdealKernel.slotCoreX_run] at member
        exact stepFacts_slot t _ x result member fun inner innerMember =>
          createProg_facts setup codec checks route t p created _ pin keyId _ inner innerMember
    | bundle k =>
        change result ∈ support ((PqxdhDeploymentIdealKeys.slotCoreX (PqxdhDeploymentIdealSteps.idealProg setup codec
          route checks t p (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks)) PqxdhDeploymentIdealKernel.lazyDummy
            created ⟨.bundle k, trivial⟩).run x) at member
        rw [PqxdhDeploymentIdealKernel.slotCoreX_run] at member
        exact stepFacts_slot t _ x result member fun inner innerMember =>
          realQuiet_facts setup codec checks route t created ⟨.bundle k, trivial⟩ trivial _ inner innerMember
    | accept raw =>
        change result ∈ support ((PqxdhDeploymentIdealKeys.slotCoreX (PqxdhDeploymentIdealSteps.idealProg setup codec
          route checks t p (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks)) PqxdhDeploymentIdealKernel.lazyDummy
            created ⟨.accept raw, trivial⟩).run x) at member
        rw [PqxdhDeploymentIdealKernel.slotCoreX_run] at member
        exact stepFacts_slot t _ x result member fun inner innerMember =>
          acceptProg_facts setup codec checks route t p created raw _ inner innerMember
    | build session payload =>
        change result ∈ support ((fun r => (r.1.1, r.2)) <$> ((PqxdhDeploymentIdealKernel.slotRunX
          PqxdhDeploymentIdealKernel.lazyDummy (PqxdhDeploymentIdealKernel.buildStepC setup codec checks route
            (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks) created session payload)).run x >>=
              PqxdhDeploymentIdealDefer.serverInstall)) at member
        rw [support_map] at member
        obtain ⟨installed, installedMember, rfl⟩ := member
        rw [mem_support_bind_iff] at installedMember
        obtain ⟨mid, midMember, installMember⟩ := installedMember
        have before := stepFacts_slot t _ x mid midMember fun inner innerMember =>
          buildProg_facts setup codec checks route t created session payload _ inner innerMember
        obtain ⟨_, shared1, ctx, alloc, mat⟩ := PqxdhDeploymentHeadlineDctCommit.serverInstall_keeps mid installed
          installMember
        obtain ⟨sessions, pending, core⟩ := serverInstall_core mid installed installMember
        refine ⟨⟨fun u v found => ?_, fun i d found => ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
        · rw [shared1]; exact before.grows.1 u v found
        · rw [ctx]; exact before.grows.2 i d found
        · simp only [alloc, mat]
          exact ⟨before.slots.1, before.slots.2.1, before.slots.2.2.1, before.slots.2.2.2⟩
        · rw [core]; exact before.accepts
        · intro other; rw [core]; exact before.marks other
        · intro s c marked; rw [core] at marked; exact before.fresh s c marked
        · intro a m act late
          rw [core] at late
          obtain ⟨one, two, three, four⟩ := before.early a m act late
          refine ⟨by rw [core]; exact one, by rw [core]; exact two, by rw [sessions]; exact three, fun s found => ?_⟩
          rw [pending] at found
          rw [sessions]
          exact four s found
    | finish owner raw =>
        change result ∈ support ((fun r => (r.1.1, r.2)) <$> ((PqxdhDeploymentIdealKernel.slotRunX
          PqxdhDeploymentIdealKernel.lazyDummy (PqxdhDeploymentIdealKernel.finishStepC setup codec checks route t p
            (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks) created owner raw)).run x >>=
              PqxdhDeploymentIdealDefer.beaconInstall owner)) at member
        rw [support_map] at member
        obtain ⟨installed, installedMember, rfl⟩ := member
        rw [mem_support_bind_iff] at installedMember
        obtain ⟨mid, midMember, installMember⟩ := installedMember
        have before := stepFacts_slot t _ x mid midMember fun inner innerMember =>
          finishProg_facts setup codec checks route t p created owner raw _ inner innerMember
        obtain ⟨_, shared⟩ := PqxdhDeploymentHeadlineDctCommit.beaconInstall_keeps owner mid installed installMember
        have backend := beaconInstall_core owner mid installed installMember
        obtain ⟨allocEq, matEq, -⟩ := PqxdhDeploymentIdealDefer.xInstall_support _ _ _ mid installed installMember
        refine ⟨by rw [shared]; exact before.grows, ?_, by rw [backend]; exact before.accepts,
          fun other => by rw [backend]; exact before.marks other,
          fun s c marked => before.fresh s c (by rw [← backend]; exact marked), fun a m act late => ?_⟩
        · simp only [allocEq, matEq]
          exact ⟨before.slots.1, before.slots.2.1, before.slots.2.2.1, before.slots.2.2.2⟩
        · rw [backend] at late
          rw [backend, shared]
          exact before.early a m act late
    | hmac key message =>
        change result ∈ support ((PqxdhDeploymentIdealKeys.slotCoreX (PqxdhDeploymentIdealSteps.idealProg setup codec
          route checks t p (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks)) PqxdhDeploymentIdealKernel.lazyDummy
            created ⟨.hmac key message, trivial⟩).run x) at member
        rw [PqxdhDeploymentIdealKernel.slotCoreX_run] at member
        exact stepFacts_slot t _ x result member fun inner innerMember =>
          realQuiet_facts setup codec checks route t created ⟨.hmac key message, trivial⟩ trivial _ inner innerMember
    | hash bytes => exact viaBase (.inr (.hash bytes)) trivial result member
    | serverSend keyId plaintext => exact viaBase (.inr (.serverSend keyId plaintext)) trivial result member
    | serverRaw raw => exact viaBase (.inr (.serverRaw raw)) trivial result member
    | beaconSend owner plaintext => exact viaBase (.inr (.beaconSend owner plaintext)) trivial result member
    | beaconRaw owner raw => exact viaBase (.inr (.beaconRaw owner raw)) trivial result member

end Split

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.nGrows_refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.nGrows_refl

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.nGrows_trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.nGrows_trans

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.growsW_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.growsW_pure

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.growsW_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.growsW_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.growsW_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.growsW_coins

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.growsW_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.growsW_local

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.growsW_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.growsW_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.growsW_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.growsW_hash

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.growsW_sourceRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.growsW_sourceRoot

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.growsW_romRootBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.growsW_romRootBytes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.romImpl_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.romImpl_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.run_ctx_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.run_ctx_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.sharedImpl_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.sharedImpl_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.nativeTail_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.nativeTail_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.tailImpl_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.tailImpl_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.tailRun_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.tailRun_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.build_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.build_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.buildHidden_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.buildHidden_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.client_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.client_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.accept_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.accept_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.familyHmac_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.familyHmac_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.hmac_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.hmac_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.beaconNative_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.beaconNative_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.callbacks_growsW' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.callbacks_growsW

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.run_callbacks_growsW' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.run_callbacks_growsW

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.finish_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.finish_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.onShared_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.onShared_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.slotGrows_refl' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.slotGrows_refl

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.slotGrows_trans' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.slotGrows_trans

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.slotLazy_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.slotLazy_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.slotRun_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.slotRun_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.slotRunX_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.slotRunX_facts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.sharedNative_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.sharedNative_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.nativePrim_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.nativePrim_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.beaconLabels_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.beaconLabels_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.chainRaw_grows' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.chainRaw_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.finishErased_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.finishErased_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.slotRun_nGrows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.slotRun_nGrows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.hiddenAfter_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.hiddenAfter_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.groupCE_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.groupCE_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.finishChallenge_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.finishChallenge_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.tailCE_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.tailCE_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.opaqueTail_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.opaqueTail_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.acceptActive_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.acceptActive_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.acceptInactive_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.acceptInactive_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.acceptExposed_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.acceptExposed_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.tailCE_mark' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.tailCE_mark

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.acceptExposed_mark' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.acceptExposed_mark

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.serverStep_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.serverStep_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.beaconStep_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.beaconStep_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.nativeHandler_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.nativeHandler_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.progFacts_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.progFacts_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.realQuiet_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.realQuiet_facts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.createProg_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.createProg_facts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.acceptProg_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.acceptProg_facts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.realBuild_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.realBuild_facts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.buildProg_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.buildProg_facts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.finishProg_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.finishProg_facts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.stepFacts_refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.stepFacts_refl

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.stepFacts_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.stepFacts_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.stepFacts_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.stepFacts_slot

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.serverInstall_core' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.serverInstall_core

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.beaconInstall_core' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.beaconInstall_core

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.step_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep.step_facts
