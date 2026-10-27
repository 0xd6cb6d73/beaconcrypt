import BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor
import BeaconcryptCore.Computational.PqxdhPhase2LocalMatching
import BeaconcryptCore.Refinement.RatchetFuturePublication

/-! The complete Beacon registration tail through the same 108-byte factor. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor
open PqxdhServerAuthSendFactor (Kernel Factor Settled resolve)
open PqxdhSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedChain (Slot nativeKernel)

/-- A successful extracted pending-receive validation fits the exact cache window. -/
theorem pending_window (entry : Kernel) (pending : PendingReceive Slot RatchetMaterial)
    (requested : Std.U64) (valid : pending_receive_is_valid entry pending requested = ok true) :
    pending.first_slot.val + pending.skipped.val ≤ 50 := by
  simp only [pending_receive_is_valid, control.RatchetState.impl.receive_sequence,
    control.RatchetState.impl.send_sequence, control.RatchetState.receive_cache_len,
    lift, bind_tc_ok] at valid
  by_contra bound
  obtain ⟨committed, added, value⟩ := control.uscalar_add_eq_ok
    (UScalar.cast .Usize pending.first_slot) (UScalar.cast .Usize pending.skipped) (by scalar_tac)
  have greater : committed > UScalar.cast .Usize 50#u64 := by scalar_tac
  simp only [added, control.capacity_eq_ok, bind_tc_ok, greater, ite_true] at valid
  simp only [ite_self, Bind.bind, Aeneas.Std.bind] at valid
  repeat' split at valid
  all_goals cases valid

/-- An empty logical receive cache cannot select a cached opening. -/
theorem no_cached (entry : Kernel) (empty : entry.control.receive_cache.len.val = 0)
    (sequence : Std.U64) : prepare_cached_receive entry sequence = ok .None := by
  obtain ⟨reply, prepared⟩ := prepare_cached_receive_total entry sequence
  cases reply with
  | none => exact prepared
  | some cached =>
      have live := (prepare_cached_receive_success_inv entry sequence cached prepared).target_live
      simp only [empty] at live
      exact False.elim (Nat.not_lt_zero _ live)

def KnownSend (entry : Kernel) : Prop := ∃ chain, entry.send_chain = .known chain

/-- Any reached opening has a known final receive chain and the validated cache window. -/
def ReadyOpening {Context : Type}
    (opening : RawCtxInterpretedOpening.Opening Slot Slot RatchetMaterial Context) : Prop :=
  KnownSend opening.entry ∧ match opening.prepared with
    | .PreparedReceiveCachedCase _ => False
    | .PreparedReceiveFutureCase pending =>
      (∃ chain, pending.final_receive_chain = .known chain) ∧
        pending.first_slot.val + pending.skipped.val ≤ 50

def ReadyEffect {Context : Type} : RawCtxChainReceive.Effect Slot Slot RatchetMaterial Context → Prop
  | .rejected _ _ => True
  | .kdfRequested pending => KnownSend pending.entry
  | .openRequested opening => ReadyOpening opening

/-- Every KDF response marks its next chain known. The actual receive driver therefore
reaches only future openings with known chains, while retaining its original rollback entry. -/
theorem resume_ready {Context : Type}
    (pending : RawCtxChainReceive.Kdf Slot Slot RatchetMaterial Context)
    (send : KnownSend pending.entry) (reply : Slot × RatchetMaterial)
    (next : ∃ chain, reply.1 = .known chain) :
    ReadyEffect (RawCtxChainReceive.normalResume pending reply) := by
  have resumed := RawCtxChainReceive.normalResume_exact pending reply
  simp only [RawCtxChainReceive.resume, RawCtxChainReceive.rejected, Bind.bind, Aeneas.Std.bind] at resumed
  repeat' split at resumed
  all_goals simp only [RustM.ok.injEq, reduceCtorEq] at resumed
  all_goals rw [← resumed]
  all_goals simp only [ReadyEffect, ReadyOpening, KnownSend] at *
  all_goals first | exact send | refine ⟨send, next, ?_⟩
  rename_i valid trueReply
  exact pending_window pending.entry _ pending.target (valid.trans (congrArg RustM.ok trueReply))

/-- Initial receive admission cannot take the cached path; every admitted future path
retains the known send chain before its first hidden-chain KDF query. -/
theorem begin_ready {Context : Type} (entry : Kernel) (target : Std.U64) (context : Context)
    (send : KnownSend entry) (empty : entry.control.receive_cache.len.val = 0) :
    ReadyEffect (RawCtxChainReceive.normalBegin entry target context) := by
  have begun := RawCtxChainReceive.normalBegin_exact entry target context
  simp only [RawCtxChainReceive.beginReceive, no_cached entry empty,
    RawCtxChainReceive.rejected, Bind.bind, Aeneas.Std.bind] at begun
  repeat' split at begun
  all_goals simp only [RustM.ok.injEq, reduceCtorEq] at begun
  all_goals rw [← begun]
  all_goals simp only [ReadyEffect]
  exact send

/-- A successful opening publishes both known chains; the checked cache window rules
out the extracted publisher's invalid-window fallback. -/
theorem finish_ready {Context Plaintext : Type}
    (opening : RawCtxInterpretedOpening.Opening Slot Slot RatchetMaterial Context)
    (ready : ReadyOpening opening) (plaintext : Plaintext) :
    Settled (RawCtxChainReceive.normalFinish opening (.Some plaintext)).1 := by
  obtain ⟨send, future⟩ := ready
  cases prepared : opening.prepared with
  | PreparedReceiveCachedCase cached => simp only [prepared] at future
  | PreparedReceiveFutureCase pending =>
      simp only [prepared] at future
      obtain ⟨next, window⟩ := future
      obtain ⟨published, publishedEq, _, sendEq, receiveEq, _⟩ :=
        publish_future_receive_exact opening.entry pending window
      have finished := RawCtxChainReceive.normalFinish_exact opening (.Some plaintext)
      simp only [RawCtxInterpretedOpening.finish, prepared, publishedEq, bind_tc_ok] at finished
      rw [← RustM.ok.inj finished]
      obtain ⟨sendChain, sendKnown⟩ := send
      obtain ⟨receiveChain, receiveKnown⟩ := next
      exact ⟨⟨sendChain, sendEq.trans sendKnown⟩, ⟨receiveChain, receiveEq.trans receiveKnown⟩⟩

section General
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Private chain labels pass the actual opening arguments to the supplied primitive
interpreter; their unused chain fields are filled only inside the source adapter. -/
noncomputable def primLabels (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (source : FixedHkdfSha512NoSaltSource) (challenge : RatchetKdfResponse) :
    QueryImpl (RawCtxChainReceive.ReceiveSpec Slot Slot RatchetMaterial
      RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted) m
  | .inl slot => pure (RawCtxSelectedChain.step source challenge slot)
  | .inr pending => (prim ∘ₛ RawCtxWholeOwner.adapter) (.inr (RawCtxInterpretedOpening.toNative
      (RawCtxChainInterpretation.mapOpeningChains (fun _ => RawCtxSelectedChain.unusedChain)
        (fun _ => RawCtxSelectedChain.unusedChain) pending)))

/-- Observing a completed receive through a callback that ignores a failed kernel
needs no hidden chain. All primitive state effects remain in the same computation. -/
theorem program_settlement {Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (challenge : RatchetKdfResponse) (chain : RatchetChain)
    (observe : ConcreteRatchetKernel → core.option.Option RawCtxWholeOwner.Decrypted → Result)
    (failure : ∀ first second, observe first .None = observe second .None)
    (effect : RawCtxChainReceive.Effect Slot Slot RatchetMaterial RawCtxWholeOwner.OpenContext)
    (ready : ReadyEffect effect) :
    (fun result => observe (nativeKernel chain result.1) result.2) <$>
        simulateQ (primLabels prim source challenge)
          (RawCtxChainReceive.program effect) =
      (fun result => observe (resolve result.1) result.2) <$>
        simulateQ (primLabels prim source challenge)
          (RawCtxChainReceive.program effect) := by
  generalize ranked : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
      cases effect with
      | kdfRequested pending =>
          simp only [RawCtxChainReceive.program, simulateQ_bind, simulateQ_spec_query,
            primLabels, pure_bind]
          exact ih _ (ranked ▸ RawCtxChainReceive.normalResume_rank pending
            (RawCtxSelectedChain.step source challenge pending.request)) _
              (resume_ready pending ready _ ⟨_, rfl⟩) rfl
      | rejected entry context =>
          simp only [RawCtxChainReceive.program, simulateQ_pure, map_pure]
          exact congrArg pure (failure _ _)
      | openRequested opening =>
          simp only [RawCtxChainReceive.program, simulateQ_bind, simulateQ_spec_query,
            simulateQ_pure, map_bind, map_pure]
          refine bind_congr fun reply => ?_
          cases reply with
          | none =>
              have failed := RawCtxChainReceive.normalFinish_exact opening
                (core.option.Option.None : core.option.Option RawCtxWholeOwner.Decrypted)
              change ok (opening.entry, core.option.Option.None) = _ at failed
              rw [← RustM.ok.inj failed]
              exact congrArg pure (failure _ _)
          | some plaintext =>
              rw [PqxdhServerAuthSendFactor.settled_native chain _ (finish_ready opening ready plaintext)]

/-- The local Beacon owner calls receive only; its send implementation remains arbitrary. -/
noncomputable def primCalls
    (sendCall : Kernel → RawCtxSourceSend.SealContext → m (Kernel × Option RawCtxSourceSend.Encrypted))
    (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (source : FixedHkdfSha512NoSaltSource) (challenge : RatchetKdfResponse) : RawCtxChainOwner.Calls Kernel m :=
  { receive := fun entry target context => simulateQ (primLabels prim source challenge)
      (RawCtxChainReceive.execute entry target context)
    send := sendCall }

/-- The raw owner retains parser and frame-validation rejection and all primitive effects
before the same failure-insensitive observation of the kernel. -/
theorem raw_settlement {Metadata Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (sendCall : Kernel → RawCtxSourceSend.SealContext → m (Kernel × Option RawCtxSourceSend.Encrypted))
    (challenge : RatchetKdfResponse) (chain : RatchetChain)
    (observe : ConcreteRatchetKernel → core.option.Option RawCtxWholeOwner.Decrypted → Result)
    (failure : ∀ first second, observe first .None = observe second .None)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxChainOwner.State Kernel Metadata)
    (send : KnownSend state.kernel) (empty : state.kernel.control.receive_cache.len.val = 0) :
    (fun result => observe (nativeKernel chain result.2.kernel) result.1) <$>
        (RawCtxChainOwner.rawReceive (primCalls sendCall prim source challenge)
          decode raw).run state =
      (fun result => observe (resolve result.2.kernel) result.1) <$>
        (RawCtxChainOwner.rawReceive (primCalls sendCall prim source challenge)
          decode raw).run state := by
  simp only [RawCtxChainOwner.rawReceive, StateT.run]
  by_cases blank : raw.isEmpty = true
  · simp only [blank, ite_true, map_pure, RawCtxChainOwner.publish]
    exact congrArg pure (failure _ _)
  · simp only [blank, Bool.false_eq_true, ite_false]
    cases decoded : decode raw with
    | none =>
        simp only [map_pure, RawCtxChainOwner.publish]
        exact congrArg pure (failure _ _)
    | some frame =>
        by_cases valid : RawCtxReceive.ValidFrame state.expectedSender state.associatedData frame
        · simp only [valid, ite_true, map_bind, map_pure, RawCtxChainOwner.publish,
            primCalls, RawCtxChainReceive.execute]
          simpa only [bind_pure_comp] using program_settlement source prim challenge chain observe failure
            _ (begin_ready state.kernel frame.sequence ⟨raw, frame, state.associatedData⟩ send empty)
        · simp only [valid, ite_false, map_pure, RawCtxChainOwner.publish]
          exact congrArg pure (failure _ _)

/-- Arbitrary primitive effects realize the complete labelled receive when the KDF
callback is the real source. Opening arguments cannot read the omitted chain fields. -/
theorem primitive_receive (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (source : FixedHkdfSha512NoSaltSource)
    (kdf : ∀ request, prim (.inl request) = pure (RawCtxSourceHkdf.response source.crypto request))
    (target : RatchetChain) (entry : Kernel) (requested : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    simulateQ (prim ∘ₛ RawCtxWholeOwner.adapter)
        (RawCtxOwnerOracle.receive (nativeKernel target entry) requested context) =
      (fun result => (nativeKernel target result.1, result.2)) <$>
        simulateQ (primLabels prim source
          (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target)))
          (RawCtxChainReceive.execute entry requested context) := by
  rw [nativeKernel, RawCtxInterpretedReceive.receive_native, simulateQ_map, ← QueryImpl.simulateQ_compose]
  have mapped := RawCtxChainReceive.execute_native (RawCtxSelectedChain.interpret target)
    (RawCtxSelectedChain.interpret target)
    (primLabels prim source (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target)))
    ((prim ∘ₛ RawCtxWholeOwner.adapter) ∘ₛ RawCtxInterpretedReceive.nativeAdapter)
    ?_ ?_ entry requested context
  · simpa only [Functor.map_map, nativeKernel] using congrArg
      (fun work => (fun result => (ConcreteRatchetKernel.mk result.1, result.2)) <$> work) mapped
  · intro request
    simp only [QueryImpl.apply_compose, RawCtxInterpretedReceive.nativeAdapter,
      simulateQ_map, simulateQ_spec_query, RawCtxWholeOwner.adapter, kdf, map_pure,
      primLabels, RawCtxSelectedChain.step_source]
    rfl
  · intro opening
    simp only [QueryImpl.apply_compose, RawCtxInterpretedReceive.nativeAdapter,
      simulateQ_spec_query, primLabels]
    exact congrArg (simulateQ prim) (RawCtxChainOpeningArguments.adapter_chains
      (RawCtxSelectedChain.interpret target) (fun _ => RawCtxSelectedChain.unusedChain)
      (RawCtxSelectedChain.interpret target) (fun _ => RawCtxSelectedChain.unusedChain) opening)

end General

/-- The actual empty Beacon initializer with its receive chain represented by the private slot. -/
def initial (other : RootOutput) : Kernel :=
  { control := ⟨0#u64, 0#u64, ⟨Std.Array.repeat 50#usize 0#u64, 0#u8⟩⟩
    send_chain := .known (RawCtxFreshChainCut.concreteChain other)
    receive_chain := .hidden
    receive_slots := Std.Array.repeat 50#usize .None }

/-- This constructor is the complete extracted initial result, not a replacement state. -/
theorem initial_exact (other : RootOutput) :
    RawCtxSelectedInitialConstructor.initial true other = ok (initial other) := rfl

/-- The actual deterministic initial callback installs the interpreted placeholder state. -/
theorem initial_source (source : FixedHkdfSha512NoSaltSource) (root : RootOutput) :
    PqxdhBeaconPhase2Publication.normalInitial
        (PqxdhInitialRatchetComplementarity.beaconPending (PqxdhRootTableInitialization.rootArray root))
        (RawCtxSourceHkdf.initialResponse source.crypto
          (PqxdhInitialRatchetComplementarity.beaconPending (PqxdhRootTableInitialization.rootArray root)).request) =
      nativeKernel (RawCtxFreshChainCut.concreteChain (PqxdhServerAuthSendFactor.target source root))
        (initial (PqxdhServerAuthSendFactor.other source root)) := by
  have factored := PqxdhServerAuthSendFactor.initial_factor_beacon source root
  rw [initial_exact] at factored
  have native := PqxdhBeaconPhase2Publication.normalInitial_exact
    (PqxdhInitialRatchetComplementarity.beaconPending (PqxdhRootTableInitialization.rootArray root))
    (RawCtxSourceHkdf.initialResponse source.crypto
      (PqxdhInitialRatchetComplementarity.beaconPending (PqxdhRootTableInitialization.rootArray root)).request)
  simp only [PqxdhRootTableInitialization.initialKernelRun, ite_true,
    BeaconcryptCore.Refinement.PqxdhConcreteSession.initializeBeacon_eq] at factored
  exact RustM.ok.inj (native.symm.trans factored)

/-- The source mixed receive adapter is exactly the native opening adapter on the same cache. -/
theorem receive_adapter {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    RawCtxSourceMaterialLabels.nativeImpl (Auxiliary := A) source writer ∘ₛ RawCtxMixedOwner.receiveAdapter =
      RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source) ∘ₛ
        RawCtxSourceOpen.nativeAdapter := by
  funext query
  simp only [RawCtxSourceMaterialLabels.nativeImpl, RawCtxMixedOwner.receiveAdapter, QueryImpl.compose]
  rw [← QueryImpl.simulateQ_compose, RawCtxMixedShared.shared_receive]

/-- The local owner's complete initial metadata and attempt counter. -/
def localState (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : Kernel) :
    RawCtxChainOwner.State Kernel Unit :=
  ⟨kernel, candidate.server_binding.identity_key_id, absBytes candidate.associated_data, (), 0⟩

section Tail
variable {m : Type → Type} [Monad m] [LawfulMonad m] {Response : Type}

/-- The post-root primitive interpreter, with real initial HKDF and an arbitrary
application getter. The root callback is not reached by the post-root program. -/
def sourceTail (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (source : FixedHkdfSha512NoSaltSource) (application : Response → m (Option Pqxdh.Bytes)) :
    QueryImpl (PqxdhBeaconPhase2Publication.TailSpec Response) m
  | .inl query => prim query
  | .inr (.root _) => pure none
  | .inr (.initial request) => pure (RawCtxSourceHkdf.initialResponse source.crypto request)
  | .inr (.application response) => application response

/-- The Beacon tail consumes the same 108-byte factor and the cleared metadata.
All application, raw receive, sequence-one and binding checks retain their order. -/
noncomputable def factored (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (sendCall : Kernel → RawCtxSourceSend.SealContext → m (Kernel × Option RawCtxSourceSend.Encrypted))
    (source : FixedHkdfSha512NoSaltSource) (application : Response → m (Option Pqxdh.Bytes))
    (decode : RawCtxReceive.FrameDecoder) (prepared : PqxdhBeaconPhase2Preparation.Prepared Response)
    (value : Factor) : m (Option PqxdhBeaconPhase2Publication.Staged) := do
  let candidate := PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate
  let raw ← application prepared.response
  match raw with
  | none => pure none
  | some raw => do
      let result ← (RawCtxChainOwner.rawReceive (primCalls sendCall prim source value.1) decode raw).run
        (localState candidate (initial value.2))
      pure (PqxdhBeaconPhase2Publication.afterOpening candidate (resolve result.2.kernel) result.1)

/-- Exact post-root factorization for any complete primitive interpreter satisfying
its real KDF callback contract; no callback state or failure effect is dropped. -/
theorem primitive_factor (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (sendCall : Kernel → RawCtxSourceSend.SealContext → m (Kernel × Option RawCtxSourceSend.Encrypted))
    (source : FixedHkdfSha512NoSaltSource) (application : Response → m (Option Pqxdh.Bytes))
    (kdf : ∀ request, prim (.inl request) = pure (RawCtxSourceHkdf.response source.crypto request))
    (decode : RawCtxReceive.FrameDecoder) (prepared : PqxdhBeaconPhase2Preparation.Prepared Response)
    (root : RootOutput) :
    simulateQ (sourceTail prim source application)
        (PqxdhBeaconPhase2Publication.afterRoot decode prepared (PqxdhRootTableInitialization.rootArray root)) =
      factored prim sendCall source application decode prepared (PqxdhServerAuthSendFactor.factor source root) := by
  simp only [PqxdhBeaconPhase2Publication.afterRoot, PqxdhBeaconPhase2Publication.initialRun,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, sourceTail, pure_bind, initial_source, factored]
  refine bind_congr fun raw => ?_
  cases raw with
  | none => rfl
  | some raw =>
      have lifted : sourceTail prim source application ∘ₛ PqxdhBeaconPhase2Publication.rawLift = prim := by
        funext query
        simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Publication.rawLift,
          simulateQ_spec_query, sourceTail]
      simp only [simulateQ_bind, simulateQ_pure, ← QueryImpl.simulateQ_compose, lifted]
      rw [show PqxdhBeaconPhase2Publication.localOwner
          (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate)
          (nativeKernel (RawCtxFreshChainCut.concreteChain (PqxdhServerAuthSendFactor.target source root))
            (initial (PqxdhServerAuthSendFactor.other source root))) =
          RawCtxChainOwner.nativeState
            (nativeKernel (RawCtxFreshChainCut.concreteChain (PqxdhServerAuthSendFactor.target source root)))
            (localState (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate)
              (initial (PqxdhServerAuthSendFactor.other source root))) from rfl,
        RawCtxChainOwner.rawReceive_native _
          (primCalls sendCall prim source (PqxdhServerAuthSendFactor.factor source root).1) prim
          (primitive_receive prim source kdf _)]
      simpa only [bind_map_left, bind_pure_comp, Functor.map_map, Prod.map_fst, Prod.map_snd,
        RawCtxChainOwner.nativeState, Function.comp_def, id_eq, PqxdhServerAuthSendFactor.factor] using
        raw_settlement source prim sendCall (PqxdhServerAuthSendFactor.factor source root).1
          (RawCtxFreshChainCut.concreteChain (PqxdhServerAuthSendFactor.target source root))
          (PqxdhBeaconPhase2Publication.afterOpening
            (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate))
          (fun _ _ => rfl) decode raw
          (localState (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate)
            (initial (PqxdhServerAuthSendFactor.other source root))) ⟨_, rfl⟩ rfl

end Tail

open PqxdhServerAuthExperiment

/-- The actual raw receive primitive interpreter, on the experiment's complete CTX cache. -/
noncomputable def nativePrim {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : Setup baseSpec KemSK) (_codec : Codec Reader Response) :
    QueryImpl RawCtxWholeOwner.PrimitiveSpec
      (StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp) :=
  RawCtxSharedPrimitive.nativeImpl setup.source.crypto (RawCtxSourceHkdf.kdfImpl setup.source) ∘ₛ
    RawCtxSourceOpen.nativeAdapter

/-- Expanding the actual Beacon tail adapter yields exactly the primitive-level tail. -/
theorem native_tail {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    beaconNative setup codec ∘ₛ PqxdhBeaconPhase2Publication.nativeTailAdapter =
      sourceTail (nativePrim setup codec) setup.source (fun response => pure (codec.application response)) := by
  funext query
  cases query with
  | inl query =>
      simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Publication.nativeTailAdapter,
        sourceTail, nativePrim]
      have lifted : beaconNative setup codec ∘ₛ PqxdhBeaconPhase2Publication.nativeRawLift =
          RawCtxSharedPrimitive.nativeImpl setup.source.crypto (RawCtxSourceHkdf.kdfImpl setup.source) := by
        funext request
        simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Publication.nativeRawLift,
          simulateQ_spec_query, beaconNative]
      rw [← QueryImpl.simulateQ_compose, lifted]
  | inr query =>
      cases query <;> simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Publication.nativeTailAdapter,
        simulateQ_spec_query, beaconNative, sourceTail]

/-- The actual primitive interpreter supplies the real public ratchet KDF. -/
theorem native_kdf {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (request : SymmetricRatchetKdfRequest) :
    nativePrim setup codec (.inl request) = pure (RawCtxSourceHkdf.response setup.source.crypto request) := by
  simp only [nativePrim, QueryImpl.apply_compose, RawCtxSourceOpen.nativeAdapter,
    simulateQ_spec_query]
  change RawCtxSourceHkdf.kdfImpl setup.source request = _
  funext state
  exact RawCtxSourceHkdf.kdf_step setup.source request state

/-- The actual cleared Beacon continuation retains its complete staged result and every
primitive effect while consuming only the source 108-byte factor. -/
theorem beacon_afterRoot_factor {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (sendCall : Kernel → RawCtxSourceSend.SealContext →
      StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp (Kernel × Option RawCtxSourceSend.Encrypted))
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (root : RootOutput) :
    simulateQ (beaconNative setup codec)
        (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending (PqxdhRootTableInitialization.rootArray root)) =
      factored (nativePrim setup codec) sendCall setup.source (fun response => pure (codec.application response))
        codec.frameRead (PqxdhPhase2DhRootConsumer.cleared pending) (PqxdhServerAuthSendFactor.factor setup.source root) := by
  rw [PqxdhPhase2DhRootConsumer.afterRoot, ← QueryImpl.simulateQ_compose, native_tail]
  exact primitive_factor (nativePrim setup codec) sendCall setup.source _ (native_kdf setup codec) _ _ root

/-- Evaluating on any reached cache preserves its full distribution with the staged result. -/
theorem beacon_afterRoot_run {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (sendCall : Kernel → RawCtxSourceSend.SealContext →
      StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp (Kernel × Option RawCtxSourceSend.Encrypted))
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (root : RootOutput)
    (state : RawCtxSharedPrimitive.SharedState Unit) :
    (simulateQ (beaconNative setup codec)
        (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending (PqxdhRootTableInitialization.rootArray root))).run state =
      (factored (nativePrim setup codec) sendCall setup.source (fun response => pure (codec.application response))
        codec.frameRead (PqxdhPhase2DhRootConsumer.cleared pending) (PqxdhServerAuthSendFactor.factor setup.source root)).run state := by
  rw [beacon_afterRoot_factor setup codec sendCall]

end BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.pending_window' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.pending_window
/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.no_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.no_cached
/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.resume_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.resume_ready
/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.begin_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.begin_ready
/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.finish_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.finish_ready
/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.program_settlement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.program_settlement
/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.raw_settlement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.raw_settlement
/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.primitive_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.primitive_receive
/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.initial_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.initial_exact
/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.initial_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.initial_source
/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.receive_adapter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.receive_adapter
/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.primitive_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.primitive_factor
/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.native_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.native_tail
/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.native_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.native_kdf
/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.beacon_afterRoot_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.beacon_afterRoot_factor
/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.beacon_afterRoot_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor.beacon_afterRoot_run
