import BeaconcryptCore.Computational.PqxdhInitialGenericBuilder
import BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor

/-!
The Server registration build uses a root through a 108-byte value: the complete
76-byte response for its initial sending chain and the 32-byte initial receiving
chain. `server_send_factor` preserves the complete computation, including the
Server state, auxiliary effects, rejection branches, writer and shared CTX cache.
The root-free continuation resolves hidden chain slots only after proving that
every published kernel has both chains known.

This ports the checked Milestone B Server-send spike. The build follows
`beaconcrypt/src/server.rs:424-499` through the existing model and its extracted
preparation/commit operations. Serialization stays an arbitrary writer under the
approved message model; no serialization implementation is modeled here.
`prim_send_source` also handles an arbitrary seal interpreter, so later stages
can retain the authentication experiment's seal log. The two Beacon lemmas
preserve its initializer and receive computation but still interpret its hidden
chain; whole-game factorization and Beacon settlement are separate obligations.

This is a functional equality with no new security premise, primitive reduction,
query-count claim or global authentication conclusion. Public KDF evaluations
remain the source evaluations. No new random-oracle replacement occurs here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthSendFactor
open PqxdhServerRegistrationPublication (AuxSpec Response TailSpec registrationWitness)
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open RawCtxChainInterpretation
open RawCtxSelectedChain (Slot nativeKernel)

abbrev Kernel := RawCtxSelectedChain.Kernel

/-- The 108-byte image: the complete 76-byte step response on chain_0 and the Server receive chain. -/
abbrev Factor := RatchetKdfResponse × RootOutput

/-- The fixed 76-byte stream address of the initializer for a root. -/
def address (root : RootOutput) : JointKdfAddress :=
  RawCtxKdfRequestTable.address ⟨PqxdhRootTableInitialization.rootArray root, ratchet.SYM_RATCHET_INFO⟩

/-- chain_0 = first32 init (Server send chain). -/
def target (source : FixedHkdfSha512NoSaltSource) (root : RootOutput) : RootOutput :=
  JointKdfProjection.first32.project (productionStream source.crypto (address root))

/-- second32 init (Server receive chain). -/
def other (source : FixedHkdfSha512NoSaltSource) (root : RootOutput) : RootOutput :=
  (RawCtxSelectedInitialEntry.fromOutput (address root) (productionStream source.crypto (address root))).otherChain

/-- `f`: the only root-dependent value the Server-send half consumes. -/
def factor (source : FixedHkdfSha512NoSaltSource) (root : RootOutput) : Factor :=
  (RawCtxSourceHkdf.response source.crypto
      (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain (target source root))),
    other source root)

/-! ### Placeholder kernels -/

/-- Existing concrete peers enter the labelled state with both chains known. -/
def known (kernel : ConcreteRatchetKernel) : Kernel :=
  mapChains Slot.known Slot.known kernel.refined

theorem native_known (chain : RatchetChain) (kernel : ConcreteRatchetKernel) :
    nativeKernel chain (known kernel) = kernel := rfl

/-- Target-free interpretation (hidden slots, if any, get an unused chain). -/
def resolve : Kernel → ConcreteRatchetKernel := nativeKernel RawCtxSelectedChain.unusedChain

def Settled (kernel : Kernel) : Prop :=
  (∃ chain, kernel.send_chain = .known chain) ∧ ∃ chain, kernel.receive_chain = .known chain

theorem settled_native (chain : RatchetChain) (kernel : Kernel) (settled : Settled kernel) :
    nativeKernel chain kernel = resolve kernel := by
  obtain ⟨⟨send, hsend⟩, ⟨receive, hreceive⟩⟩ := settled
  simp only [resolve, nativeKernel, mapChains, hsend, hreceive, RawCtxSelectedChain.interpret]

section States
variable {Metadata PeerMetadata Consumed : Type}

def embed (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed :=
  ⟨⟨state.server.identity, fun kid => (state.server.peers kid).map
      (fun peer => ⟨peer.identity, known peer.kernel, peer.metadata⟩), state.server.metadata⟩,
    state.identityKeyId, state.control, state.consumed⟩

theorem native_embed (chain : RatchetChain)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    PqxdhInitialGenericPublication.native (nativeKernel chain) (embed state) = state := by
  rcases state with ⟨⟨identity, peers, metadata⟩, identityKeyId, control, consumed⟩
  simp only [PqxdhInitialGenericPublication.native, embed, RawCtxGenericRoleStorage.nativeServer,
    Option.map_map, Function.comp_def, native_known]
  congr
  funext kid
  cases peers kid <;> rfl

def StateSettled (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed) : Prop :=
  ∀ kid peer, state.server.peers kid = some peer → Settled peer.kernel

theorem embed_settled (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    StateSettled (embed state) := by
  intro kid peer found
  simp only [embed, Option.map_eq_some_iff] at found
  obtain ⟨original, _, rfl⟩ := found
  exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

theorem native_settled (chain : RatchetChain)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (settled : StateSettled state) :
    PqxdhInitialGenericPublication.native (nativeKernel chain) state =
      PqxdhInitialGenericPublication.native resolve state := by
  rcases state with ⟨⟨identity, peers, metadata⟩, identityKeyId, control, consumed⟩
  simp only [PqxdhInitialGenericPublication.native, RawCtxGenericRoleStorage.nativeServer]
  congr
  funext kid
  cases found : peers kid with
  | none => rfl
  | some peer =>
      simp only [Option.map_some]
      rw [settled_native chain peer.kernel (settled kid peer found)]

theorem publish_settled
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (settled : StateSettled state) (candidate : pqxdh.ServerRegistrationCandidate)
    (kernel : Kernel) (fresh : Settled kernel) (metadata : PeerMetadata) :
    StateSettled (PqxdhInitialGenericPublication.publish state candidate kernel metadata) := by
  intro kid peer found
  simp only [PqxdhInitialGenericPublication.publish] at found
  by_cases same : kid = candidate.key_id
  · subst same
    simp only [Function.update_self, Option.some.injEq] at found
    subst found
    exact fresh
  · rw [Function.update_of_ne same] at found
    exact settled kid peer found

end States

/-! ### Initializer placeholder -/

/-- The actual 64-byte initializer is the hidden-send constructor with the factor's second half. -/
theorem initial_factor (source : FixedHkdfSha512NoSaltSource) (root : RootOutput) :
    PqxdhRootTableInitialization.initialKernelRun source false root =
      nativeKernel (RawCtxFreshChainCut.concreteChain (target source root)) <$>
        RawCtxSelectedInitialConstructor.initial false (other source root) :=
  RawCtxSelectedInitialConstructor.source_initial source (false, PqxdhRootTableInitialization.rootArray root)


/-! ### Build with a supplied initializer, and its generic-kernel form -/

section Build
variable {Metadata PeerMetadata Consumed : Type}

/-- Plain `build`, cut at the initializer result. -/
noncomputable def cutBuild (initial : RustM ConcreteRatchetKernel) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    OracleComp TailSpec
      (RustM (Option Response × PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)) :=
  PqxdhServerRegistrationPublication.continueRust (pqxdh.server_next_key_id state.control) fun next =>
    match next with
    | .Err _ => pure (ok (none, state))
    | .Ok next =>
        let availability := if (state.server.peers next).isSome then
          pqxdh.KeyIdAvailability.Occupied else .Available
        PqxdhServerRegistrationPublication.continueRust (pqxdh.server_prepare_commit state.control pending
          ⟨state.server.identity, state.identityKeyId⟩ availability) fun prepared =>
          match prepared with
          | .Err _ => pure (ok (none, state))
          | .Ok candidate => PqxdhInitialBuilderCut.candidate initial candidate data metadata state

theorem cut_source (source : FixedHkdfSha512NoSaltSource) (pending : pqxdh.PendingServerRegistration)
    (root : RootOutput) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    cutBuild (PqxdhRootTableInitialization.initialKernelRun source false root) pending data metadata state =
      PqxdhServerRegistrationPublication.build source pending root data metadata state := by
  unfold cutBuild
  simp only [PqxdhInitialBuilderCut.candidate_source]
  rfl

variable {K : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

/-- The same gates over an abstract kernel representation. -/
noncomputable def genericBuild (calls : RawCtxChainOwner.Calls K m) (aux : QueryImpl AuxSpec m)
    (initial : RustM K) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed) :
    m (RustM (Option Response × PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed)) :=
  PqxdhInitialGenericBuilder.continueRust (pqxdh.server_next_key_id state.control) fun next =>
    match next with
    | .Err _ => pure (ok (none, state))
    | .Ok next =>
        let availability := if (state.server.peers next).isSome then
          pqxdh.KeyIdAvailability.Occupied else .Available
        PqxdhInitialGenericBuilder.continueRust (pqxdh.server_prepare_commit state.control pending
          ⟨state.server.identity, state.identityKeyId⟩ availability) fun prepared =>
          match prepared with
          | .Err _ => pure (ok (none, state))
          | .Ok candidate => PqxdhInitialGenericBuilder.candidate calls aux initial candidate data metadata state

open PqxdhInitialGenericPublication in
/-- `used_native` for the plain pending registration. -/
theorem build_native (interpret : K → ConcreteRatchetKernel)
    (calls : RawCtxChainOwner.Calls K m) (backend : QueryImpl RawCtxMixedOwner.NativeSpec m)
    (aux : QueryImpl AuxSpec m)
    (sendRealized : ∀ entry context,
      simulateQ ((backend ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
        (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (initial : RustM K) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State K Metadata PeerMetadata Consumed) :
    simulateQ (nativeImpl backend aux)
      (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
        (cutBuild (interpret <$> initial) pending data metadata (native interpret state))) =
      Functor.map (Prod.map id (native interpret)) <$> genericBuild calls aux initial pending data metadata state := by
  unfold cutBuild genericBuild
  change simulateQ (nativeImpl backend aux) (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
    (PqxdhServerRegistrationPublication.continueRust (pqxdh.server_next_key_id state.control) _)) = _
  cases next : pqxdh.server_next_key_id state.control with
  | fail error => simp only [PqxdhServerRegistrationPublication.continueRust, PqxdhInitialGenericBuilder.continueRust, simulateQ_pure, map_pure]; rfl
  | div => simp only [PqxdhServerRegistrationPublication.continueRust, PqxdhInitialGenericBuilder.continueRust, simulateQ_pure, map_pure]; rfl
  | ok result =>
      cases result with
      | Err error => simp only [PqxdhServerRegistrationPublication.continueRust, PqxdhInitialGenericBuilder.continueRust, simulateQ_pure, map_pure]; rfl
      | Ok key =>
          simp only [PqxdhServerRegistrationPublication.continueRust, PqxdhInitialGenericBuilder.continueRust]
          have preparation :
              pqxdh.server_prepare_commit (native interpret state).control pending
                ⟨(native interpret state).server.identity, (native interpret state).identityKeyId⟩
                (if ((native interpret state).server.peers key).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) =
              pqxdh.server_prepare_commit state.control pending ⟨state.server.identity, state.identityKeyId⟩
                (if (state.server.peers key).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) := by
            simp only [native, RawCtxGenericRoleStorage.nativeServer, Option.isSome_map]
          rw [preparation]
          cases prepared : pqxdh.server_prepare_commit state.control pending ⟨state.server.identity, state.identityKeyId⟩
            (if (state.server.peers key).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
          | fail error => simp only [simulateQ_pure, map_pure]; rfl
          | div => simp only [simulateQ_pure, map_pure]; rfl
          | ok value => cases value with
            | Err error => simp only [simulateQ_pure, map_pure]; rfl
            | Ok value =>
                exact PqxdhInitialGenericBuilder.candidate_native interpret calls backend aux sendRealized
                  initial value data metadata state

end Build

/-! ### Complete build factorization and settlement -/

section Factor
variable {A Metadata PeerMetadata Consumed : Type}

/-- Root-free continuation: consumes the 108-byte factor, which includes the message key; takes no root argument. -/
noncomputable def factored (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (value : Factor) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    StateT (RawCtxSharedPrimitive.SharedState A) ProbComp
      (RustM (Option Response × PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)) :=
  Functor.map (Prod.map id (PqxdhInitialGenericPublication.native resolve)) <$>
    genericBuild (RawCtxSelectedChain.calls source writer value.1) aux
      (RawCtxSelectedInitialConstructor.initial false value.2) pending data metadata (embed state)

/-- Copied from `PqxdhFirstRecordStopTagged.send_begin` (avoids importing that module). -/
theorem send_begin {Send Receive Material Context : Type} (kernel : RefinedRatchet Send Receive Material) (context : Context) :
    (∃ other, RawCtxChainSend.normalBegin kernel context = .exhausted kernel other) ∨
      ∃ pending, RawCtxChainSend.normalBegin kernel context = .requested pending ∧ pending.entry = kernel ∧
        pending.request = kernel.send_chain := by
  have begun := RawCtxChainSend.normalBegin_exact kernel context
  cases start : RawCtxChainSend.normalBegin kernel context with
  | exhausted entry other =>
    rw [start] at begun
    simp only [RawCtxChainSend.beginSend, Bind.bind, Aeneas.Std.bind] at begun
    repeat' split at begun
    all_goals simp_all only [RustM.ok.injEq, reduceCtorEq]
    all_goals cases begun
    all_goals exact Or.inl ⟨_, rfl⟩
  | requested pending =>
    rw [start] at begun
    simp only [RawCtxChainSend.beginSend, Bind.bind, Aeneas.Std.bind] at begun
    repeat' split at begun
    all_goals simp_all only [RustM.ok.injEq, reduceCtorEq]
    all_goals cases begun
    all_goals exact Or.inr ⟨_, rfl, rfl, rfl⟩

/-- The placeholder initial Server kernel: hidden send slot, known receive chain. -/
theorem initial_ok (otherChain : RootOutput) :
    ∃ kernel, RawCtxSelectedInitialConstructor.initial false otherChain = ok kernel ∧
      kernel.receive_chain = .known (RawCtxFreshChainCut.concreteChain otherChain) :=
  ⟨_, rfl, rfl⟩

/-- A labelled send either stays exhausted (no ciphertext) or publishes a settled kernel. -/
theorem send_shape (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (entry : Kernel)
    (receive : ∃ chain, entry.receive_chain = .known chain) (context : RawCtxSourceSend.SealContext) :
    (RawCtxSelectedChain.calls (Auxiliary := A) source writer challenge).send entry context = pure (entry, none) ∨
      ∃ (advanced : Kernel)
        (sealing : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp (Option RawCtxSourceSend.Encrypted)),
        Settled advanced ∧
          (RawCtxSelectedChain.calls source writer challenge).send entry context =
            (fun sealed => (advanced, sealed)) <$> sealing := by
  rcases send_begin entry context with ⟨other, begun⟩ | ⟨pending, begun, entryEq, _⟩
  · left
    simp only [RawCtxSelectedChain.calls, RawCtxChainSend.execute, begun, RawCtxChainSend.program, simulateQ_pure]
  · right
    refine ⟨(RawCtxChainSend.ready pending (RawCtxSelectedChain.step source challenge pending.request)).advanced,
      RawCtxSelectedChain.sendLabels source writer challenge
        (.inr (RawCtxChainSend.ready pending (RawCtxSelectedChain.step source challenge pending.request))),
      ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
    · simpa only [RawCtxChainSend.ready, entryEq] using receive
    · simp only [RawCtxSelectedChain.calls, RawCtxChainSend.execute, begun, RawCtxChainSend.program,
        simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
      change (RawCtxSelectedChain.sendLabels source writer challenge (.inl pending.request) >>= fun reply =>
        RawCtxSelectedChain.sendLabels source writer challenge (.inr (RawCtxChainSend.ready pending reply)) >>= fun sealed =>
          pure ((RawCtxChainSend.ready pending reply).advanced, sealed)) = _
      simp only [RawCtxSelectedChain.sendLabels, pure_bind, bind_pure_comp]

section Settle
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (challenge : RatchetKdfResponse) (chain : RatchetChain)

theorem settle_after (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (entry : Kernel) (receive : ∃ c, entry.receive_chain = .known c) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (settled : StateSettled state) :
    Prod.map id (PqxdhInitialGenericPublication.native (nativeKernel chain)) <$>
      PqxdhInitialGenericPublication.afterInitialization (RawCtxSelectedChain.calls source writer challenge) aux
        candidate authenticated entry metadata state =
    Prod.map id (PqxdhInitialGenericPublication.native resolve) <$>
      PqxdhInitialGenericPublication.afterInitialization (RawCtxSelectedChain.calls source writer challenge) aux
        candidate authenticated entry metadata state := by
  have base := native_settled chain state settled
  simp only [PqxdhInitialGenericPublication.afterInitialization]
  rcases send_shape source writer challenge entry receive (PqxdhServerRegistrationPublication.firstContext candidate authenticated)
    with sent | ⟨advanced, sealing, fresh, sent⟩
  · rw [sent]
    simp only [pure_bind, map_bind, map_pure, Prod.map_apply, id_eq, base]
  · rw [sent]
    simp only [bind_map_left, map_bind]
    refine bind_congr fun sealed => bind_congr fun _ => ?_
    cases sealed with
    | none => simp only [map_pure, Prod.map_apply, id_eq, base]
    | some encrypted =>
        simp only [map_bind]
        refine bind_congr fun written => ?_
        cases written with
        | none => simp only [map_pure, Prod.map_apply, id_eq, base]
        | some bytes =>
            simp only [map_pure, Prod.map_apply, id_eq,
              native_settled chain _ (publish_settled state settled candidate advanced fresh metadata)]

theorem settle_candidate (otherChain : RootOutput) (candidate : pqxdh.ServerRegistrationCandidate)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (settled : StateSettled state) :
    Functor.map (Prod.map id (PqxdhInitialGenericPublication.native (nativeKernel chain))) <$>
      PqxdhInitialGenericBuilder.candidate (RawCtxSelectedChain.calls source writer challenge) aux
        (RawCtxSelectedInitialConstructor.initial false otherChain) candidate data metadata state =
    Functor.map (Prod.map id (PqxdhInitialGenericPublication.native resolve)) <$>
      PqxdhInitialGenericBuilder.candidate (RawCtxSelectedChain.calls source writer challenge) aux
        (RawCtxSelectedInitialConstructor.initial false otherChain) candidate data metadata state := by
  have base := native_settled chain state settled
  obtain ⟨kernel, built, receive⟩ := initial_ok otherChain
  simp only [PqxdhInitialGenericBuilder.candidate, built, PqxdhInitialGenericBuilder.continueRust, map_bind]
  refine bind_congr fun valid => ?_
  cases valid
  · simp only [Bool.not_false, ite_true, map_pure, RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq, base]
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, map_bind]
    refine bind_congr fun reserved => ?_
    cases reserved
    · simp only [Bool.not_false, ite_true, map_pure, RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq, base]
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      by_cases empty : (data.getD registrationWitness).isEmpty = true
      · simp only [empty, ite_true, map_pure, RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq, base]
      · simp only [empty, Bool.false_eq_true, ite_false]
        by_cases fits : 8 + (data.getD registrationWitness).length ≤ Usize.max
        · simp only [fits, ite_true, map_bind]
          refine bind_congr fun allocated => ?_
          cases allocated
          · simp only [Bool.not_false, ite_true, map_pure, RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq, base]
          · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
            cases bound : candidate.key_id_binding with
            | fail error => rfl
            | div => rfl
            | ok binding =>
                simp only [Functor.map_map]
                have after := settle_after source writer aux challenge chain candidate
                  (absBytes binding.bytes ++ data.getD registrationWitness) kernel ⟨_, receive⟩ metadata state settled
                have lifted := congrArg (fun work => RustM.ok <$> work) after
                simpa only [Functor.map_map, Function.comp_def, RawCtxMaterialInterpretation.rust_map_ok] using lifted
        · simp only [fits, ite_false, map_pure, RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq, base]

theorem settle_generic (otherChain : RootOutput) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (settled : StateSettled state) :
    Functor.map (Prod.map id (PqxdhInitialGenericPublication.native (nativeKernel chain))) <$>
      genericBuild (RawCtxSelectedChain.calls source writer challenge) aux
        (RawCtxSelectedInitialConstructor.initial false otherChain) pending data metadata state =
    Functor.map (Prod.map id (PqxdhInitialGenericPublication.native resolve)) <$>
      genericBuild (RawCtxSelectedChain.calls source writer challenge) aux
        (RawCtxSelectedInitialConstructor.initial false otherChain) pending data metadata state := by
  have base := native_settled chain state settled
  unfold genericBuild
  cases next : pqxdh.server_next_key_id state.control with
  | fail error => rfl
  | div => rfl
  | ok result =>
      cases result with
      | Err error =>
          simp only [PqxdhInitialGenericBuilder.continueRust, map_pure,
            RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq, base]
      | Ok key =>
          simp only [PqxdhInitialGenericBuilder.continueRust]
          cases prepared : pqxdh.server_prepare_commit state.control pending ⟨state.server.identity, state.identityKeyId⟩
            (if (state.server.peers key).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
          | fail error => rfl
          | div => rfl
          | ok value => cases value with
            | Err error =>
                simp only [map_pure, RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq, base]
            | Ok value =>
                exact settle_candidate source writer aux challenge chain otherChain value data metadata state settled

end Settle

/-- Settlement: every kernel the continuation can publish has both chains known. -/
theorem settle_build (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (challenge : RatchetKdfResponse) (chain : RatchetChain) (otherChain : RootOutput)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (settled : StateSettled state) :
    Functor.map (Prod.map id (PqxdhInitialGenericPublication.native (nativeKernel chain))) <$>
      genericBuild (RawCtxSelectedChain.calls source writer challenge) aux
        (RawCtxSelectedInitialConstructor.initial false otherChain) pending data metadata state =
    Functor.map (Prod.map id (PqxdhInitialGenericPublication.native resolve)) <$>
      genericBuild (RawCtxSelectedChain.calls source writer challenge) aux
        (RawCtxSelectedInitialConstructor.initial false otherChain) pending data metadata state :=
  settle_generic source writer aux challenge chain otherChain pending data metadata state settled

/-- Server-send half of `entry_factor`: the native build uses the root only through `factor`. -/
theorem server_send_factor (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (pending : pqxdh.PendingServerRegistration) (root : RootOutput) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    simulateQ (PqxdhRegistrationProtocolState.registrationImpl source writer aux)
      (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
        (PqxdhServerRegistrationPublication.build source pending root data metadata state)) =
      factored source writer aux (factor source root) pending data metadata state := by
  rw [← cut_source, initial_factor,
    ← native_embed (RawCtxFreshChainCut.concreteChain (target source root)) state,
    ← PqxdhInitialGenericPublication.registration_source,
    build_native _ (RawCtxSelectedChain.calls source writer (factor source root).1)
      (RawCtxSourceMaterialLabels.nativeImpl source writer) aux
      (fun entry context => RawCtxSelectedChain.send_source source writer
        (RawCtxFreshChainCut.concreteChain (target source root)) entry context)]
  rw [native_embed]
  exact settle_build source writer aux _ _ _ pending data metadata (embed state) (embed_settled state)

end Factor


/-! ### Generalization: any monad, any seal primitive with the real KDF branch

The experiment logs successful seals at the `RawCtxSourceSend.PrimitiveSpec` seal callback and may run
in `StateT _ (OracleComp RootSpec)`; this shows the chain placeholder does not depend on either choice. -/

section General
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Address-free chain labels over an arbitrary primitive handler. -/
noncomputable def primLabels (prim : QueryImpl RawCtxSourceSend.PrimitiveSpec m)
    (source : FixedHkdfSha512NoSaltSource) (challenge : RatchetKdfResponse) :
    QueryImpl (RawCtxChainSend.SendSpec Slot Slot RatchetMaterial
      RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted) m
  | .inl slot => pure (RawCtxSelectedChain.step source challenge slot)
  | .inr pending => (prim ∘ₛ RawCtxSourceSend.adapter) (.inr (RawCtxInterpretedSend.nativeSeal
      (RawCtxChainSend.nativeSeal (fun _ => RawCtxSelectedChain.unusedChain)
        (fun _ => RawCtxSelectedChain.unusedChain) pending)))

theorem prim_send_source (prim : QueryImpl RawCtxSourceSend.PrimitiveSpec m)
    (source : FixedHkdfSha512NoSaltSource)
    (kdf : ∀ request, prim (.inl request) = pure (RawCtxSourceHkdf.response source.crypto request))
    (target : RatchetChain) (entry : Kernel) (context : RawCtxSourceSend.SealContext) :
    simulateQ (prim ∘ₛ RawCtxSourceSend.adapter) (RawCtxSourceSend.send (nativeKernel target entry) context) =
      (fun result => (nativeKernel target result.1, result.2)) <$>
        simulateQ (primLabels prim source
          (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target)))
          (RawCtxChainSend.execute entry context) := by
  rw [nativeKernel, RawCtxInterpretedSend.send_native, simulateQ_map, ← QueryImpl.simulateQ_compose]
  have mapped := RawCtxChainSend.execute_native (RawCtxSelectedChain.interpret target)
    (RawCtxSelectedChain.interpret target)
    (primLabels prim source (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target)))
    ((prim ∘ₛ RawCtxSourceSend.adapter) ∘ₛ RawCtxInterpretedSend.nativeAdapter) ?_ ?_ entry context
  · rw [mapped, Functor.map_map]
    rfl
  · intro slot
    have lifted : ∀ request, simulateQ (prim ∘ₛ RawCtxSourceSend.adapter)
        ((RawCtxSourceSend.SendSpec RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted).query (.inl request)) =
          pure (RawCtxSourceHkdf.response source.crypto request) := by
      intro request
      rw [simulateQ_spec_query]
      change simulateQ prim (liftM (RawCtxSourceSend.PrimitiveSpec.query (.inl request))) = _
      rw [simulateQ_spec_query, kdf]
    change simulateQ (prim ∘ₛ RawCtxSourceSend.adapter) (RawCtxInterpretedReceive.decodeResponse <$>
      (RawCtxSourceSend.SendSpec RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted).query
        (.inl (RawCtxChainSend.nativeRequest (RawCtxSelectedChain.interpret target slot)))) = _
    rw [simulateQ_map, lifted, map_pure, RawCtxSelectedChain.step_source]
    simp only [primLabels, map_pure]
    rfl
  · intro pending
    simp only [QueryImpl.compose, RawCtxInterpretedSend.nativeAdapter, simulateQ_spec_query, primLabels]
    rfl

end General


/-! ### The factor in ideal-model terms (interface to B8a) -/

theorem address_ratchet (root : RootOutput) : address root = ratchetAddress root.toList := by
  simp only [address, RawCtxKdfRequestTable.address, PqxdhRootTableInitialization.rootArray_bytes,
    PqxdhInitialRatchetComplementarity.absBytes_ratchetSymmetricInfo, ratchetAddress]

theorem concreteChain_bytes (value : RootOutput) :
    absBytes (RawCtxFreshChainCut.concreteChain value).bytes = value.toList := by
  simp [RawCtxFreshChainCut.concreteChain, absBytes, List.map_map, Function.comp_def]

/-- `f` = (HKDF(chain_0, INFO_R, 76), second32 init) with (chain_0, second32 init) = `Pqxdh.rootChains root`. -/
theorem factor_bytes (source : FixedHkdfSha512NoSaltSource) (root : RootOutput) :
    absBytes (factor source root).1.bytes =
        Pqxdh.ratchetOut source.crypto (Pqxdh.rootChains source.crypto root.toList).1 ∧
      (factor source root).2.toList = (Pqxdh.rootChains source.crypto root.toList).2 := by
  have chains := rootChains_eq_initialProjection source.crypto source.prefixConsistent root.toList
  rw [chains, ← address_ratchet]
  constructor
  · rw [factor, RawCtxSourceHkdf.response_bytes, RawCtxChainSend.nativeRequest, concreteChain_bytes,
      PqxdhInitialRatchetComplementarity.absBytes_ratchetSymmetricInfo]
    rfl
  · rfl


/-- Corollary: two roots with the same 108-byte factor give identical complete native builds. -/
theorem root_only_through_factor {A Metadata PeerMetadata Consumed : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (pending : pqxdh.PendingServerRegistration) (first second : RootOutput)
    (same : factor source first = factor source second) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    simulateQ (PqxdhRegistrationProtocolState.registrationImpl source writer aux)
        (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
          (PqxdhServerRegistrationPublication.build source pending first data metadata state)) =
      simulateQ (PqxdhRegistrationProtocolState.registrationImpl source writer aux)
        (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
          (PqxdhServerRegistrationPublication.build source pending second data metadata state)) := by
  rw [server_send_factor, server_send_factor, same]


/-! ### Evidence for the Beacon-receive half: the same factor serves it -/

/-- The Beacon initializer hides the same first32 (its receive chain) and keeps the same second32. -/
theorem initial_factor_beacon (source : FixedHkdfSha512NoSaltSource) (root : RootOutput) :
    PqxdhRootTableInitialization.initialKernelRun source true root =
      nativeKernel (RawCtxFreshChainCut.concreteChain (target source root)) <$>
        RawCtxSelectedInitialConstructor.initial true (other source root) :=
  RawCtxSelectedInitialConstructor.source_initial source (true, PqxdhRootTableInitialization.rootArray root)

/-- Every Beacon raw receive on such a kernel consumes only `(factor source root).1` for the hidden chain. -/
theorem beacon_receive_factor {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (root : RootOutput) (entry : Kernel) (requested : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) :
    simulateQ (RawCtxSourceChainHandles.receiveNative (Auxiliary := Auxiliary) source writer)
      (RawCtxOwnerOracle.receive (nativeKernel (RawCtxFreshChainCut.concreteChain (target source root)) entry)
        requested context) =
      (fun result => (nativeKernel (RawCtxFreshChainCut.concreteChain (target source root)) result.1, result.2)) <$>
        simulateQ (RawCtxSelectedChain.receiveLabels source writer (factor source root).1)
          (RawCtxChainReceive.execute entry requested context) :=
  RawCtxSelectedChain.receive_source source writer _ entry requested context

end BeaconcryptCore.Computational.PqxdhServerAuthSendFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.native_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.native_known

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.settled_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.settled_native

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.native_embed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.native_embed

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.embed_settled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.embed_settled

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.native_settled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.native_settled

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.publish_settled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.publish_settled

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.initial_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.initial_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.cut_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.cut_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.build_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.build_native

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.send_begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.send_begin

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.initial_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.initial_ok

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.send_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.send_shape

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.settle_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.settle_after

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.settle_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.settle_candidate

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.settle_generic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.settle_generic

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.settle_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.settle_build

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.server_send_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.server_send_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.prim_send_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.prim_send_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.address_ratchet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.address_ratchet

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.concreteChain_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.concreteChain_bytes

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.factor_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.factor_bytes

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.root_only_through_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.root_only_through_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.initial_factor_beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.initial_factor_beacon

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.beacon_receive_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSendFactor.beacon_receive_factor
