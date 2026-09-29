import BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality
/-!
# Target-free bound on the first-record finish-collision term

`PqxdhFirstRecordConfidentiality.collGame` is the probability, in the selected-key CTX source game of the instrumented confidentiality client, that the client event holds and some attempted Beacon finish made a selected raw opening (the `markRaw` flag of `PqxdhFirstRecordConfidentiality.insImpl`). `coll_bound` bounds it by `(2 + qSend + 51 (qRaw + qFinish)) / 2^256` for every post whose continuations are bounded by a query budget (`qSend` sends, `qRaw` raw receives and `qFinish` attempted finishes), and `coll_real` restates it with a certificate's post budget. `first_record_confidentiality_coll` and `first_record_confidentiality_budget_coll` substitute it into `PqxdhFirstRecordConfidentiality.first_record_confidentiality` and `first_record_confidentiality_budget`; their only remaining explicit game is `keyGame`. This module adds no premise, primitive law or cryptographic assumption.

The hit event. A compiled finish makes a selected raw opening only through the terminal opening of its application receive (`RawCtxSelectedReceiveReceipt.program_terminal`), and only when that opening uses the selected (hidden) material. `HitRaw` is this event of a finish request: the receive prelude accepts the raw bytes and the deterministic receive path reaches a terminal opening with the selected material (`TerminalHidden`). It is a pure predicate of the candidate, the Beacon kernel and the bytes, and `raw_quiet` and `lower_quiet` show that without it the compiled finish makes no selected raw opening. The finish programs `ownerMarkedHit` and `ownerHit` return `HitReq` of their finish request as an extra bit and erase to `ownerMarked` and `owner`; `hit_dominates` shows that the `markRaw` flag of a compiled finish is raised only if that bit is set.

Transfer to the source post. `hitObserved` is the history-extended source post `PqxdhFirstRecordNonceStop.sourceObserved` with a sticky hit flag that takes the bit of `ownerHit`. The instrumented augmented post and `hitObserved` are both images of one evaluated marked run of `ownerMarkedHit` (`PqxdhSelectedInitialOwnerCompiler.program_source`, `PqxdhFirstRecordConfidentiality.markRaw_evaluate`), so they are coupled with equal replies and projected states, and a raised raw flag implies a raised hit flag (`aug_keep`, `aug_finish`, `aug_run`). The output of the confidentiality chain requires the raw flag and an undisclosed selected chain, so it is at most the hit event of `hitObserved` (`aug_hit`, `postBit_hit`, `first_hit`).

The tagged coupling. The hit event is coupled with the target-free tagged world of `PqxdhFirstRecordStopTagged`, like the stop event but without its invariant `GoodState`, because a derivation that returns the selected material on a known chain logs the selected value at once. Material provenance (`terminal_known`, `terminal_hit`, by material naturality of the interpreted receive) turns a selected terminal opening into a derivation returning the selected material. Chain provenance (`begin_request`, `resume_request`) shows that every derivation of the tagged first receive of a finish is on a known chain, because the finish kernel is clean (`Clean`: known receiving chain and known cached material; `hidden_clean`, `known_clean`, `initial_clean`). Path correspondence (`interp_path`) and `tagged_path` give `stage_hit`: the tagged first receive logs the selected value whenever the represented concrete delivery hits. `owner_hit_coupled`, `finish_hit_step`, `hit_coupled` and `hit_bound` couple the whole post, so a hit with the selected chain undisclosed implies that the selected value is logged. `hit_tagged` adds the builder as `stop_tagged` does: the source-only finish-hit run `hitRun` is at most the probability that the selected half of the initializer block is in the final log of the same target-free run `taggedRun`.

The prepared level. `insRun_client_out` and `outObserve_eq` are the output-generic forms of `insRun_client` and `insObserve_eq`. `client_le_out` reorders the CTX source game into the prepared samples and pays `2^-256` for the initial half alias; `out_le_hit` and `hit_source_tagged` reach `PqxdhFirstRecordStopTagged.taggedGame`, which `tagged_game_bound` bounds by `(1 + qSend + 51 (qRaw + qFinish)) / 2^256`.

The stop term and `collGame` both reduce to the event that the selected half is logged by the same target-free tagged run, but they arise at different places of the confidentiality chain (the stop term in the source world of the key-last endpoint, `collGame` in the CTX source game after the output switch), so the headline keeps one stop-sized term for each and a joint term would need a different chain.

Messages are byte strings that each side knows how to decode; the frame decoder and the record writer are abstract functions of the environment, and no property of a serialization library is used.
-/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound
open PqxdhFirstRecordStopTagged

section Provenance
open ratchet.refined

/-- Receive admission requests its first derivation on the kernel's receiving chain. -/
theorem begin_request {Send Receive Material Context : Type} (kernel : RefinedRatchet Send Receive Material)
    (target : Std.U64) (context : Context) (pending : RawCtxChainReceive.Kdf Send Receive Material Context)
    (begun : RawCtxChainReceive.normalBegin kernel target context = .kdfRequested pending) :
    pending.request = kernel.receive_chain := by
  have exact := RawCtxChainReceive.normalBegin_exact kernel target context
  rw [begun] at exact
  simp only [RawCtxChainReceive.beginReceive, Bind.bind, Aeneas.Std.bind] at exact
  repeat' split at exact
  all_goals simp_all only [RustM.ok.injEq, reduceCtorEq, RawCtxChainReceive.rejected]
  all_goals cases exact
  all_goals rfl

/-- A receive resumption requests its next derivation on the chain returned by the previous one. -/
theorem resume_request {Send Receive Material Context : Type} (pending : RawCtxChainReceive.Kdf Send Receive Material Context)
    (reply : Receive × Material) (next : RawCtxChainReceive.Kdf Send Receive Material Context)
    (resumed : RawCtxChainReceive.normalResume pending reply = .kdfRequested next) :
    next.request = reply.1 := by
  have exact := RawCtxChainReceive.normalResume_exact pending reply
  rw [resumed] at exact
  simp only [RawCtxChainReceive.resume, Bind.bind, Aeneas.Std.bind] at exact
  repeat' split at exact
  all_goals simp_all only [RustM.ok.injEq, reduceCtorEq, RawCtxChainReceive.rejected]
  all_goals cases exact
  all_goals rfl

end Provenance

section Hit
open ratchet.refined PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxSelectedParentTable

/-- Selected (hidden) message-key material. -/
def HiddenSlot : RawCtxSelectedMessageKey.Slot → Prop
  | .hidden _ => True
  | .known _ => False

variable (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)

/-- Along the deterministic derivation path of a stopped-source receive effect, some private derivation returns the selected material. -/
noncomputable def InterpHit (effect : RawCtxInterpretedReceive.Effect RawCtxSelectedMessageKey.Slot RawCtxWholeOwner.OpenContext) :
    Prop :=
  match effect with
  | .kdfRequested pending => HiddenSlot (RawCtxSelectedMessageKdf.step prior target nonce next pending.request).2 ∨
      InterpHit (RawCtxInterpretedReceive.normalResume pending (RawCtxSelectedMessageKdf.step prior target nonce next pending.request))
  | _ => False
termination_by RawCtxInterpretedReceive.effectRank effect
decreasing_by exact RawCtxInterpretedReceive.normalResume_rank _ _

/-- The terminal opening of a stopped-source receive effect uses the selected material. -/
def TerminalHidden (effect : RawCtxSelectedReceiveReceipt.SourceEffect) : Prop :=
  ∃ pending input, RawCtxSelectedReceiveReceipt.terminal prior none target nonce next effect = .opening pending ∧
    RawCtxInterpretedArguments.openArguments pending = some input ∧ HiddenSlot input.material

/-- A raw application delivery to a Beacon kernel is accepted by the receive prelude and its receive reaches a terminal opening with the selected material. -/
def HitRaw (read : RawCtxReceive.FrameDecoder) (candidate : pqxdh.BeaconRegistrationCandidate)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (raw : Pqxdh.Bytes) : Prop :=
  ∃ frame, raw.isEmpty = false ∧ read raw = some frame ∧
    RawCtxReceive.ValidFrame (PqxdhInitialGenericBeacon.localOwner candidate kernel).expectedSender
      (PqxdhInitialGenericBeacon.localOwner candidate kernel).associatedData frame ∧
    TerminalHidden prior target nonce next (RawCtxInterpretedReceive.normalBegin kernel frame.sequence
      ⟨raw, frame, (PqxdhInitialGenericBeacon.localOwner candidate kernel).associatedData⟩)

/-- Material interpretation keeps the receive measure. -/
theorem rank_map (effect : RawCtxInterpretedReceive.Effect RatchetMaterial RawCtxWholeOwner.OpenContext) :
    RawCtxInterpretedReceive.effectRank (RawCtxInterpretedReceive.mapEffect RawCtxSelectedMessageKey.Slot.known effect) =
      RawCtxInterpretedReceive.effectRank effect := by
  cases effect <;> rfl

/-- Material provenance: if no derivation of the path returns the selected material, the terminal opening of an effect with only known material uses known material. -/
theorem terminal_known (effect : RawCtxInterpretedReceive.Effect RatchetMaterial RawCtxWholeOwner.OpenContext)
    (clear : ¬ InterpHit prior target nonce next (RawCtxInterpretedReceive.mapEffect RawCtxSelectedMessageKey.Slot.known effect))
    (pending : RawCtxSelectedReceiveReceipt.Pending)
    (reached : RawCtxSelectedReceiveReceipt.terminal prior none target nonce next
      (RawCtxInterpretedReceive.mapEffect RawCtxSelectedMessageKey.Slot.known effect) = .opening pending) :
    ∃ base, pending = RawCtxInterpretedOpening.mapOpening RawCtxSelectedMessageKey.Slot.known base := by
  generalize depth : RawCtxInterpretedReceive.effectRank effect = rank
  induction rank using Nat.strong_induction_on generalizing effect with
  | h rank ih =>
    cases effect with
    | rejected entry context =>
      simp only [RawCtxInterpretedReceive.mapEffect, RawCtxSelectedReceiveReceipt.terminal, reduceCtorEq] at reached
    | openRequested opening =>
      simp only [RawCtxInterpretedReceive.mapEffect, RawCtxSelectedReceiveReceipt.terminal,
        RawCtxSelectedReceiveReceipt.Terminal.opening.injEq] at reached
      exact ⟨opening, reached.symm⟩
    | kdfRequested base =>
      simp only [RawCtxInterpretedReceive.mapEffect] at clear reached
      rw [RawCtxSelectedReceiveReceipt.terminal] at reached
      rw [InterpHit] at clear
      simp only [not_or] at clear
      obtain ⟨notHidden, rest⟩ := clear
      change RawCtxSelectedReceiveReceipt.terminal prior none target nonce next
        (RawCtxInterpretedReceive.normalResume (RawCtxInterpretedReceive.mapKdf RawCtxSelectedMessageKey.Slot.known base)
          (RawCtxSelectedMessageKdf.step prior target nonce next base.request)) = _ at reached
      change ¬ HiddenSlot (RawCtxSelectedMessageKdf.step prior target nonce next base.request).2 at notHidden
      change ¬ InterpHit prior target nonce next (RawCtxInterpretedReceive.normalResume
        (RawCtxInterpretedReceive.mapKdf RawCtxSelectedMessageKey.Slot.known base)
          (RawCtxSelectedMessageKdf.step prior target nonce next base.request)) at rest
      generalize RawCtxSelectedMessageKdf.step prior target nonce next base.request = reply at notHidden rest reached
      obtain ⟨chain, material⟩ := reply
      cases material with
      | hidden value => exact absurd trivial notHidden
      | known value =>
        have mapped := RawCtxInterpretedReceive.normalResume_map RawCtxSelectedMessageKey.Slot.known base (chain, value)
        simp only at mapped
        rw [mapped] at reached rest
        refine ih _ ?_ _ rest reached rfl
        rw [← depth]
        exact RawCtxInterpretedReceive.normalResume_rank base (chain, value)

/-- A terminal opening with selected material on an effect with only known material is preceded by a derivation returning the selected material. -/
theorem terminal_hit (effect : RawCtxInterpretedReceive.Effect RatchetMaterial RawCtxWholeOwner.OpenContext)
    (hidden : TerminalHidden prior target nonce next (RawCtxInterpretedReceive.mapEffect RawCtxSelectedMessageKey.Slot.known effect)) :
    InterpHit prior target nonce next (RawCtxInterpretedReceive.mapEffect RawCtxSelectedMessageKey.Slot.known effect) := by
  by_contra clear
  obtain ⟨pending, input, reached, arguments, selected⟩ := hidden
  obtain ⟨base, rfl⟩ := terminal_known prior target nonce next effect clear pending reached
  rw [RawCtxInterpretedArguments.openArguments_map] at arguments
  cases found : RawCtxInterpretedArguments.openArguments base with
  | none => simp [found] at arguments
  | some value =>
    simp only [found, Option.map_some, Option.some.injEq] at arguments
    subst arguments
    exact selected

/-- Along the derivation path of a tagged receive effect under the concrete replies, some derivation is on a known chain equal to the selected value. -/
noncomputable def PathHit (effect : RawCtxChainReceive.Effect Chain Chain Material RawCtxWholeOwner.OpenContext) : Prop :=
  match effect with
  | .kdfRequested pending => target ∈ logged pending.request ∨
      PathHit (RawCtxChainReceive.normalResume pending (concreteStep prior target nonce next pending.request))
  | _ => False
termination_by RawCtxChainReceive.effectRank effect
decreasing_by exact RawCtxChainReceive.normalResume_rank _ _

/-- A known slot reads as its own chain. -/
theorem reveal_known (chain : RatchetChain) : reveal target (.known chain) = chain := rfl

/-- The concrete derivation on a known slot is the stopped-source derivation on its chain. -/
theorem concrete_known (chain : RatchetChain) :
    (reveal target (concreteStep prior target nonce next (.known chain)).1, (concreteStep prior target nonce next (.known chain)).2) =
      RawCtxSelectedMessageKdf.step prior target nonce next (RawCtxChainSend.nativeRequest chain) := rfl

/-- Path correspondence: a hit of the stopped-source path of the represented effect is a known-chain hit of the tagged path, when the first derivation of the effect is on a known slot (later ones then are, by `resume_request`). -/
theorem interp_path (effect : RawCtxChainReceive.Effect Chain Chain Material RawCtxWholeOwner.OpenContext)
    (known : ∀ pending, effect = .kdfRequested pending → isHidden pending.request = false)
    (hit : InterpHit prior target nonce next (RawCtxChainReceive.nativeEffect (reveal target) (reveal target) effect)) :
    PathHit prior target nonce next effect := by
  generalize depth : RawCtxChainReceive.effectRank effect = rank
  induction rank using Nat.strong_induction_on generalizing effect with
  | h rank ih =>
    cases effect with
    | rejected entry context =>
      simp only [RawCtxChainReceive.nativeEffect] at hit
      unfold InterpHit at hit
      exact hit.elim
    | openRequested opening =>
      simp only [RawCtxChainReceive.nativeEffect] at hit
      unfold InterpHit at hit
      exact hit.elim
    | kdfRequested pending =>
      have slotKnown := known pending rfl
      simp only [RawCtxChainReceive.nativeEffect] at hit
      rw [InterpHit] at hit
      rw [PathHit]
      cases slot : pending.request with
      | hidden => rw [slot] at slotKnown; exact absurd slotKnown (by simp [isHidden])
      | known chain =>
        change HiddenSlot (RawCtxSelectedMessageKdf.step prior target nonce next
            (RawCtxChainSend.nativeRequest (reveal target pending.request))).2 ∨
          InterpHit prior target nonce next (RawCtxInterpretedReceive.normalResume
            (RawCtxChainReceive.nativeKdf (reveal target) (reveal target) pending)
            (RawCtxSelectedMessageKdf.step prior target nonce next
              (RawCtxChainSend.nativeRequest (reveal target pending.request)))) at hit
        rw [slot, reveal_known] at hit
        rcases hit with selected | later
        · left
          unfold RawCtxSelectedMessageKdf.step at selected
          split at selected
          · rename_i address
            have same := (RawCtxSelectedParentPrivatePatch.address_eq target chain).mp address
            simp [logged, same]
          · simp [RawCtxSelectedMessageKdf.known, HiddenSlot] at selected
        · right
          rw [← concrete_known prior target nonce next chain, RawCtxChainReceive.normalResume_native] at later
          refine ih _ ?_ _ ?_ later rfl
          · rw [← depth, ← slot]
            exact RawCtxChainReceive.normalResume_rank pending _
          · intro following resumed
            rw [resume_request _ _ following resumed]
            rfl

end Hit

section TaggedPath
open ratchet.refined PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxSelectedParentTable PqxdhJointKdfGame
variable {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)

/-- A known-chain hit of the tagged path forces the selected value into the log of every run of the tagged receive program from that effect, when the first derivation of the effect is on a known slot (later ones then are, by `resume_request`). -/
theorem tagged_path (target : RootOutput) (effect : RawCtxChainReceive.Effect Chain Chain Material RawCtxWholeOwner.OpenContext)
    (known : ∀ pending, effect = .kdfRequested pending → isHidden pending.request = false)
    (hit : PathHit prior target nonce next effect) (state : RawCtxSharedPrimitive.SharedState A × Log) :
    ∀ result ∈ support ((simulateQ (taggedLabels source writer prior key nonce next)
      (simulateQ receiveInject (RawCtxChainReceive.program (Plaintext := RawCtxWholeOwner.Decrypted) effect))).run state),
      target ∈ result.2.2 := by
  generalize depth : RawCtxChainReceive.effectRank effect = rank
  induction rank using Nat.strong_induction_on generalizing effect state with
  | h rank ih =>
    cases effect with
    | rejected entry context => unfold PathHit at hit; exact hit.elim
    | openRequested opening => unfold PathHit at hit; exact hit.elim
    | kdfRequested pending =>
      intro result supported
      rw [RawCtxChainReceive.program] at supported
      simp only [simulateQ_bind, simulateQ_spec_query, receiveInject, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨step, stepSupported, rest⟩ := supported
      change step ∈ support ((pure (taggedStep prior nonce next pending.request,
        (state.1, state.2 ++ logged pending.request)) : ProbComp _)) at stepSupported
      rw [support_pure, Set.mem_singleton_iff] at stepSupported
      subst stepSupported
      unfold PathHit at hit
      by_cases fresh : target ∈ logged pending.request
      · exact grows_labels source writer prior key nonce next target _ _ (List.mem_append_right _ fresh) result rest
      · have later : PathHit prior target nonce next
            (RawCtxChainReceive.normalResume pending (concreteStep prior target nonce next pending.request)) := by
          rcases hit with here | later
          · exact absurd here fresh
          · exact later
        rw [step_tagged prior target nonce next pending.request fresh] at later
        refine ih _ ?_ _ ?_ later _ rfl result rest
        · rw [← depth]
          exact RawCtxChainReceive.normalResume_rank pending _
        · intro following resumed
          rw [resume_request _ _ following resumed]
          exact tagged_known prior nonce next pending.request

/-- A tagged kernel whose receiving chain is known and whose cached material is known. -/
def Clean (kernel : TKernel) : Prop :=
  isHidden kernel.receive_chain = false ∧
    ∃ base, kernel = RawCtxMaterialInterpretation.mapRefined RawCtxSelectedMessageKey.Slot.known base

/-- The tagged first receive of an attempted finish on a clean kernel logs the selected value whenever the represented concrete delivery reaches the selected material. -/
theorem stage_hit {N C : Type} (target : RootOutput) (decode : RawCtxReceive.FrameDecoder) (candidate : pqxdh.BeaconRegistrationCandidate)
    (kernel : TKernel) (raw : Pqxdh.Bytes) (clean : Clean kernel)
    (hit : HitRaw prior target nonce next decode candidate (mapKernel target kernel) raw)
    (state : RawCtxSharedPrimitive.SharedState (PqxdhNativeSharedPrefix.Local A N C) × Log) :
    ∀ result ∈ support ((taggedStage source writer prior key nonce next decode candidate kernel raw).run state),
      Logged target result.2 := by
  obtain ⟨frame, nonempty, decoded, valid, terminalHidden⟩ := hit
  obtain ⟨receiveKnown, base, rfl⟩ := clean
  intro result supported
  unfold taggedStage at supported
  simp only [StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨inner, innerSupported, rfl⟩ := supported
  change inner ∈ support ((RawCtxChainOwner.rawReceive (RawCtxGenericOwnerInterpretation.interpretedCalls
    (taggedLabels source writer prior key nonce next) symbolicCalls) decode raw
      (PqxdhInitialGenericBeacon.localOwner candidate
        (RawCtxMaterialInterpretation.mapRefined RawCtxSelectedMessageKey.Slot.known base))).run state) at innerSupported
  simp only [RawCtxChainOwner.rawReceive, nonempty, decoded, Bool.false_eq_true, ite_false] at innerSupported
  have valid' : RawCtxReceive.ValidFrame (PqxdhInitialGenericBeacon.localOwner candidate
      (RawCtxMaterialInterpretation.mapRefined RawCtxSelectedMessageKey.Slot.known base)).expectedSender
      (PqxdhInitialGenericBeacon.localOwner candidate
        (RawCtxMaterialInterpretation.mapRefined RawCtxSelectedMessageKey.Slot.known base)).associatedData frame := valid
  simp only [valid', ↓reduceIte] at innerSupported
  simp only [StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure, Set.mem_singleton_iff] at innerSupported
  obtain ⟨received, receivedSupported, rfl⟩ := innerSupported
  change received ∈ support ((simulateQ (taggedLabels source writer prior key nonce next)
    (simulateQ receiveInject (RawCtxChainReceive.program (Plaintext := RawCtxWholeOwner.Decrypted)
      (RawCtxChainReceive.normalBegin (RawCtxMaterialInterpretation.mapRefined RawCtxSelectedMessageKey.Slot.known base)
        frame.sequence ⟨raw, frame, (PqxdhInitialGenericBeacon.localOwner candidate
          (RawCtxMaterialInterpretation.mapRefined RawCtxSelectedMessageKey.Slot.known base)).associatedData⟩)))).run state)
    at receivedSupported
  refine tagged_path source writer prior key nonce next target _ ?_ ?_ state received receivedSupported
  · intro pending begun
    rw [begin_request _ _ _ pending begun]
    exact receiveKnown
  · refine interp_path prior target nonce next _ ?_ ?_
    · intro pending begun
      rw [begin_request _ _ _ pending begun]
      exact receiveKnown
    · rw [← RawCtxChainReceive.normalBegin_native]
      have mapped := terminal_hit prior target nonce next (RawCtxInterpretedReceive.normalBegin
        (RawCtxChainInterpretation.mapChains (reveal target) (reveal target) base) frame.sequence
        ⟨raw, frame, (PqxdhInitialGenericBeacon.localOwner candidate
          (RawCtxMaterialInterpretation.mapRefined RawCtxSelectedMessageKey.Slot.known base)).associatedData⟩) (by
        rw [← RawCtxInterpretedReceive.normalBegin_map]
        exact terminalHidden)
      rw [← RawCtxInterpretedReceive.normalBegin_map] at mapped
      exact mapped

end TaggedPath

section CompiledQuiet
open ratchet.refined PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxSelectedParentTable PqxdhJointKdfGame
open PqxdhFirstRecordConfidentiality (IsRaw raw_of_target)
variable (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder)

/-- Without a selected-material hit, the compiled first raw receive of an attempted finish makes no selected raw opening. -/
theorem raw_quiet (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : RawCtxSelectedMessageReveals.Kernel) (raw : Pqxdh.Bytes)
    (clear : ¬ HitRaw prior target nonce next read candidate kernel raw) :
    (RawCtxSelectedReceiveCompiler.raw prior none target nonce next read raw
      (PqxdhInitialGenericBeacon.localOwner candidate kernel)).IsQueryBoundP IsRaw 0 := by
  unfold RawCtxSelectedReceiveCompiler.raw RawCtxChainOwner.rawReceive
  simp only [StateT.run]
  split
  · trivial
  · rename_i nonempty
    split
    · trivial
    · rename_i frame decoded
      split
      · rename_i valid
        rw [bind_pure_comp, isQueryBoundP_map_iff]
        simp only [RawCtxSelectedReceiveCompiler.calls, RawCtxSelectedReceiveCompiler.receive, RawCtxSelectedMessageDriver.receive,
          ← QueryImpl.simulateQ_compose, RawCtxInterpretedReceive.receive]
        change (simulateQ (RawCtxSelectedReceiveCompiler.compiler prior none target nonce next read frame.sender)
          (RawCtxInterpretedReceive.program (Plaintext := RawCtxWholeOwner.Decrypted)
            (RawCtxInterpretedReceive.normalBegin kernel frame.sequence _))).IsQueryBoundP IsRaw 0
        rw [RawCtxSelectedReceiveReceipt.program_terminal]
        split
        · trivial
        · rename_i pending reached
          rw [isQueryBoundP_map_iff]
          unfold RawCtxSelectedOpenConsumer.service
          split
          · trivial
          · rename_i input found
            rw [isQueryBoundP_map_iff]
            unfold RawCtxUniversalOpening.call
            split
            · rename_i value material
              exact absurd ⟨frame, Bool.eq_false_iff.mpr nonempty, decoded, valid, pending, input, reached, found,
                by simp [material, HiddenSlot]⟩ clear
            · unfold RawCtxSelectedMessageOpening.call
              simp only
              rw [isQueryBoundP_query_iff]
              intro impossible
              exact impossible.elim
      · trivial

variable {ι I D K X Response Shared A N C : Type} {extra : OracleSpec ι}

/-- An attempted-finish request whose application delivery reaches the selected material. -/
def HitReq (request : PqxdhSelectedInitialOwnerCompiler.Request I D K) : Prop :=
  match request.application with
  | none => False
  | some raw => HitRaw prior target nonce next read request.candidate request.kernel raw

variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (PqxdhNativeSharedPrefix.ExternalState A N C) ProbComp))
    (application : Response → PqxdhNativeSharedPrefix.LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → PqxdhNativeSharedPrefix.LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (PqxdhNativeSharedPrefix.ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (PqxdhNativeSharedPrefix.ExternalState A N C) ProbComp))

/-- A compiled attempted-finish request without a selected-material hit, and every source-local callback, makes no selected raw opening. -/
theorem lower_quiet (query : (PqxdhSelectedInitialOwnerCompiler.Spec extra I D K X Response Shared).Domain)
    (clear : ∀ request, query = .inr request → ¬ HitReq prior target nonce next read request)
    (state : PqxdhNativeSharedPrefix.Local A N C) :
    ((PqxdhSelectedInitialOwnerCompiler.lower pre application initial selector aux prior none target nonce next read query).run
      state).IsQueryBoundP IsRaw 0 := by
  cases query with
  | inl query =>
    exact raw_of_target _ (PqxdhSelectedInitialOwnerCompiler.external_no_open pre application initial selector aux query state)
  | inr request =>
    have quiet := clear request rfl
    simp only [PqxdhSelectedInitialOwnerCompiler.lower, StateT.run, isQueryBoundP_map_iff,
      PqxdhSelectedBeaconCompiler.finishApplication, PqxdhSelectedBeaconCompiler.afterApplication]
    unfold HitReq at quiet
    split
    · trivial
    · rename_i raw found
      rw [found] at quiet
      rw [isQueryBoundP_map_iff]
      exact raw_quiet prior target nonce next read request.candidate request.kernel raw quiet

end CompiledQuiet

section OwnerHit
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf RawCtxSelectedParentTable
open PqxdhSelectedInitialOwnerCompiler (Spec preForward Beacon Reply)
variable {ι I D K X Response Shared : Type} {extra : OracleSpec ι}
variable (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder)

/-- The attempted Beacon finish with its private installation marker, also returning whether its application delivery reaches the selected material (`HitReq` of its finish request). -/
noncomputable def ownerMarkedHit (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) (raw : Pqxdh.Bytes) (before : Beacon I D K) :
    OracleComp (Spec extra I D K X Response Shared)
      (PqxdhInitialFinishOrigin.Result PqxdhSelectedInitialOwnerCompiler.Kernel Bool I D K × Bool) :=
  match before.beacon.phase with
  | .initSent control prekey oneTime kem => do
      let prepared ← simulateQ preForward
        (PqxdhBeaconPhase2Shared.prepare control before.beacon.identity prekey oneTime kem raw)
      match prepared with
      | none => pure ((PqxdhInitialGenericBeacon.finish control before none, none), false)
      | some pending => do
          let kernel ← (Spec extra I D K X Response Shared).query (.inl (.inr (.inr (.inl pending.root))))
          match kernel with
          | none => pure (PqxdhInitialFinishOrigin.tag (mark pending.root) (PqxdhInitialGenericBeacon.finish control before none), false)
          | some kernel => do
              let application ← (Spec extra I D K X Response Shared).query (.inl (.inr (.inl pending.response)))
              (fun reply => (PqxdhInitialFinishOrigin.tag (mark pending.root) reply,
                  @decide (HitReq prior target nonce next read (⟨control, before,
                    PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata, PqxdhSelectedMessageBeacon.knownKernel kernel,
                    application⟩ : PqxdhSelectedInitialOwnerCompiler.Request I D K)) (Classical.propDecidable _))) <$>
                (Spec extra I D K X Response Shared).query (.inr
                  ⟨control, before, PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata,
                    PqxdhSelectedMessageBeacon.knownKernel kernel, application⟩)
  | _ => pure (((none, before), none), false)

/-- The attempted Beacon finish returning whether its application delivery reaches the selected material. -/
noncomputable def ownerHit (raw : Pqxdh.Bytes) (before : Beacon I D K) :
    OracleComp (Spec extra I D K X Response Shared) (Reply I D K × Bool) :=
  match before.beacon.phase with
  | .initSent control prekey oneTime kem => do
      let prepared ← simulateQ preForward
        (PqxdhBeaconPhase2Shared.prepare control before.beacon.identity prekey oneTime kem raw)
      match prepared with
      | none => pure (PqxdhInitialGenericBeacon.finish control before none, false)
      | some pending => do
          let kernel ← (Spec extra I D K X Response Shared).query (.inl (.inr (.inr (.inl pending.root))))
          match kernel with
          | none => pure (PqxdhInitialGenericBeacon.finish control before none, false)
          | some kernel => do
              let application ← (Spec extra I D K X Response Shared).query (.inl (.inr (.inl pending.response)))
              (fun reply => (reply,
                  @decide (HitReq prior target nonce next read (⟨control, before,
                    PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata, PqxdhSelectedMessageBeacon.knownKernel kernel,
                    application⟩ : PqxdhSelectedInitialOwnerCompiler.Request I D K)) (Classical.propDecidable _))) <$>
                (Spec extra I D K X Response Shared).query (.inr
                  ⟨control, before, PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata,
                    PqxdhSelectedMessageBeacon.knownKernel kernel, application⟩)
  | _ => pure ((none, before), false)

/-- Erasing the hit output gives the marked finish. -/
theorem ownerMarkedHit_erase (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) (raw : Pqxdh.Bytes) (before : Beacon I D K) :
    Prod.fst <$> ownerMarkedHit (extra := extra) (X := X) (Response := Response) prior target nonce next read mark raw before =
      PqxdhFirstRecordConfidentiality.ownerMarked mark raw before := by
  unfold ownerMarkedHit PqxdhFirstRecordConfidentiality.ownerMarked
  cases before.beacon.phase with
  | initSent control prekey oneTime kem =>
    simp only [map_bind]
    refine bind_congr fun prepared => ?_
    cases prepared with
    | none => simp only [map_pure]
    | some pending =>
      simp only [map_bind]
      refine bind_congr fun kernel => ?_
      cases kernel with
      | none => simp only [map_pure]
      | some kernel =>
        simp only [map_bind, Functor.map_map]
  | _ => simp only [map_pure]

/-- Erasing the marker gives the finish with its hit output. -/
theorem ownerMarkedHit_hit (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) (raw : Pqxdh.Bytes) (before : Beacon I D K) :
    Prod.map Prod.fst id <$> ownerMarkedHit (extra := extra) (X := X) (Response := Response) prior target nonce next read mark raw before =
      ownerHit prior target nonce next read raw before := by
  unfold ownerMarkedHit ownerHit
  cases before.beacon.phase with
  | initSent control prekey oneTime kem =>
    simp only [map_bind]
    refine bind_congr fun prepared => ?_
    cases prepared with
    | none => simp only [map_pure, Prod.map, id_eq]
    | some pending =>
      simp only [map_bind]
      refine bind_congr fun kernel => ?_
      cases kernel with
      | none => simp only [map_pure, Prod.map, id_eq, PqxdhInitialFinishOrigin.tag]
      | some kernel =>
        simp only [map_bind, Functor.map_map]
        rfl
  | _ => simp only [map_pure, Prod.map, id_eq]

end OwnerHit

section TaggedHit
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxChainInterpretation PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily RawCtxSelectedMessageDriver
variable {ι I D K X Response A N C : Type} {extra : OracleSpec ι}

/-- The zero-state ratchet constructor keeps its receiving chain. -/
theorem new_receive {Send Receive Material : Type} (send : Send) (receive : Receive) (kernel : RefinedRatchet Send Receive Material)
    (built : RefinedRatchet.new Material send receive = ok kernel) : kernel.receive_chain = receive := by
  simp only [RefinedRatchet.new, RefinedRatchet.from_counters] at built
  cases first : control.RatchetState.from_counters 0#u64 0#u64 <;> simp [first] at built
  cases second : refined.empty_material_slots Material <;> simp [second] at built
  subst built
  rfl

/-- The hidden-send tagged kernel of the marked finish is clean. -/
theorem hidden_clean (other : RootOutput) : Clean (hiddenKernel other) := by
  refine ⟨?_, hiddenBase other, rfl⟩
  have chain := new_receive _ _ _ (new_total .hidden (.known (RawCtxFreshChainCut.concreteChain other))).choose_spec
  change isHidden (hiddenBase other).receive_chain = false
  unfold hiddenBase
  rw [chain]
  rfl

/-- The known tagged image of an initializer kernel is clean. -/
theorem known_clean (kernel : PqxdhSelectedMessageBeacon.NativeKernel) :
    Clean (knownTagged (PqxdhSelectedMessageBeacon.knownKernel kernel)) :=
  ⟨rfl, mapChains RawCtxSelectedChain.Slot.known RawCtxSelectedChain.Slot.known kernel, rfl⟩

variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : PqxdhCorrelatedExtractFamily.Message) (other : RootOutput)

/-- Every kernel returned by the target-free initializer reply is clean. -/
theorem initial_clean (initialW : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (state : RawCtxSharedPrimitive.SharedState (Local A N C) × Log) :
    ∀ result ∈ support ((keepLog (taggedInitialCall pre application initialW selector aux fixed selectedMessage other secrets)).run state),
      ∀ kernel, result.1 = some kernel → Clean kernel := by
  intro result supported kernel found
  change result ∈ support ((fun reply => (reply.1, (reply.2, state.2))) <$>
    (taggedInitialCall pre application initialW selector aux fixed selectedMessage other secrets).run state.1) at supported
  rw [support_map] at supported
  obtain ⟨inner, innerSupported, rfl⟩ := supported
  unfold taggedInitialCall at innerSupported
  split at innerSupported
  · rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at innerSupported
    subst innerSupported
    simp only [Option.some.injEq] at found
    subst found
    exact hidden_clean other
  · rw [StateT.run_map, support_map] at innerSupported
    obtain ⟨value, _, rfl⟩ := innerSupported
    cases reply : value.1 with
    | none => simp [reply] at found
    | some native =>
      simp only [reply, Option.map_some, Option.some.injEq] at found
      subst found
      exact known_clean native

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput) (decode : RawCtxReceive.FrameDecoder)

/-- The postcondition of a coupled attempted finish with its hit output: a logged selected value, or represented replies and Beacons with states equal up to the audit and no hit. -/
def HitPost (target : RootOutput)
    (left : (PqxdhSelectedInitialOwnerCompiler.Reply I D K × Bool) × RawCtxSharedPrimitive.SharedState (Local A N C))
    (right : (Option Pqxdh.Bytes × BeaconState TKernel I D K) × (RawCtxSharedPrimitive.SharedState (Local A N C) × Log)) : Prop :=
  Logged target right.2 ∨
    (left.1.1 = Prod.map id (mapBeacon (mapKernel target)) right.1 ∧ Near left.2 right.2 ∧ left.1.2 = false)

/-- An attempted finish of the concrete source post with its hit output, on a represented Beacon, and the target-free finish on the tagged Beacon are coupled so that a hit logs the selected value. -/
theorem owner_hit_coupled (initialC initialW : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N C PqxdhInitialNativeAudit.InitialReply) (target : RootOutput)
    (marked : ∀ secrets, PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets = true →
      ∀ first : RawCtxSharedPrimitive.SharedState (Local A N C), ∀ result ∈ support ((PqxdhSelectedInitialOwnerCompiler.sourceExternal
        (X := X) pre application initialC selector aux (.inr (.inr (.inl secrets)))).run first),
        result.1.map PqxdhSelectedMessageBeacon.knownKernel = some (mapKernel target (hiddenKernel other)) ∧
          strip result.2.1 = strip first.1 ∧ result.2.2 = first.2)
    (unmarked : ∀ secrets, PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets = false → initialC secrets = initialW secrets)
    (raw : Pqxdh.Bytes) (before : BeaconState TKernel I D K)
    (first : RawCtxSharedPrimitive.SharedState (Local A N C))
    (second : RawCtxSharedPrimitive.SharedState (Local A N C) × Log) (near : Near first second) :
    RelTriple ((simulateQ (PqxdhSelectedInitialOwnerCompiler.source pre application initialC selector aux source writer prior none key
        target nonce next decode) (ownerHit (extra := extra) (X := X) (Response := Response) prior target nonce next decode raw
          (mapBeacon (mapKernel target) before))).run first)
      ((taggedFinish source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage other
        raw before).run second)
      (HitPost target) := by
  unfold ownerHit taggedFinish
  cases phase : before.beacon.phase with
  | initSent control prekey oneTime kem =>
    have concretePhase : (mapBeacon (mapKernel target) before).beacon.phase = .initSent control prekey oneTime kem := by
      simp [mapBeacon, phase, mapPhase]
    simp only [concretePhase, simulateQ_bind, StateT.run_bind]
    refine relTriple_bind (prepare_coupled source writer prior key nonce next decode pre application selector aux initialC initialW target
      (PqxdhBeaconPhase2Shared.prepare control before.beacon.identity prekey oneTime kem raw) first second near) ?_
    rintro ⟨prepared, middle⟩ ⟨prepared', middle'⟩ ⟨equal, closer⟩
    simp only at equal
    subst equal
    cases prepared with
    | none =>
      simp only [simulateQ_pure, StateT.run_pure]
      refine relTriple_pure_pure (Or.inr ⟨?_, closer, rfl⟩)
      simpa using PqxdhInitialGenericBeacon.finish_map (mapKernel target) control before none
    | some pending =>
      dsimp only
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      refine relTriple_bind (support_right (initial_step pre application selector aux fixed selectedMessage other initialC initialW target
        marked unmarked pending.root middle middle' closer)) ?_
      rintro ⟨kernelC, middle2⟩ ⟨kernelW, middle2'⟩ ⟨⟨related, closer2⟩, reachedW⟩
      cases kernelC with
      | none =>
        cases kernelW with
        | none =>
          simp only [simulateQ_pure, StateT.run_pure]
          refine relTriple_pure_pure (Or.inr ⟨?_, closer2, rfl⟩)
          simpa using PqxdhInitialGenericBeacon.finish_map (mapKernel target) control before none
        | some kernelW => simp at related
      | some kernelC =>
        cases kernelW with
        | none => simp at related
        | some kernelW =>
          have clean := initial_clean pre application selector aux fixed selectedMessage other initialW pending.root middle' _ reachedW
            kernelW rfl
          simp only [Option.map_some, Option.some.injEq] at related
          dsimp only
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
          refine relTriple_bind (restores_exact _ (local_restores (application pending.response)) middle2 middle2' closer2) ?_
          rintro ⟨reply, middle3⟩ ⟨reply', middle3'⟩ ⟨equal, closer3⟩
          simp only at equal
          subst equal
          dsimp only
          simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, PqxdhSelectedInitialOwnerCompiler.source]
          rw [related]
          cases reply with
          | none =>
            simp only [map_pure, StateT.run_pure, pure_bind]
            refine relTriple_pure_pure (Or.inr ⟨?_, closer3, ?_⟩)
            · simpa using PqxdhInitialGenericBeacon.finish_map (mapKernel target) control before none
            · exact @decide_eq_false _ (Classical.propDecidable _) not_false
          | some delivered =>
            simp only [bind_pure_comp, StateT.run_map]
            by_cases hit : HitRaw prior target nonce next decode (PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata)
                (mapKernel target kernelW) delivered
            · refine relTriple_map (relTriple_post_mono (product_coupling (P := fun _ => True) (fun _ _ => trivial)
                (stage_hit source writer prior key nonce next target decode _ kernelW delivered clean hit middle3')) ?_)
              intro _ _ held
              exact Or.inl held.2
            · have staging := stage_coupled source writer prior key nonce next decode target
                (PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata) kernelW delivered middle3 middle3' closer3
              rw [StateT.run_map] at staging
              rw [Functor.map_map]
              refine relTriple_map (relTriple_post_mono staging ?_)
              intro left right held
              rcases held with bad | ⟨staged, closer4⟩
              · exact Or.inl bad
              · refine Or.inr ⟨?_, closer4, ?_⟩
                · simp only [staged]
                  exact PqxdhInitialGenericBeacon.finish_map (mapKernel target) control before right.1
                · simp only [decide_eq_false_iff_not]
                  exact hit
  | fresh _ _ _ | freshWithCoins _ _ _ _ | established _ _ _ | aborted _ =>
    simp only [mapBeacon, phase, mapPhase, simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure (Or.inr ⟨by simp [mapBeacon, phase, mapPhase], near, rfl⟩)

end TaggedHit

section HitObserved
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily RawCtxSelectedMessageDriver
open PqxdhSelectedPostCompiler (Optional)
variable {ι M P I D K X Response A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)

/-- Erasing the hit output gives the attempted finish. -/
theorem ownerHit_erase {Shared : Type} (raw : Pqxdh.Bytes) (before : PqxdhSelectedInitialOwnerCompiler.Beacon I D K) :
    Prod.fst <$> ownerHit (extra := extra) (X := X) (Response := Response) (Shared := Shared) prior target nonce next decode raw before =
      PqxdhSelectedInitialOwnerCompiler.owner raw before := by
  unfold ownerHit PqxdhSelectedInitialOwnerCompiler.owner
  cases before.beacon.phase with
  | initSent control prekey oneTime kem =>
    simp only [map_bind]
    refine bind_congr fun prepared => ?_
    cases prepared with
    | none => simp only [map_pure]
    | some pending =>
      simp only [map_bind]
      refine bind_congr fun kernel => ?_
      cases kernel with
      | none => simp only [map_pure]
      | some kernel =>
        simp only [map_bind, Functor.map_map, id_map']
  | _ => simp only [map_pure]

/-- The history-extended source post with a sticky hit flag: an attempted finish raises the flag when its application delivery reaches the selected material; every other request keeps it. -/
noncomputable def hitObserved :
    QueryImpl (Optional (PqxdhInitialGenericPost.Spec extra S B)) (StateT (Concrete M P I D K A N C S B × Bool) ProbComp)
  | .inl request => fun before => (fun result => (result.1, (result.2, before.2))) <$>
      ((PqxdhFirstRecordNonceStop.sourceObserved (extra := extra) pre application initial selector aux source writer prior none key
        target nonce next sender route decode) (.inl request)).run before.1
  | .inr (.finish index raw) => fun before =>
      (fun result => (some result.1.1.1, ((before.1.1 ++ [],
          (PqxdhSelectedPostCompiler.install index before.1.2.1 result.1.1.2, result.2)), before.2 || result.1.2))) <$>
        (simulateQ (PqxdhSelectedInitialOwnerCompiler.source pre application initial selector aux source writer prior none key target
          nonce next decode) (ownerHit prior target nonce next decode raw (before.1.2.1.roles.1.2 index))).run before.1.2.2

/-- Erasing the hit flag gives the history-extended source post. -/
theorem hit_erase (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain) (before : Concrete M P I D K A N C S B × Bool) :
    Prod.map id Prod.fst <$> (hitObserved pre application initial selector aux source writer prior key target nonce next sender route
      decode query).run before =
      ((PqxdhFirstRecordNonceStop.sourceObserved (extra := extra) pre application initial selector aux source writer prior none key
        target nonce next sender route decode) query).run before.1 := by
  rcases query with request | ⟨index, raw⟩
  · simp only [hitObserved, StateT.run, Functor.map_map, Prod.map_def, id_eq]
    exact id_map _
  · rw [PqxdhFirstRecordStopTagged.finish_source, ← ownerHit_erase prior target nonce next decode raw, simulateQ_map, StateT.run_map]
    simp only [hitObserved, StateT.run, Functor.map_map, Prod.map_def, id_eq]
    rfl

/-- A reached hit-flagged state erases to a reached history-extended source state. -/
theorem hit_support (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain) (before : Concrete M P I D K A N C S B × Bool)
    (result : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Range query × (Concrete M P I D K A N C S B × Bool))
    (supported : result ∈ support ((hitObserved pre application initial selector aux source writer prior key target nonce next sender
      route decode query).run before)) :
    (result.1, result.2.1) ∈ support (((PqxdhFirstRecordNonceStop.sourceObserved (extra := extra) pre application initial selector aux
      source writer prior none key target nonce next sender route decode) query).run before.1) := by
  rw [← hit_erase, support_map]
  exact ⟨result, supported, rfl⟩

end HitObserved

section HitCoupled
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily RawCtxSelectedMessageDriver
open PqxdhSelectedPostCompiler (Optional)
variable {ι M P I D K X Response A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : PqxdhCorrelatedExtractFamily.Message) (other : RootOutput)

/-- The concrete relation of the hit coupling: a represented concrete state with a lowered hit flag. -/
def HitRepresents (target : RootOutput) (first : Concrete M P I D K A N C S B × Bool) (second : TState M P I D K A N C S B) : Prop :=
  Represents target first.1 second ∧ first.2 = false

/-- An attempted finish of the hit-flagged source post and of the tagged world are coupled so that a hit logs the selected value. -/
theorem finish_hit_step (initialC initialW : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N C PqxdhInitialNativeAudit.InitialReply) (target : RootOutput)
    (marked : ∀ secrets, PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets = true →
      ∀ first : RawCtxSharedPrimitive.SharedState (Local A N C), ∀ result ∈ support ((PqxdhSelectedInitialOwnerCompiler.sourceExternal
        (X := X) pre application initialC selector aux (.inr (.inr (.inl secrets)))).run first),
        result.1.map PqxdhSelectedMessageBeacon.knownKernel = some (mapKernel target (hiddenKernel other)) ∧
          strip result.2.1 = strip first.1 ∧ result.2.2 = first.2)
    (unmarked : ∀ secrets, PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets = false → initialC secrets = initialW secrets)
    (index : Fin B) (raw : Pqxdh.Bytes) (first : Concrete M P I D K A N C S B × Bool) (second : TState M P I D K A N C S B)
    (related : HitRepresents target first second) :
    RelTriple (((hitObserved (extra := extra) pre application initialC selector aux source writer prior key target nonce next sender route
      decode) (.inr (.finish index raw))).run first)
      ((taggedFinishOp source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage other
        index raw).run second)
      (UpTo (HitRepresents target) (fun state => Disclosed target state.1) (Exposed target)) := by
  obtain ⟨⟨roles, controls, consumed, near, seals⟩, lowered⟩ := related
  have beacon : first.1.2.1.roles.1.2 index = mapBeacon (mapKernel target) (second.front.roles.2 index) := by
    rw [roles]
    rfl
  change RelTriple ((fun result => (some result.1.1.1, ((first.1.1 ++ [],
      (PqxdhSelectedPostCompiler.install index first.1.2.1 result.1.1.2, result.2)), first.2 || result.1.2))) <$>
    (simulateQ (PqxdhSelectedInitialOwnerCompiler.source pre application initialC selector aux source writer prior none key target
      nonce next decode) (ownerHit prior target nonce next decode raw (first.1.2.1.roles.1.2 index))).run first.1.2.2) _ _
  rw [beacon]
  refine relTriple_map (relTriple_post_mono (owner_hit_coupled pre application selector aux fixed selectedMessage other source writer
    prior key nonce next decode initialC initialW target marked unmarked raw (second.front.roles.2 index) first.1.2.2 second.shared
      near) ?_)
  intro left right held
  rcases held with bad | ⟨equal, closer, clear⟩
  · exact Or.inr (Or.inl bad)
  · refine Or.inr (Or.inr ⟨by rw [equal]; rfl, ⟨?_, controls, consumed, closer, by simpa using seals⟩, by simp [lowered, clear]⟩)
    simp only [PqxdhSelectedPostCompiler.install, equal, roles, mapRoles, Prod.map_snd]
    congr 1
    funext position
    by_cases same : position = index
    · subst same
      simp
    · simp [same]

/-- A request other than a finish keeps the hit flag. -/
theorem hit_keep (initialC : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N C PqxdhInitialNativeAudit.InitialReply) (target : RootOutput)
    (request : ((RawCtxProtocolReveals.SourceSpec S B) + extra).Domain) (before : Concrete M P I D K A N C S B × Bool) :
    ((hitObserved (extra := extra) pre application initialC selector aux source writer prior key target nonce next sender route decode)
      (.inl request)).run before =
      (fun result => (result.1, (result.2, before.2))) <$> ((PqxdhFirstRecordNonceStop.sourceObserved (extra := extra) pre application
        initialC selector aux source writer prior none key target nonce next sender route decode) (.inl request)).run before.1 := rfl

/-- A coupled request other than a finish stays coupled with a lowered hit flag. -/
theorem keep_step (initialC initialW : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (finishOp : (index : Fin B) → Pqxdh.Bytes → StateT (TState M P I D K A N C S B) ProbComp (Option (Option Pqxdh.Bytes)))
    (target : RootOutput) (request : ((RawCtxProtocolReveals.SourceSpec S B) + extra).Domain)
    (left : Concrete M P I D K A N C S B × Bool) (right : TState M P I D K A N C S B) (lowered : left.2 = false)
    (base : RelTriple (((PqxdhFirstRecordNonceStop.sourceObserved (extra := extra) pre application initialC selector aux source writer
        prior none key target nonce next sender route decode) (.inl request)).run left.1)
      ((world source writer prior key nonce next sender route decode pre application initialW selector aux finishOp (.inl request)).run
        right)
      (UpTo (Represents target) (Disclosed target) (Exposed target))) :
    RelTriple (((hitObserved (extra := extra) pre application initialC selector aux source writer prior key target nonce next sender
        route decode) (.inl request)).run left)
      ((world source writer prior key nonce next sender route decode pre application initialW selector aux finishOp (.inl request)).run
        right)
      (UpTo (HitRepresents target) (fun state => Disclosed target state.1) (Exposed target)) := by
  rw [hit_keep, ← id_map ((world source writer prior key nonce next sender route decode pre application initialW selector aux finishOp
    (.inl request)).run right)]
  refine relTriple_map (relTriple_post_mono base fun leftResult rightResult held => ?_)
  rcases held with bad | bad | ⟨equal, kept⟩
  · exact Or.inl bad
  · exact Or.inr (Or.inl bad)
  · exact Or.inr (Or.inr ⟨equal, kept, lowered⟩)

/-- The whole adaptive hit-flagged source post and the tagged world are coupled up to disclosure of the selected chain or a logged selected value, keeping the representation and a lowered hit flag. -/
theorem hit_coupled {Result : Type} (initialC initialW : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N C PqxdhInitialNativeAudit.InitialReply) (target : RootOutput)
    (marked : ∀ secrets, PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets = true →
      ∀ first : RawCtxSharedPrimitive.SharedState (Local A N C), ∀ result ∈ support ((PqxdhSelectedInitialOwnerCompiler.sourceExternal
        (X := X) pre application initialC selector aux (.inr (.inr (.inl secrets)))).run first),
        result.1.map PqxdhSelectedMessageBeacon.knownKernel = some (mapKernel target (hiddenKernel other)) ∧
          strip result.2.1 = strip first.1 ∧ result.2.2 = first.2)
    (unmarked : ∀ secrets, PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets = false → initialC secrets = initialW secrets)
    (client : OracleComp (Optional (PqxdhInitialGenericPost.Spec extra S B)) Result)
    (first : Concrete M P I D K A N C S B) (second : TState M P I D K A N C S B) (represents : Represents target first second) :
    RelTriple ((simulateQ (hitObserved (extra := extra) pre application initialC selector aux source writer prior key target nonce next
        sender route decode) client).run (first, false))
      ((simulateQ (world source writer prior key nonce next sender route decode pre application initialW selector aux
        (taggedFinishOp source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage other))
        client).run second)
      (UpTo (HitRepresents target) (fun state => Disclosed target state.1) (Exposed target)) := by
  refine coupled_run _ _ _ _ _ ?_
    (exposed_absorbing source writer prior key nonce next sender route decode pre application selector aux initialW
      (taggedFinishOp source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage other)
      target (finish_keeps source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage other
        target))
    (fun query left right related _ _ => ?_) client (first, false) second (Or.inr (Or.inr ⟨represents, rfl⟩))
  · intro query state disclosed result supported
    exact disclosed_absorbing source writer prior key nonce next sender route decode pre application initialC selector aux target query
      state.1 disclosed (result.1, result.2.1) (hit_support pre application initialC selector aux source writer prior key target nonce
        next sender route decode query state result supported)
  · obtain ⟨leftRepresents, lowered⟩ := related
    rcases query with ((request | request) | request) | ⟨index, raw⟩
    · exact keep_step source writer prior key nonce next sender route decode pre application selector aux initialC initialW _ target
        _ left right lowered (record_step source writer prior key nonce next sender route decode pre application initialC selector aux
          initialW _ target request left.1 right leftRepresents)
    · exact keep_step source writer prior key nonce next sender route decode pre application selector aux initialC initialW _ target
        _ left right lowered (reveal_step source writer prior key nonce next sender route decode pre application initialC selector aux
          initialW _ target request left.1 right leftRepresents)
    · exact keep_step source writer prior key nonce next sender route decode pre application selector aux initialC initialW _ target
        _ left right lowered (selector_step source writer prior key nonce next sender route decode pre application initialC selector aux
          initialW _ target request left.1 right leftRepresents)
    · exact finish_hit_step source writer prior key nonce next sender route decode pre application selector aux fixed selectedMessage
        other initialC initialW target marked unmarked index raw left right ⟨leftRepresents, lowered⟩

/-- A hit of the hit-flagged source post while the selected chain stays undisclosed has at most the probability that the tagged world logs the selected value, from represented start states. -/
theorem hit_bound {Result : Type} (initialC initialW : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N C PqxdhInitialNativeAudit.InitialReply) (target : RootOutput)
    (marked : ∀ secrets, PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets = true →
      ∀ first : RawCtxSharedPrimitive.SharedState (Local A N C), ∀ result ∈ support ((PqxdhSelectedInitialOwnerCompiler.sourceExternal
        (X := X) pre application initialC selector aux (.inr (.inr (.inl secrets)))).run first),
        result.1.map PqxdhSelectedMessageBeacon.knownKernel = some (mapKernel target (hiddenKernel other)) ∧
          strip result.2.1 = strip first.1 ∧ result.2.2 = first.2)
    (unmarked : ∀ secrets, PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets = false → initialC secrets = initialW secrets)
    (client : OracleComp (Optional (PqxdhInitialGenericPost.Spec extra S B)) Result)
    (first : Concrete M P I D K A N C S B) (second : TState M P I D K A N C S B) (represents : Represents target first second) :
    RelTriple ((simulateQ (hitObserved (extra := extra) pre application initialC selector aux source writer prior key target nonce next
        sender route decode) client).run (first, false))
      ((simulateQ (world source writer prior key nonce next sender route decode pre application initialW selector aux
        (taggedFinishOp source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage other))
        client).run second)
      (fun left right => left.2.2 = true ∧ ¬ Disclosed target left.2.1 → Exposed target right.2) := by
  refine relTriple_post_mono (hit_coupled source writer prior key nonce next sender route decode pre application selector aux fixed
    selectedMessage other initialC initialW target marked unmarked client first second represents) ?_
  intro left right held holds
  rcases held with disclosed | exposed | ⟨_, _, lowered⟩
  · exact absurd disclosed holds.2
  · exact exposed
  · rw [lowered] at holds
    exact absurd holds.1 Bool.false_ne_true

end HitCoupled

section MarkRaw
open AdaptiveCtxDynamicKnownKeys (Spec)
open PqxdhFirstRecordConfidentiality (IsRaw markRaw markRaw_run)

/-- A program without selected raw openings keeps the `markRaw` flag. -/
theorem markRaw_quiet {α : Type} (work : OracleComp Spec α) (quiet : work.IsQueryBoundP IsRaw 0) (flag : Bool) :
    ∀ result ∈ support ((simulateQ markRaw work).run flag), result.2 = flag := by
  induction work using OracleComp.inductionOn generalizing flag with
  | pure value =>
    intro result supported
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    rw [supported]
  | query_bind query next ih =>
    intro result supported
    rw [isQueryBoundP_query_bind_iff] at quiet
    have notRaw : ¬ IsRaw query := by
      rcases quiet.1 with notRaw | impossible
      · exact notRaw
      · exact absurd impossible (Nat.lt_irrefl 0)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, markRaw_run, bind_map_left, mem_support_bind_iff] at supported
    obtain ⟨reply, _, rest⟩ := supported
    have kept : (flag || decide (IsRaw query)) = flag := by simp [notRaw]
    rw [kept] at rest
    have bounded := quiet.2 reply
    simp only [notRaw, ite_false] at bounded
    exact ih reply bounded flag result rest

/-- A reached `markRaw` run of a sequenced program passes through a reached run of its first part. -/
theorem markRaw_bind {α β : Type} (first : OracleComp Spec α) (rest : α → OracleComp Spec β) (flag : Bool)
    (result : β × Bool) (supported : result ∈ support ((simulateQ markRaw (first >>= rest)).run flag)) :
    ∃ middle ∈ support ((simulateQ markRaw first).run flag), result ∈ support ((simulateQ markRaw (rest middle.1)).run middle.2) := by
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  exact supported

/-- A reached `markRaw` run of a mapped program is the mapped reached run. -/
theorem markRaw_map {α β : Type} (work : OracleComp Spec α) (function : α → β) (flag : Bool)
    (result : β × Bool) (supported : result ∈ support ((simulateQ markRaw (function <$> work)).run flag)) :
    ∃ middle ∈ support ((simulateQ markRaw work).run flag), result = (function middle.1, middle.2) := by
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨middle, reached, rfl⟩ := supported
  exact ⟨middle, reached, rfl⟩

/-- A `markRaw` run of a pure value keeps the flag. -/
theorem markRaw_pure {α : Type} (value : α) (flag : Bool) (result : α × Bool)
    (supported : result ∈ support ((simulateQ markRaw (pure value : OracleComp Spec α)).run flag)) : result = (value, flag) := by
  simpa only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] using supported

end MarkRaw

section Dominates
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf RawCtxSelectedParentTable PqxdhNativeSharedPrefix
open PqxdhSelectedInitialOwnerCompiler (Spec preForward Beacon Reply IsFinish)
open PqxdhFirstRecordConfidentiality (IsRaw markRaw)
variable {ι I D K X Response Shared A N C : Type} {extra : OracleSpec ι}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder)

/-- A compiled source-local request makes no selected raw opening. -/
theorem lower_external (query : (PqxdhSelectedCallbackCompiler.External extra I D K X Response Shared).Domain) (state : Local A N C) :
    ((PqxdhSelectedInitialOwnerCompiler.lower pre application initial selector aux prior none target nonce next read (.inl query)).run
      state).IsQueryBoundP IsRaw 0 :=
  lower_quiet prior target nonce next read pre application initial selector aux (.inl query) (fun _ impossible => by cases impossible)
    state

/-- The compiled preparation of an attempted finish makes no selected raw opening. -/
theorem lower_prepare {β : Type} (work : OracleComp (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) β) (state : Local A N C) :
    ((simulateQ (PqxdhSelectedInitialOwnerCompiler.lower pre application initial selector aux prior none target nonce next read)
      (simulateQ (preForward (extra := extra)) work)).run state).IsQueryBoundP IsRaw 0 := by
  classical
  have forwarded : (simulateQ (preForward (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response)
      (Shared := Shared)) work).IsQueryBoundP (IsFinish (extra := extra)) 0 :=
    (isQueryBoundP_false _ 0).simulateQ_of_step
      (impl := preForward) (q := IsFinish (extra := extra)) (fun _ impossible => False.elim impossible)
      (fun query _ => (isQueryBoundP_query_iff (spec := Spec extra I D K X Response Shared)
        (p := IsFinish (extra := extra)) (.inl (.inl query)) 0).mpr (by simp [IsFinish]))
  refine forwarded.simulateQ_run_of_step ?_ ?_ state
  · intro query finishing current
    cases query with
    | inl query => exact False.elim finishing
    | inr request =>
      simp only [PqxdhSelectedInitialOwnerCompiler.lower, StateT.run, isQueryBoundP_map_iff]
      exact IsQueryBoundP.of_imp (fun _ _ => True.intro)
        ((isQueryBoundP_true_iff _ _).mpr (PqxdhSelectedBeaconCompiler.finish_queries prior none target nonce next read
          request.control request.before request.candidate request.kernel request.application))
  · intro query notFinishing current
    cases query with
    | inl query => exact lower_external pre application initial selector aux prior target nonce next read query current
    | inr request => exact absurd True.intro notFinishing

/-- The `markRaw` flag of a compiled marked finish is raised only if it was raised before or the finish's application delivery reaches the selected material (its hit output). -/
theorem hit_dominates (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) (raw : Pqxdh.Bytes) (before : Beacon I D K)
    (state : Local A N C) (flag : Bool) :
    ∀ result ∈ support ((simulateQ markRaw ((simulateQ (PqxdhSelectedInitialOwnerCompiler.lower pre application initial selector aux
      prior none target nonce next read) (ownerMarkedHit (extra := extra) (X := X) (Response := Response) prior target nonce next read
        mark raw before)).run state)).run flag),
      result.2 = true → flag = true ∨ result.1.1.2 = true := by
  intro result supported raised
  unfold ownerMarkedHit at supported
  split at supported
  · rename_i control prekey oneTime kem _
    rw [simulateQ_bind, StateT.run_bind] at supported
    obtain ⟨first, firstReached, supported⟩ := markRaw_bind _ _ _ _ supported
    have firstKept := markRaw_quiet _ (lower_prepare pre application initial selector aux prior target nonce next read _ state) flag
      first firstReached
    rw [firstKept] at supported
    rcases first with ⟨⟨_ | pending, middle⟩, _⟩
    · have same := markRaw_pure _ _ _ (by simpa only [simulateQ_pure, StateT.run_pure] using supported)
      subst same
      exact Or.inl raised
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨second, secondReached, supported⟩ := supported
      have secondKept := markRaw_quiet _ (lower_external pre application initial selector aux prior target nonce next read _ middle)
        flag second secondReached
      rw [secondKept] at supported
      rcases second with ⟨⟨_ | kernel, middle2⟩, _⟩
      · have same := markRaw_pure _ _ _ (by simpa only [simulateQ_pure, StateT.run_pure] using supported)
        subst same
        exact Or.inl raised
      · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
        obtain ⟨third, thirdReached, supported⟩ := supported
        have thirdKept := markRaw_quiet _ (lower_external pre application initial selector aux prior target nonce next read _ middle2)
          flag third thirdReached
        rw [thirdKept] at supported
        simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map, Set.mem_image] at supported
        obtain ⟨fourth, fourthReached, rfl⟩ := supported
        by_cases hit : HitReq prior target nonce next read (⟨control, before, PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata,
            PqxdhSelectedMessageBeacon.knownKernel kernel, third.1.1⟩ : PqxdhSelectedInitialOwnerCompiler.Request I D K)
        · exact Or.inr (@decide_eq_true _ (Classical.propDecidable _) hit)
        · have fourthKept := markRaw_quiet _ (lower_quiet prior target nonce next read pre application initial selector aux _
            (fun request same => by rw [← Sum.inr.inj same]; exact hit) third.1.2) flag fourth fourthReached
          exact Or.inl (fourthKept ▸ raised)
  · have same := markRaw_pure _ _ _ (by simpa only [simulateQ_pure, StateT.run_pure] using supported)
    subst same
    exact Or.inl raised

end Dominates

section AugCoupling
open OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhNativeSharedPrefix
open PqxdhSelectedPostCompiler (Optional)
open PqxdhFirstRecordConfidentiality (InsFull insAugmented insEvaluated insImpl insErase markRaw)
variable {ι M P I D K X Response A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (mark : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared → Bool) (b : Fin B)

/-- A computation is coupled with its own image, related pointwise on its support. -/
theorem relTriple_self_map {α β : Type} (work : ProbComp α) (function : α → β) (related : α → β → Prop)
    (holds : ∀ value ∈ support work, related value (function value)) : RelTriple work (function <$> work) related := by
  have mapped := relTriple_map (f := id) (g := function)
    (relTriple_refl_of_mem_support work (R := fun first second => related (id first) (function second)) holds)
  simpa only [id_map] using mapped

/-- The relation between an instrumented compiled state and a hit-flagged source state: the compiled state projects to the source state, and a raised finish raw flag implies a raised hit flag. -/
def AugRel (first : InsFull M P I D K A N C S B) (second : Concrete M P I D K A N C S B × Bool) : Prop :=
  PqxdhSelectedPostCompiler.project (insErase first) = second.1.2 ∧ (first.1.2.2.2 = true → second.2 = true)

/-- Every request other than a finish keeps the finish raw flag of the instrumented augmented post. -/
theorem aug_flag (request : ((RawCtxProtocolReveals.SourceSpec S B) + extra).Domain) (first : InsFull M P I D K A N C S B) :
    ∀ result ∈ support ((insAugmented pre application initial selector aux source writer prior none key target nonce next sender route
      decode mark b (.inl request)).run first), result.2.1.2.2.2 = first.1.2.2.2 := by
  intro result supported
  rcases request with request | request
  · simp only [insAugmented, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨_, _, rfl⟩ := supported
    rfl
  · change result ∈ support (PqxdhSelectedStateInterpreter.pair <$> (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true
      (RawCtxUniversalDecoder.decoder decode) source.crypto key) (((insImpl pre application initial selector aux source writer prior
        none target nonce next sender route decode mark b (.inl (.inr request))).run).run first.1)).run first.2) at supported
    rw [support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    change inner ∈ support ((simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder decode)
      source.crypto key) ((fun result => (some result.1, ((first.1.1.1, result.2), first.1.2))) <$>
        (PqxdhSelectedCallbackCompiler.lower pre application initial selector aux
          (.inl (.inr (.inr (.inr (.inl request)))))).run first.1.1.2)).run first.2) at reached
    rw [simulateQ_map, StateT.run_map, support_map] at reached
    obtain ⟨_, _, rfl⟩ := reached
    rfl

/-- A request other than a finish of the instrumented augmented post and of the hit-flagged source post are coupled with equal replies and related states. -/
theorem aug_keep (request : ((RawCtxProtocolReveals.SourceSpec S B) + extra).Domain) (first : InsFull M P I D K A N C S B)
    (second : Concrete M P I D K A N C S B × Bool) (related : AugRel first second) :
    RelTriple ((insAugmented pre application initial selector aux source writer prior none key target nonce next sender route decode
        mark b (.inl request)).run first)
      ((hitObserved (extra := extra) pre application initial selector aux source writer prior key target nonce next sender route decode
        (.inl request)).run second)
      (fun left right => left.1 = right.1 ∧ AugRel left.2 right.2) := by
  obtain ⟨projected, flagged⟩ := related
  have erased := PqxdhFirstRecordConfidentiality.insAugmented_erase pre application initial selector aux source writer prior none key
    target nonce next sender route decode mark b (.inl request) first
  have stepped := PqxdhSelectedPostCompiler.augmented_step pre application initial selector aux source writer prior none key target
    nonce next sender route decode (.inl request) (insErase first)
  rw [← erased, Functor.map_map] at stepped
  rw [hit_keep]
  change RelTriple _ ((fun result => (result.1, (result.2, second.2))) <$>
    ((fun result => (result.1, (second.1.1 ++ PqxdhFirstRecordNonceStop.sourceEvents prior none target nonce next sender
      (.inl request) second.1.2, result.2))) <$> (PqxdhSelectedPostCompiler.original pre application initial selector aux source
        writer prior none key target nonce next sender route decode (.inl request)).run second.1.2)) _
  rw [← projected, ← stepped, Functor.map_map, Functor.map_map]
  refine relTriple_self_map _ _ _ fun result supported => ?_
  refine ⟨rfl, rfl, fun raised => flagged ?_⟩
  rw [← aug_flag pre application initial selector aux source writer prior key target nonce next sender route decode mark b request
    first result supported]
  exact raised

/-- An attempted finish of the instrumented augmented post and of the hit-flagged source post are coupled with equal replies and related states: both are images of one evaluated marked run of the finish with its hit output, and a raised raw flag implies a raised hit (`hit_dominates`). -/
theorem aug_finish (index : Fin B) (raw : Pqxdh.Bytes) (first : InsFull M P I D K A N C S B)
    (second : Concrete M P I D K A N C S B × Bool) (related : AugRel first second) :
    RelTriple ((insAugmented pre application initial selector aux source writer prior none key target nonce next sender route decode
        mark b (.inr (.finish index raw))).run first)
      ((hitObserved (extra := extra) pre application initial selector aux source writer prior key target nonce next sender route decode
        (.inr (.finish index raw))).run second)
      (fun left right => left.1 = right.1 ∧ AugRel left.2 right.2) := by
  obtain ⟨projected, flagged⟩ := related
  obtain ⟨⟨history, sourceState⟩, flag⟩ := second
  simp only at projected flagged
  subst projected
  change RelTriple (PqxdhSelectedStateInterpreter.pair <$> (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true
      (RawCtxUniversalDecoder.decoder decode) source.crypto key)
      ((fun result => (some result.1.1.1.1, ((PqxdhSelectedPostCompiler.install index first.1.1.1 result.1.1.1.2, result.1.2),
        (PqxdhInitialOriginPost.finish first.1.2.1 index result.1.1.2, first.1.2.2.1, result.2)))) <$>
        (simulateQ markRaw ((simulateQ (PqxdhSelectedInitialOwnerCompiler.lower pre application initial selector aux prior none target
          nonce next decode) (PqxdhFirstRecordConfidentiality.ownerMarked mark raw (first.1.1.1.roles.1.2 index))).run
            first.1.1.2)).run first.1.2.2.2)).run first.2)
    ((fun result => (some result.1.1.1, ((history ++ [],
        (PqxdhSelectedPostCompiler.install index first.1.1.1 result.1.1.2, result.2)), flag || result.1.2))) <$>
      (simulateQ (PqxdhSelectedInitialOwnerCompiler.source pre application initial selector aux source writer prior none key target
        nonce next decode) (ownerHit prior target nonce next decode raw (first.1.1.1.roles.1.2 index))).run
          (RawCtxSelectedReceiveCompiler.project (first.1.1.2, first.2)))
    (fun (left : Option (Option Pqxdh.Bytes) × InsFull M P I D K A N C S B)
      (right : Option (Option Pqxdh.Bytes) × (Concrete M P I D K A N C S B × Bool)) => left.1 = right.1 ∧ AugRel left.2 right.2)
  rw [← ownerMarkedHit_erase prior target nonce next decode mark raw, ← ownerMarkedHit_hit prior target nonce next decode mark raw]
  simp only [simulateQ_map, StateT.run_map]
  rw [← PqxdhSelectedInitialOwnerCompiler.program_source]
  have evaluated := PqxdhFirstRecordConfidentiality.markRaw_evaluate (AdaptiveCtxDynamicKnownKeys.sourceImpl true
    (RawCtxUniversalDecoder.decoder decode) source.crypto key) ((simulateQ (PqxdhSelectedInitialOwnerCompiler.lower pre application
      initial selector aux prior none target nonce next decode) (ownerMarkedHit prior target nonce next decode mark raw
        (first.1.1.1.roles.1.2 index))).run first.1.1.2) first.1.2.2.2 first.2
  simp only [PqxdhSelectedStateInterpreter.evaluate, StateT.run] at evaluated ⊢
  rw [← evaluated]
  simp only [Functor.map_map]
  refine relTriple_map (relTriple_refl_of_mem_support _ fun result reached => ?_)
  refine ⟨rfl, rfl, fun raised => ?_⟩
  have inner : result.1 ∈ support ((simulateQ markRaw ((simulateQ (PqxdhSelectedInitialOwnerCompiler.lower pre application initial
      selector aux prior none target nonce next decode) (ownerMarkedHit prior target nonce next decode mark raw
        (first.1.1.1.roles.1.2 index))).run first.1.1.2)).run first.1.2.2.2) := by
    refine support_simulateQ_run'_subset (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder decode)
      source.crypto key) _ first.2 ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨result, reached, rfl⟩
  rcases hit_dominates pre application initial selector aux prior target nonce next decode mark raw _ _ _ result.1 inner raised with
    old | hit
  · exact Bool.or_eq_true_iff.mpr (Or.inl (flagged old))
  · exact Bool.or_eq_true_iff.mpr (Or.inr hit)

/-- The whole instrumented augmented post and the hit-flagged source post are coupled with equal replies and related states. -/
theorem aug_run {Result : Type} (client : OracleComp (Optional (PqxdhInitialGenericPost.Spec extra S B)) Result)
    (first : InsFull M P I D K A N C S B) (second : Concrete M P I D K A N C S B × Bool) (related : AugRel first second) :
    RelTriple ((simulateQ (insAugmented pre application initial selector aux source writer prior none key target nonce next sender route
        decode mark b) client).run first)
      ((simulateQ (hitObserved (extra := extra) pre application initial selector aux source writer prior key target nonce next sender
        route decode) client).run second)
      (fun left right => left.1 = right.1 ∧ AugRel left.2 right.2) := by
  refine relTriple_post_mono (coupled_run _ _ AugRel (fun _ => False) (fun _ => False) (fun _ _ impossible => impossible.elim)
    (fun _ _ impossible => impossible.elim) (fun query left right held _ _ => ?_) client first second (Or.inr (Or.inr related))) ?_
  · refine relTriple_post_mono ?_ fun _ _ held => Or.inr (Or.inr held)
    rcases query with request | ⟨index, raw⟩
    · exact aug_keep pre application initial selector aux source writer prior key target nonce next sender route decode mark b request
        left right held
    · exact aug_finish pre application initial selector aux source writer prior key target nonce next sender route decode mark b index
        raw left right held
  · intro _ _ held
    rcases held with impossible | impossible | held
    · exact impossible.elim
    · exact impossible.elim
    · exact held

set_option linter.deprecated false in
/-- An output of the instrumented augmented post that requires a raised finish raw flag and an undisclosed selected chain has at most the probability of a hit with the selected chain undisclosed in the hit-flagged source post. -/
theorem aug_hit (client : OracleComp (Optional (PqxdhInitialGenericPost.Spec extra S B)) (Option Bool))
    (out : Option Bool × InsFull M P I D K A N C S B → Bool)
    (implies : ∀ result, out result = true →
      result.2.1.2.2.2 = true ∧ RawCtxFreshChainCut.concreteChain target ∉ RawCtxSelectedMessageFreshness.known [] result.2.1.1.1.roles.2)
    (first : InsFull M P I D K A N C S B) (history : PqxdhFirstRecordNonceStop.History S B) :
    𝒟[out <$> (simulateQ (insAugmented pre application initial selector aux source writer prior none key target nonce next sender route
        decode mark b) client).run first] {true} ≤
      𝒟[(fun result => @decide (result.2.2 = true ∧ ¬ Disclosed target result.2.1) (Classical.propDecidable _)) <$>
        (simulateQ (hitObserved (extra := extra) pre application initial selector aux source writer prior key target nonce next sender
          route decode) client).run ((history, PqxdhSelectedPostCompiler.project (insErase first)), first.1.2.2.2)] {true} := by
  simp only [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map]
  refine probEvent_le_of_relTriple (aug_run pre application initial selector aux source writer prior key target nonce next sender route
    decode mark b client first _ ⟨rfl, id⟩) fun left right held holds => ?_
  obtain ⟨raised, fresh⟩ := implies left holds
  obtain ⟨_, projected, flagged⟩ := held
  simp only [Function.comp_apply, decide_eq_true_eq]
  refine ⟨flagged raised, fun disclosed => fresh ?_⟩
  have front := congrArg Prod.fst projected
  simp only [PqxdhSelectedPostCompiler.project, insErase] at front
  unfold Disclosed at disclosed
  rw [← front] at disclosed
  exact disclosed

end AugCoupling

section HitRun
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhNativeSharedPrefix PqxdhCorrelatedExpand
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily
open PqxdhSelectedPostCompiler (Optional)
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (selectedMessage : PqxdhCorrelatedExtractFamily.Message)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
    (before : PqxdhInitialOriginPostPath.Front M P I D K S B)
    (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)
    (store : RawCtxSelectiveChainGame.Store)

/-- The source-only finish-hit run: after the selected first Server builder, the hit-flagged history-extended source post runs from the builder's front and local state, and the event is that some attempted finish reached the selected material while, at the end, the selected chain is undisclosed. -/
noncomputable def hitRun (initial : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply)
    (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response) (selected : RawCtxProtocolReveals.Owner S B)
    (key : RootOutput) (nonce : NonceOutput) (next : RootOutput) : ProbComp Bool := do
  let built ← PqxdhFirstBeaconRecordIntegrity.firstBuild pre application initial selector aux source writer previousRoot response64
    sender index metadata ready before selected shared privateState cache store key nonce next
  (fun result => @decide (result.2.2 = true ∧
      ¬ Disclosed (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) result.2.1) (Classical.propDecidable _)) <$>
    (simulateQ (hitObserved pre application initial selector aux source writer (PqxdhJointKdf.productionStream source.crypto) key
      (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) nonce next sender route decode)
      (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run (([], (built.1.2, built.2)), false)

set_option linter.deprecated false in
/-- The source-only finish-hit run of a Beacon owner, with initializer response `other ++ target`, is at most the probability that `target` is in the final log of the target-free tagged run of `PqxdhFirstRecordStopTagged`. -/
theorem hit_tagged (other target key : RootOutput) (nonce : NonceOutput) (next : RootOutput) (b : Fin B) :
    𝒟[hitRun pre application selector aux source writer sender route decode index metadata ready post before shared privateState cache
        store (initialLocal source selectedMessage (List.Vector.replicate 32 0) (RawCtxSelectedInitialConstructor.response64 (other ++ target)))
        (List.Vector.replicate 32 0) (RawCtxSelectedInitialConstructor.response64 (other ++ target)) (.beacon b) key nonce next] {true} ≤
      Pr[fun log => target ∈ log | taggedRun pre application selector aux source writer selectedMessage sender route decode index metadata
        ready post before shared privateState cache store other key nonce next] := by
  unfold hitRun PqxdhFirstBeaconRecordIntegrity.firstBuild taggedRun
  rw [beacon_root]
  refine bind_event_le _ _ _ _ _ _ target ?_
  rw [← build_initial pre application selector aux source writer (PqxdhJointKdf.productionStream source.crypto) key nonce next sender
    (initialLocal source selectedMessage (List.Vector.replicate 32 0) (RawCtxSelectedInitialConstructor.response64 (other ++ target)))
    (initialFree source selectedMessage other) other index metadata ready]
  refine relTriple_bind (build_coupled source writer (PqxdhJointKdf.productionStream source.crypto) key nonce next sender pre application
    (initialLocal source selectedMessage (List.Vector.replicate 32 0) (RawCtxSelectedInitialConstructor.response64 (other ++ target)))
    selector aux target other index metadata ready (PqxdhSelectedFirstRecord.initialFront before)
    (frontOf (PqxdhSelectedFirstRecord.initialFront before)) (front_rep target _)
    (PqxdhSelectedFirstRecord.initialShared shared privateState cache store)
    (PqxdhSelectedFirstRecord.initialShared shared privateState cache store, []) ⟨rfl, rfl⟩ (List.not_mem_nil)) ?_
  intro left right held
  rcases held with bad | ⟨⟨sameReply, sameFront⟩, near⟩
  · refine relTriple_post_mono (product_coupling (P := fun _ => True) (fun _ _ => trivial)
      (run_absorbing _ (Exposed target) (exposed_absorbing source writer (PqxdhJointKdf.productionStream source.crypto) key nonce next
        sender route decode pre application selector aux (initialFree source selectedMessage other) _ target
        (finish_keeps source writer (PqxdhJointKdf.productionStream source.crypto) key nonce next decode pre application
          (initialFree source selectedMessage other) selector aux source selectedMessage other target)) _ _ bad)) ?_
    intro _ _ held _
    exact held.2
  · rw [sameReply]
    refine relTriple_post_mono (hit_bound source writer (PqxdhJointKdf.productionStream source.crypto) key nonce next sender route decode
      pre application selector aux source selectedMessage other
      (initialLocal source selectedMessage (List.Vector.replicate 32 0) (RawCtxSelectedInitialConstructor.response64 (other ++ target)))
      (initialFree source selectedMessage other) target
      (fun secrets selected start result supported => initial_marked pre application selector aux source selectedMessage other target
        secrets selected start result supported)
      (fun secrets unmarkedMark => initial_unmarked source selectedMessage _ _ _ _ secrets unmarkedMark)
      _ ([], (left.1.2, left.2)) ⟨[], right.1.2, right.2⟩ ⟨sameFront.1, sameFront.2.1, sameFront.2.2, near, rfl⟩) ?_
    intro _ _ held holds
    exact held (@of_decide_eq_true _ (Classical.propDecidable _) holds)

end HitRun

section ClientOut
open PqxdhNativeSharedPrefix PqxdhSelectedStateInterpreter PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open RawCtxSelectedParentTable PqxdhSelectedFirstRecord PqxdhFirstBeaconRecordIntegrity PqxdhCorrelatedExpand
open PqxdhInitialBeaconAmbient PqxdhFirstBeaconRecordCtx
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (selectedMessage : PqxdhCorrelatedExtractFamily.Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
    (before : PqxdhInitialOriginPostPath.Front M P I D K S B) (selected : RawCtxProtocolReveals.Owner S B)
    (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)
    (store : RawCtxSelectiveChainGame.Store) (key : RootOutput) (nonce : NonceOutput) (next : RootOutput) (b : Fin B)

local notation "target" => PqxdhInitialSourceExperiment.root source previousRoot response64 selected
local notation "challenger" => AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder decode) source.crypto key

/-- For any output function of the instrumented compiled state, when every first send of the initial Server kernel is known, the selected builder followed by the instrumented post bit is the key-free instrumented first client evaluated by the selected-key challenger (the output-generic form of `PqxdhFirstRecordConfidentiality.insRun_client`). -/
theorem insRun_client_out (out : Option Bool × PqxdhFirstRecordConfidentiality.InsState M P I D K A N RootOracle.QueryCache S B → Bool)
    (known : ∀ kernel, initialKernel response64 = .ok kernel → ∀ context,
      PqxdhFirstBeaconRecordCtx.KnownSend (productionStream source.crypto) none target nonce next kernel context)
    (log : List Pqxdh.Bytes) :
    (firstBuild pre application initial selector aux source writer previousRoot response64 sender index metadata ready
      before selected shared privateState cache store key nonce next >>= fun built =>
      PqxdhFirstRecordConfidentiality.insPostBit pre application initial selector aux source writer selectedMessage previousRoot response64
        sender route decode post selected key nonce next b out built.1.1 (PqxdhFirstRecordConfidentiality.insStart index built)) =
      Prod.fst <$> (simulateQ challenger (PqxdhFirstRecordConfidentiality.insFirstClient pre application initial selector aux source writer selectedMessage previousRoot
        response64 sender route decode index metadata ready post before selected shared privateState cache store nonce next b
        out)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log)) := by
  have related := build_rel pre application initial selector aux source writer (productionStream source.crypto) none key target
    nonce next decode sender (initialKernel response64) index metadata ready (initialFront before) known
    ((initialShared shared privateState cache store).1,
      RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log))
  simp only [evaluate, StateT.run] at related
  have clientEq : Prod.fst <$> (simulateQ challenger (PqxdhFirstRecordConfidentiality.insFirstClient pre application initial selector aux source writer selectedMessage
      previousRoot response64 sender route decode index metadata ready post before selected shared privateState cache store nonce next b
        out)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log)) =
      (simulateQ challenger (((compiledBuild pre application initial selector aux source writer (productionStream source.crypto) none
        target nonce next sender (initialKernel response64) index metadata ready).run (initialFront before)).run
          (initialShared shared privateState cache store).1)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log)) >>= fun result =>
        PqxdhFirstRecordConfidentiality.insPostBit pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode post
          selected key nonce next b out result.1.1.1
          (((result.1.1.2, result.1.2), (selectedAfter PqxdhInitialSourcePublication.empty result.1.1.2 index true result.1.1.1, none, false)),
            result.2) := by
    simp only [PqxdhFirstRecordConfidentiality.insFirstClient, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure]
    refine bind_congr fun result => ?_
    simp only [PqxdhFirstRecordConfidentiality.insPostBit, bind_pure_comp]
    change _ = (fun result => out (result.1, result.2.1)) <$>
      (pair <$> (simulateQ challenger (((simulateQ (PqxdhFirstRecordConfidentiality.insImpl pre application initial selector aux source writer
        (productionStream source.crypto) none target nonce next sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage)
          b) (post result.1.1.1)).run).run ((result.1.1.2, result.1.2),
            (selectedAfter PqxdhInitialSourcePublication.empty result.1.1.2 index true result.1.1.1, none, false)))).run result.2)
    rw [Functor.map_map]
    rfl
  have cleaned : ((simulateQ challenger (((compiledBuild pre application initial selector aux source writer
      (productionStream source.crypto) none target nonce next sender (initialKernel response64) index metadata ready).run
        (initialFront before)).run (initialShared shared privateState cache store).1)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log)) >>= fun result =>
        PqxdhFirstRecordConfidentiality.insPostBit pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode post
          selected key nonce next b out result.1.1.1
          (((result.1.1.2, result.1.2), (selectedAfter PqxdhInitialSourcePublication.empty result.1.1.2 index true result.1.1.1, none, false)),
            result.2)) =
      ((simulateQ challenger (((compiledBuild pre application initial selector aux source writer
      (productionStream source.crypto) none target nonce next sender (initialKernel response64) index metadata ready).run
        (initialFront before)).run (initialShared shared privateState cache store).1)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log)) >>= fun result =>
        PqxdhFirstRecordConfidentiality.insPostBit pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode post
          selected key nonce next b out result.1.1.1
          (((result.1.1.2, result.1.2), (selectedAfter PqxdhInitialSourcePublication.empty result.1.1.2 index true result.1.1.1, none, false)),
            { AdaptiveCtxDynamicKnownKeys.initialSource with cache := result.2.cache })) := by
    refine bind_congr_of_forall_mem_support _ fun result supported => ?_
    obtain ⟨shared', clean⟩ := related.2 (pair result) (by
      simp only [support_map, Set.mem_image]
      exact ⟨result, supported, rfl⟩)
    rw [PqxdhFirstRecordConfidentiality.insPostBit_ghost]
    change result.2 = _ at clean
    rw [clean]
    rfl
  have build : firstBuild pre application initial selector aux source writer previousRoot response64 sender index metadata ready
      before selected shared privateState cache store key nonce next =
      Prod.map id project <$> (pair <$> (simulateQ challenger (((compiledBuild pre application initial selector aux source writer
        (productionStream source.crypto) none target nonce next sender (initialKernel response64) index metadata ready).run
          (initialFront before)).run (initialShared shared privateState cache store).1)).run
          (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log))) :=
    related.1.symm
  rw [clientEq, cleaned, build, bind_map_left, bind_map_left]
  rfl

set_option linter.deprecated false in
/-- Per selected builder result: an output of the instrumented post bit that requires the finish raw flag and the undisclosed selected chain is at most the hit event of the hit-flagged source post from the builder's front and local state. -/
theorem postBit_hit (out : Option Bool × PqxdhFirstRecordConfidentiality.InsState M P I D K A N RootOracle.QueryCache S B → Bool)
    (implies : ∀ result, out result = true → result.1 = some true ∧ result.2.2.2.2 = true ∧
      RawCtxFreshChainCut.concreteChain target ∉ RawCtxSelectedMessageFreshness.known [] result.2.1.1.roles.2)
    (built : Built M P I D K A N S B) :
    𝒟[PqxdhFirstRecordConfidentiality.insPostBit pre application initial selector aux source writer selectedMessage previousRoot response64
        sender route decode post selected key nonce next b out built.1.1 (PqxdhFirstRecordConfidentiality.insStart index built)] {true} ≤
      𝒟[(fun result => @decide (result.2.2 = true ∧ ¬ Disclosed target result.2.1) (Classical.propDecidable _)) <$>
        (simulateQ (hitObserved pre application initial selector aux source writer (productionStream source.crypto) key target nonce next
          sender route decode) (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run
          (([], (built.1.2, built.2)), false)] {true} := by
  unfold PqxdhFirstRecordConfidentiality.insPostBit
  rw [PqxdhFirstRecordConfidentiality.insEvaluated_program]
  refine (PqxdhFirstRecordConfidentiality.evaluated_le_augmented pre application initial selector aux source writer
    (productionStream source.crypto) none key target nonce next sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage)
    b (post built.1.1) (PqxdhFirstRecordConfidentiality.insStart index built) (fun result => out (result.1, result.2.1))
    (fun result holds => (implies _ holds).1)).trans ?_
  exact aug_hit pre application initial selector aux source writer (productionStream source.crypto) key target nonce next sender route
    decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b _ (fun result => out (result.1, result.2.1))
    (fun result holds => ⟨(implies _ holds).2.1, (implies _ holds).2.2⟩) (PqxdhFirstRecordConfidentiality.insStart index built) []

/-- The selected builder followed by such an instrumented post bit is at most the source-only finish-hit run. -/
theorem first_hit (out : Option Bool × PqxdhFirstRecordConfidentiality.InsState M P I D K A N RootOracle.QueryCache S B → Bool)
    (implies : ∀ result, out result = true → result.1 = some true ∧ result.2.2.2.2 = true ∧
      RawCtxFreshChainCut.concreteChain target ∉ RawCtxSelectedMessageFreshness.known [] result.2.1.1.roles.2) :
    𝒟[firstBuild pre application initial selector aux source writer previousRoot response64 sender index metadata ready
      before selected shared privateState cache store key nonce next >>= fun built =>
      PqxdhFirstRecordConfidentiality.insPostBit pre application initial selector aux source writer selectedMessage previousRoot response64
        sender route decode post selected key nonce next b out built.1.1 (PqxdhFirstRecordConfidentiality.insStart index built)] {true} ≤
      𝒟[hitRun pre application selector aux source writer sender route decode index metadata ready post before shared privateState cache
        store initial previousRoot response64 selected key nonce next] {true} := by
  unfold hitRun
  exact PqxdhFirstRecordStopBound.bind_le _ _ _ fun built =>
    postBit_hit pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode index post
      selected key nonce next b out implies built

end ClientOut

section PreparedOut
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity CtxRomAuth AdaptiveCtxSharedHash
open PqxdhFirstRecordConfidentiality (InsState insSuffix insSuffixRun insFullClient readOut insFirstRun insFirstClient_run insPostBit
  insStart collGame flagOut clientOut ClientEvent)
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)) (b : Fin (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

/-- The output functions of the instrumented prepared clients. -/
abbrev OutFunction (M P I K A : Type) (setup : StatefulPhase1Setup baseSpec) (S B : Nat) :=
  RawCtxProtocolReveals.Owner S (B + 1) → PqxdhInitialRootLabelService.Response →
    Option Bool × InsState M P (PqxdhGeneratedBeaconState.IdentityHandle I) (DhPair setup) (PqxdhGeneratedBeaconState.KemHandle K) A
      (BareState 1) RootOracle.QueryCache S (B + 1) → Bool

/-- The instrumented compiled continuation of one prepared context with an arbitrary output function: completed preparations give `false`; a pending preparation runs the selected builder and the instrumented evaluated post, and reads the output from the selected owner, the initializer response and the final instrumented result. -/
noncomputable def outObserve (target : Target S (B + 1)) (out : OutFunction M P I K A setup S B)
    (context : PqxdhInitialLegalObserver.Context env0 kem attachedVerify primitives program post)
    (initialBlock : HmacBlock) (nonce : NonceOutput) (chain key : RootOutput) : ProbComp Bool :=
  match PqxdhInitialPreparedSourceInput.input env0 baseImpl kem attachedVerify primitives program post context
      target.owner target.number target.ancestors target.disclosed with
  | .inl _ => pure false
  | .inr input =>
    firstBuild
      (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        context.secretKey context.ciphertext)
      (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        context.secretKey context.ciphertext)
      (initialLocal (A := A) (N := BareState 1) (env0).source input.selectedMessage zeroRoot
        (RawCtxSelectedInitialConstructor.response64 initialBlock))
      (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A)
        (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem context.secretKey context.ciphertext))
      (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks)
      (env0).source (env0).recordWriter zeroRoot (RawCtxSelectedInitialConstructor.response64 initialBlock)
      (env0).senderId input.index input.metadata { input.ready with root := zeroRoot }
      input.before input.selected input.shared input.privateState input.cache emptyStore key nonce chain >>= fun built =>
    insPostBit
      (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        context.secretKey context.ciphertext)
      (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        context.secretKey context.ciphertext)
      (initialLocal (A := A) (N := BareState 1) (env0).source input.selectedMessage zeroRoot
        (RawCtxSelectedInitialConstructor.response64 initialBlock))
      (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A)
        (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem context.secretKey context.ciphertext))
      (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks)
      (env0).source (env0).recordWriter input.selectedMessage zeroRoot (RawCtxSelectedInitialConstructor.response64 initialBlock)
      (env0).senderId (env0).route (env0).decode input.post input.selected key nonce chain b
      (out input.selected (RawCtxSelectedInitialConstructor.response64 initialBlock)) built.1.1 (insStart input.index built)

/-- The instrumented compiled game with an arbitrary output function: the actual preparation, the initializer block, the selected nonce and next chain, then the selected key, then the instrumented compiled continuation. -/
noncomputable def outGame (target : Target S (B + 1)) (out : OutFunction M P I K A setup S B) : ProbComp Bool := do
  let context ← PqxdhCorrelatedExtractFamily.prepare baseImpl kem
    (PqxdhAuthenticatedRootExperiment.protocol env0 kem attachedVerify primitives program post)
  let initialBlock ← $ᵗ HmacBlock
  let nonce ← $ᵗ NonceOutput
  let chain ← $ᵗ RootOutput
  let key ← $ᵗ RootOutput
  outObserve setup env callbacks baseImpl kem attachedVerify primitives program post b target out context initialBlock nonce chain key

/-- Outside the initial half alias, the instrumented compiled continuation of the first Beacon record with any output function equals the key-free instrumented suffix with that output, evaluated by the selected-key challenger from the reached cache and public log (the output-generic form of `PqxdhFirstRecordConfidentiality.insObserve_eq`). -/
theorem outObserve_eq (out : OutFunction M P I K A setup S B)
    (sample : PqxdhFirstBeaconRecordCtx.Packet (M := M) (P := P) (I := I) (K := K) (A := A) (KemSK := KemSK) setup program ×
      HmacBlock × NonceOutput × RootOutput)
    (cache : CtxRO.QueryCache) (log : List Pqxdh.Bytes) (key : RootOutput)
    (aliased : ¬ RawCtxSendLineageCollision.InitialAlias sample.2.1) :
    outObserve setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b) out
        (PqxdhFirstBeaconRecordCtx.restoreSample setup env callbacks kem attachedVerify primitives program post sample cache).1
        sample.2.1 sample.2.2.1 sample.2.2.2 key =
      Prod.fst <$> (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder (env0).decode)
        (env0).source.crypto key) (insSuffix setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)
          out sample)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (cache, log)) := by
  unfold outObserve insSuffix insSuffixRun PqxdhFirstBeaconRecordCtx.restoreSample
  rw [← PqxdhSourceSharedInput.input_cache setup env callbacks program post attachedVerify primitives baseImpl kem]
  cases pending : PqxdhSourceSharedInput.input setup env callbacks program post attachedVerify primitives baseImpl kem
      (firstBeacon b).owner (firstBeacon b).number (firstBeacon b).ancestors (firstBeacon b).disclosed sample.1 with
  | inl decision => simp [PqxdhSourceSharedInput.restore, readOut]
  | inr input =>
    have owner := PqxdhFirstBeaconRecordCtx.input_selected setup env callbacks baseImpl kem attachedVerify primitives program post _ _ _
      _ sample.1 input pending
    simp only [PqxdhSourceSharedInput.restore]
    have known : ∀ kernel, initialKernel (RawCtxSelectedInitialConstructor.response64 sample.2.1) = .ok kernel → ∀ context,
        PqxdhFirstBeaconRecordCtx.KnownSend (productionStream (env0).source.crypto) none (PqxdhInitialSourceExperiment.root (env0).source
          zeroRoot (RawCtxSelectedInitialConstructor.response64 sample.2.1) (firstBeacon b).owner) sample.2.2.1 sample.2.2.2 kernel
          context :=
      fun kernel initialized context => PqxdhFirstBeaconRecordCtx.initial_known (S := S) (env0).source sample.2.1 b sample.2.2.1
        sample.2.2.2 aliased kernel initialized context
    rw [owner] at *
    rw [insRun_client_out (known := known) (log := log), insFirstClient_run, Functor.map_map]
    rfl

/-- The CTX source game of the instrumented client with any output function is dominated by the output-generic instrumented compiled game plus the initial half-alias term `2^-256`. -/
theorem client_le_out (out : OutFunction M P I K A setup S B) :
    𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
      (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b) out)] {true} ≤
    𝒟[outGame setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b) out] {true} +
      (1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) := by
  refine le_trans ?_ (add_le_add le_rfl (PqxdhFirstBeaconRecordCtx.alias_bound setup env callbacks baseImpl kem attachedVerify primitives
    program post))
  have reorder := PqxdhFirstRecordConfidentiality.prepared_reorder setup env callbacks baseImpl kem attachedVerify primitives program post
    (outObserve setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b) out)
  change outGame setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b) out = _ at reorder
  have aliasReorder := PqxdhFirstRecordConfidentiality.prepared_reorder setup env callbacks baseImpl kem attachedVerify primitives program
    post (fun _ initialBlock _ _ _ => pure (@decide (RawCtxSendLineageCollision.InitialAlias initialBlock) (Classical.propDecidable _)))
  change PqxdhFirstBeaconRecordCtx.aliasGame setup env callbacks baseImpl kem attachedVerify primitives program post = _ at aliasReorder
  rw [reorder, aliasReorder, PqxdhFirstRecordConfidentiality.insClient_source]
  refine true_bind_le _ _ _ _ fun result => true_bind_le _ _ _ _ fun key => ?_
  classical
  by_cases aliased : RawCtxSendLineageCollision.InitialAlias result.1.2.1
  · rw [show (@decide (RawCtxSendLineageCollision.InitialAlias result.1.2.1) (Classical.propDecidable _)) = true from
        @decide_eq_true _ (Classical.propDecidable _) aliased]
    refine le_add_left ?_
    simp only [evalDist_apply_singleton, probOutput_pure_self]
    exact probOutput_le_one
  · rw [outObserve_eq setup env callbacks baseImpl kem attachedVerify primitives program post b out result.1 result.2.1 result.2.2 key
      aliased]
    exact le_self_add

/-- The source-only finish-hit continuation of one prepared context: completed preparations give `false`; a pending preparation runs the source-only finish-hit run with the prepared callbacks of its own KEM secret and challenge. -/
noncomputable def hitObserve (target : Target S (B + 1))
    (context : PqxdhInitialLegalObserver.Context env0 kem attachedVerify primitives program post)
    (initialBlock : HmacBlock) (nonce : NonceOutput) (chain key : RootOutput) : ProbComp Bool :=
  match PqxdhInitialPreparedSourceInput.input env0 baseImpl kem attachedVerify primitives program post context
      target.owner target.number target.ancestors target.disclosed with
  | .inl _ => pure false
  | .inr input => hitRun
      (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        context.secretKey context.ciphertext)
      (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        context.secretKey context.ciphertext)
      (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A)
        (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem context.secretKey context.ciphertext))
      (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks)
      (env0).source (env0).recordWriter (env0).senderId (env0).route (env0).decode input.index input.metadata
      { input.ready with root := zeroRoot } input.post input.before input.shared input.privateState input.cache emptyStore
      (initialLocal (A := A) (N := BareState 1) (env0).source input.selectedMessage zeroRoot
        (RawCtxSelectedInitialConstructor.response64 initialBlock))
      zeroRoot (RawCtxSelectedInitialConstructor.response64 initialBlock) input.selected key nonce chain

/-- The source-only finish-hit game: the samples of `sourceStopGame`, then the source-only finish-hit continuation. -/
noncomputable def hitGame (target : Target S (B + 1)) : ProbComp Bool := do
  let context ← PqxdhCorrelatedExtractFamily.prepare baseImpl kem
    (PqxdhAuthenticatedRootExperiment.protocol env0 kem attachedVerify primitives program post)
  let initialBlock ← $ᵗ HmacBlock
  let nonce ← $ᵗ NonceOutput
  let chain ← $ᵗ RootOutput
  let key ← $ᵗ RootOutput
  hitObserve setup env callbacks baseImpl kem attachedVerify primitives program post target context initialBlock nonce chain key

/-- The finish-flag output requires the post result `true`, a raised finish raw flag and the undisclosed selected chain. -/
theorem flagOut_implies (owner : RawCtxProtocolReveals.Owner S (B + 1)) (response64 : PqxdhInitialRootLabelService.Response)
    (result : Option Bool × InsState M P (PqxdhGeneratedBeaconState.IdentityHandle I) (DhPair setup)
      (PqxdhGeneratedBeaconState.KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1))
    (holds : flagOut setup env callbacks (firstBeacon b) owner response64 result = true) :
    result.1 = some true ∧ result.2.2.2.2 = true ∧
      RawCtxFreshChainCut.concreteChain (PqxdhInitialSourceExperiment.root (env0).source zeroRoot response64 owner) ∉
        RawCtxSelectedMessageFreshness.known [] result.2.1.1.roles.2 := by
  simp only [flagOut, clientOut, Bool.and_eq_true, decide_eq_true_eq] at holds
  obtain ⟨⟨some, _, fresh, _⟩, raised⟩ := holds
  exact ⟨some, raised, fresh _ (List.mem_singleton_self _)⟩

/-- The finish-flag instrumented compiled game is dominated by the source-only finish-hit game. -/
theorem out_le_hit :
    𝒟[outGame setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)
      (flagOut setup env callbacks (firstBeacon b))] {true} ≤
    𝒟[hitGame setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)] {true} := by
  unfold outGame hitGame
  refine PqxdhFirstRecordStopBound.bind_le _ _ _ fun context => ?_
  refine PqxdhFirstRecordStopBound.bind_le _ _ _ fun initialBlock => ?_
  refine PqxdhFirstRecordStopBound.bind_le _ _ _ fun nonce => ?_
  refine PqxdhFirstRecordStopBound.bind_le _ _ _ fun chain => ?_
  refine PqxdhFirstRecordStopBound.bind_le _ _ _ fun key => ?_
  unfold outObserve hitObserve
  cases PqxdhInitialPreparedSourceInput.input env0 baseImpl kem attachedVerify primitives program post context
      (firstBeacon b).owner (firstBeacon b).number (firstBeacon b).ancestors (firstBeacon b).disclosed with
  | inl _ => exact le_rfl
  | inr input =>
    exact first_hit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b _
      (fun result holds => flagOut_implies setup env callbacks b _ _ result holds)

/-- The source-only finish-hit game of the first record of Beacon `b` is at most the target-free tagged stop game. -/
theorem hit_source_tagged :
    𝒟[hitGame setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)] {true} ≤
    𝒟[PqxdhFirstRecordStopTagged.taggedGame setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)]
      {true} := by
  unfold hitGame PqxdhFirstRecordStopTagged.taggedGame
  refine PqxdhFirstRecordStopBound.bind_le _ _ _ fun context => ?_
  refine PqxdhFirstRecordStopBound.bind_le _ _ _ fun initialBlock => ?_
  refine PqxdhFirstRecordStopBound.bind_le _ _ _ fun nonce => ?_
  refine PqxdhFirstRecordStopBound.bind_le _ _ _ fun chain => ?_
  refine PqxdhFirstRecordStopBound.bind_le _ _ _ fun key => ?_
  unfold hitObserve PqxdhFirstRecordStopTagged.taggedLog
  cases prepared : PqxdhInitialPreparedSourceInput.input env0 baseImpl kem attachedVerify primitives program post context
      (firstBeacon b).owner (firstBeacon b).number (firstBeacon b).ancestors (firstBeacon b).disclosed with
  | inl _ => simp
  | inr input =>
    obtain ⟨selected, _⟩ := PqxdhFirstRecordStopTagged.input_selected setup env callbacks baseImpl kem attachedVerify primitives program
      post context _ _ _ _ input prepared
    simp only
    rw [selected, decide_mass]
    have split := RawCtxSelectedInitialConstructor.split_reconstruct initialBlock
    generalize first32 initialBlock = other at split ⊢
    generalize RawCtxSelectedInitialSampler.initialOther initialBlock = value at split ⊢
    subst split
    exact hit_tagged _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ other value key nonce chain b

end PreparedOut

section CollBound
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity
open PqxdhPhase2SourceSchedulerBounds (Kind)
open PqxdhFirstRecordConfidentiality (collGame flagOut)
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)) (b : Fin (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅

/-- The finish-collision game `collGame` of the first record of Beacon `b` is at most `(2 + qSend + 51 (qRaw + qFinish)) / 2^256`, for every post whose every continuation is bounded by the query budget (`qSend` sends, `qRaw` raw receives and `qFinish` attempted finishes): `2^-256` for the initial half alias, plus the target-free tagged bound `(1 + qSend + 51 (qRaw + qFinish)) / 2^256` of `PqxdhFirstRecordStopTagged.tagged_game_bound`. -/
theorem coll_bound (budget : Kind → Nat)
    (bounded : ∀ choice response, PqxdhPhase2SourceSchedulerBounds.Bounded (post choice response) budget) :
    𝒟[collGame setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)] {true} ≤
      ((2 + budget (.inl .send) + 51 * (budget (.inl .raw) + budget (.inr 5)) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold collGame
  refine (client_le_out setup env callbacks baseImpl kem attachedVerify primitives program post b
    (flagOut setup env callbacks (firstBeacon b))).trans ?_
  refine (add_le_add ((out_le_hit setup env callbacks baseImpl kem attachedVerify primitives program post b).trans
    ((hit_source_tagged setup env callbacks baseImpl kem attachedVerify primitives program post b).trans
      (PqxdhFirstRecordStopTagged.tagged_game_bound setup env callbacks baseImpl kem attachedVerify primitives program post budget
        bounded (firstBeacon b)))) le_rfl).trans (le_of_eq ?_)
  rw [PqxdhFirstRecordStopTagged.potential_bound, ENNReal.div_add_div_same]
  congr 1
  push_cast
  ring

/-- The real value of the finish-collision bound with a certificate's post budget. -/
theorem coll_real (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) :
    (𝒟[collGame setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)] {true}).toReal ≤
      ((2 + c.postBudget (.inl .send) + 51 * (c.postBudget (.inl .raw) + c.postBudget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256 := by
  have bound := coll_bound setup env callbacks baseImpl kem attachedVerify primitives program post b c.postBudget c.postBound
  have real := ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)) bound
  rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast] at real
  simpa using real

end CollBound

section Headline
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCtx CtxRomAuth AdaptiveCtxSharedHash
open RawCtxSelectedAuthenticationObserver AdaptiveCtxDynamicKnownBounds AdaptiveCtxQueryBounds AdaptiveCtxReceive
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
open PqxdhFirstRecordConfidentiality (AdvSpec confPost confGame twinLoss keyGame collGame first_record_confidentiality
  first_record_confidentiality_budget confCertificate AdvBounded)
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅

/-- First-record left-or-right confidentiality (S7) with the finish-collision term bounded: `PqxdhFirstRecordConfidentiality.first_record_confidentiality` with each `collGame` term replaced by `(2 + qSend + 51 (qRaw + qFinish)) / 2^256` for the certificate's post budget of the corresponding wrapper post (`coll_real`). The remaining explicit game is `keyGame`; the premises are exactly those of `first_record_confidentiality`. -/
theorem first_record_confidentiality_coll (b : Fin (B + 1))
    (adversary : program.Selection → RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (c0 : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program (confPost adversary b false))
    (c1 : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program (confPost adversary b true))
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem (env0).native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect (env0).source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (ctxFallback : ModifiedNonceAeadForgery) (qPrelude0 qPrelude1 : Nat)
    (prepareHash0 : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false)
      qPrelude0)
    (prepareHash1 : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true)
      qPrelude1)
    (small0 : 1 + postTotal setup env callbacks baseImpl kem program c0 < 2 ^ 96)
    (small1 : 1 + postTotal setup env callbacks baseImpl kem program c1 < 2 ^ 96) :
    |(𝒟[confGame setup env callbacks baseImpl kem attachedVerify primitives program b adversary false] {true}).toReal -
      (𝒟[confGame setup env callbacks baseImpl kem attachedVerify primitives program b adversary true] {true}).toReal| ≤
    (twinLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b c0 ctxFallback
      qPrelude0).toReal +
    (twinLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b c1 ctxFallback
      qPrelude1).toReal +
    (PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (confPost adversary b false)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (confPost adversary b false) c0) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (confPost adversary b false) hmac fallback
      ordinaryFallback) +
    (PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (confPost adversary b true)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (confPost adversary b true) c1) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (confPost adversary b true) hmac fallback
      ordinaryFallback) +
    ((2 + c0.postBudget (.inl .send) + 51 * (c0.postBudget (.inl .raw) + c0.postBudget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256 +
    ((2 + c1.postBudget (.inl .send) + 51 * (c1.postBudget (.inl .raw) + c1.postBudget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256 +
    (𝒟[keyGame setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) (firstBeacon b)]
      {true}).toReal +
    (𝒟[keyGame setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) (firstBeacon b)]
      {true}).toReal +
    ((1 + c0.postBudget (.inl .send) + 51 * (c0.postBudget (.inl .raw) + c0.postBudget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256 +
    ((1 + c1.postBudget (.inl .send) + 51 * (c1.postBudget (.inl .raw) + c1.postBudget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256 +
    2 / 2 ^ 256 := by
  have bound := first_record_confidentiality setup env callbacks baseImpl kem attachedVerify primitives program b adversary c0 c1
    compatible adapter functional hmac correct fallback ordinaryFallback ctxFallback qPrelude0 qPrelude1 prepareHash0 prepareHash1
    small0 small1
  have coll0 := coll_real setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b c0
  have coll1 := coll_real setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b c1
  linarith

/-- First-record left-or-right confidentiality with the adversary's own budget and the finish-collision term bounded: `PqxdhFirstRecordConfidentiality.first_record_confidentiality_budget` with both `collGame` terms replaced by `(2 + budget send + 51 * (budget raw + budget finish)) / 2^256` (`coll_real` for `confCertificate`). The remaining explicit game is `keyGame`; the premises are exactly those of `first_record_confidentiality_budget`. -/
theorem first_record_confidentiality_budget_coll (b : Fin (B + 1))
    (adversary : program.Selection → RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    {post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)}
    (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post0)
    (budget : PqxdhPhase2SourceSchedulerBounds.Budget) (bounded : AdvBounded program b adversary budget)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem (env0).native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect (env0).source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (ctxFallback : ModifiedNonceAeadForgery) (qPrelude0 qPrelude1 : Nat)
    (prepareHash0 : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false)
      qPrelude0)
    (prepareHash1 : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true)
      qPrelude1)
    (small : 1 + ∑ kind, budget kind < 2 ^ 96) :
    |(𝒟[confGame setup env callbacks baseImpl kem attachedVerify primitives program b adversary false] {true}).toReal -
      (𝒟[confGame setup env callbacks baseImpl kem attachedVerify primitives program b adversary true] {true}).toReal| ≤
    (twinLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b
      (confCertificate env0 baseImpl kem program c b adversary budget bounded false) ctxFallback qPrelude0).toReal +
    (twinLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b
      (confCertificate env0 baseImpl kem program c b adversary budget bounded true) ctxFallback qPrelude1).toReal +
    (PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (confPost adversary b false)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (confPost adversary b false)
        (confCertificate env0 baseImpl kem program c b adversary budget bounded false)) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (confPost adversary b false) hmac fallback
      ordinaryFallback) +
    (PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (confPost adversary b true)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (confPost adversary b true)
        (confCertificate env0 baseImpl kem program c b adversary budget bounded true)) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (confPost adversary b true) hmac fallback
      ordinaryFallback) +
    2 * (((2 + budget (.inl .send) + 51 * (budget (.inl .raw) + budget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256) +
    (𝒟[keyGame setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) (firstBeacon b)]
      {true}).toReal +
    (𝒟[keyGame setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) (firstBeacon b)]
      {true}).toReal +
    2 * (((1 + budget (.inl .send) + 51 * (budget (.inl .raw) + budget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256) +
    2 / 2 ^ 256 := by
  have bound := first_record_confidentiality_budget setup env callbacks baseImpl kem attachedVerify primitives program b adversary c
    budget bounded compatible adapter functional hmac correct fallback ordinaryFallback ctxFallback qPrelude0 qPrelude1 prepareHash0
    prepareHash1 small
  have coll0 := coll_real setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b
    (confCertificate env0 baseImpl kem program c b adversary budget bounded false)
  have coll1 := coll_real setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b
    (confCertificate env0 baseImpl kem program c b adversary budget bounded true)
  simp only [confCertificate] at coll0 coll1
  linarith

end Headline

end BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.begin_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.begin_request

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.resume_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.resume_request

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.rank_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.rank_map

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.terminal_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.terminal_known

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.terminal_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.terminal_hit

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.reveal_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.reveal_known

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.concrete_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.concrete_known

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.interp_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.interp_path

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.tagged_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.tagged_path

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.stage_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.stage_hit

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.raw_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.raw_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.lower_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.lower_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.ownerMarkedHit_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.ownerMarkedHit_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.ownerMarkedHit_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.ownerMarkedHit_hit

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.new_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.new_receive

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.hidden_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.hidden_clean

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.known_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.known_clean

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.initial_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.initial_clean

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.owner_hit_coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.owner_hit_coupled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.ownerHit_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.ownerHit_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.hit_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.hit_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.hit_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.hit_support

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.finish_hit_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.finish_hit_step

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.hit_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.hit_keep

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.keep_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.keep_step

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.hit_coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.hit_coupled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.hit_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.hit_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.markRaw_quiet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.markRaw_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.markRaw_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.markRaw_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.markRaw_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.markRaw_map

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.markRaw_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.markRaw_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.lower_external' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.lower_external

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.lower_prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.lower_prepare

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.hit_dominates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.hit_dominates

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.relTriple_self_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.relTriple_self_map

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.aug_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.aug_flag

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.aug_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.aug_keep

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.aug_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.aug_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.aug_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.aug_run

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.aug_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.aug_hit

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.hit_tagged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.hit_tagged

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.insRun_client_out' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.insRun_client_out

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.postBit_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.postBit_hit

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.first_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.first_hit

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.outObserve_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.outObserve_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.client_le_out' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.client_le_out

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.flagOut_implies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.flagOut_implies

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.out_le_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.out_le_hit

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.hit_source_tagged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.hit_source_tagged

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.coll_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.coll_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.coll_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.coll_real

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.first_record_confidentiality_coll' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.first_record_confidentiality_coll

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.first_record_confidentiality_budget_coll' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound.first_record_confidentiality_budget_coll
