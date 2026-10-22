import BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity
import BeaconcryptCore.Computational.RawCtxSelectedSendAddress
import BeaconcryptCore.Computational.RawCtxSendLineageCollision
import BeaconcryptCore.Computational.RawCtxPrefixKeyOrder
import BeaconcryptCore.Computational.PqxdhSourceSharedInput
import BeaconcryptCore.Computational.PqxdhSourceSharedPreparationResources
import BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver

/-!
First Beacon record integrity for the protocol-derived key of Beacon `b`'s first record (selected owner `.beacon b`, record number one, no ancestors, no disclosures) in the HB-112 experiment, with the compiled game `compiledGame` of `PqxdhFirstBeaconRecordIntegrity` replaced by CTX terms.

Construction. `compiledBuild` is a key-free first Server builder: the Ready builder of `PqxdhInitialGenericBuilder` with the compiled selected send of `RawCtxSelectedSendCompiler` and the source-local registration callbacks forwarded to the shared ROM. `firstClient` runs it and then the executable post client of `PqxdhSelectedPostCompiler`. `prelude` is the complete shared-ROM preparation of `PqxdhSourceSharedPreparation` followed by the 64-byte initializer response, the selected nonce and the next chain, all drawn through the shared ROM. `fullClient` forwards the prelude to the ordinary selected-key challenger and continues with `firstClient` for pending preparations; it contains no selected key.

Results. `build_rel` shows that, evaluated by the challenger, the compiled builder projects exactly to the selected-material builder of `PqxdhSelectedFirstRecord` whenever the builder's first send derives a known slot, and that it then changes only the challenger's shared cache and selected public-hash log; `initial_known` shows that this holds unless the two 32-byte halves of the uniform initializer response are equal. `source_ghost` shows that the challenger never reads its selected public-hash log. Together they give `run_client`: C4's compiled run equals the challenger's evaluation of `firstClient`. `separated_le_client` samples the selected key first by an exchange of independent samples (`RawCtxPrefixKeyOrder.source_game`), so C4's compiled game with the alias runs removed is dominated by one ordinary CTX source experiment of `fullClient`; `compiled_le_separated` charges the alias runs with `2^-256` (`RawCtxSendLineageCollision.initial_alias_uniform`). `client_le_decision` splits the client's `true` mass into the win of `RawCtxSelectedAuthenticationObserver` and the explicit gap game `gapGame`, and `RawCtxSelectedAuthenticationObserver.authentication_bound` bounds the win by `ctxLoss`: the IND$ advantage of the constructed validation reduction, `qHash/2^128`, twice the INT-CTXT advantages of the constructed attempt-indexed reductions and `qRaw/2^512`. The raw-opening and seal budgets are derived from the certificate's post budget (one builder request plus one per post request); the hash budget adds the hash budget of the shared-ROM preparation.

Final theorem. `first_beacon_record_integrity` has the same left side as C4's `first_beacon_forgery_le` and bounds it by `targetLoss + completedLoss + ctxLoss + 2^-256 + gap + stopMass`. The premises are C4's premises, the CTX fallback forgery, the resource contract `PrepareHashBudget` (a public-hash query count of the existing shared-ROM preparation; `prepare_hash_budget` discharges it from the caps taken by `PqxdhSourceSharedPreparationResources.prepare`, which are not yet derived from the certificate) and the numeric side condition `1 + qPost < 2^96`. No codec or other functional premise is introduced.

Limits. Two terms of the final bound are still explicit games, neither a reduction advantage nor a statistical term, so the theorem is an intermediate reduction and not yet an assumption-level bound. The gap game (the constructed client returns `true`, i.e. the post client did not stop and `Forged` holds, while the ordinary observer does not win) is not yet shown to be zero or negligible; that needs an invariant over the whole compiled post relating the transcript to the observer (the Server peer keeps its first-message slot hidden until it is consumed, every selected seal before an accepted receive is returned by its send with the writer's bytes decoding to the sealed frame, and an equal authentication tuple forces an equal decoded frame), and, because a seal whose writer fails is recorded by the challenger but never reaches the transcript, either a writer-totality contract on sealed frames or a further charged term. C4's restricted stop game `stopMass` is left explicit. The replay link between the Server receive service and the extracted driver is not treated here.
-/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx

section Relation
open PqxdhSelectedStateInterpreter
variable {Local : Type}

/-- The CTX state `after` differs from `before` only in the shared cache and the selected public-hash log. -/
def Clean (before after : AdaptiveCtxDynamicKnownKeys.SourceState) : Prop :=
  ∃ shared, after = RawCtxSourceSharedRom.install before shared

/-- Every state is clean relative to itself. -/
theorem clean_refl (state : AdaptiveCtxDynamicKnownKeys.SourceState) : Clean state state :=
  ⟨(state.cache, state.selected.1.publicInputs), rfl⟩

/-- Cleanliness composes. -/
theorem clean_trans {first second third : AdaptiveCtxDynamicKnownKeys.SourceState}
    (left : Clean first second) (right : Clean second third) : Clean first third := by
  obtain ⟨shared, rfl⟩ := left
  obtain ⟨shared', rfl⟩ := right
  exact ⟨shared', rfl⟩

/-- Projection of a full local and CTX state to the source local state with the CTX cache. -/
def project (state : Local × AdaptiveCtxDynamicKnownKeys.SourceState) : RawCtxSharedPrimitive.SharedState Local :=
  (state.1, state.2.cache)

/-- A compiled local program `x` simulates a source program `y`: evaluating `x` and projecting gives `y` on the projected state, and every reached CTX state is clean. -/
def Rel (impl : QueryImpl AdaptiveCtxDynamicKnownKeys.Spec (StateT AdaptiveCtxDynamicKnownKeys.SourceState ProbComp))
    {X : Type} (x : StateT Local (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) X)
    (y : StateT (RawCtxSharedPrimitive.SharedState Local) ProbComp X) : Prop :=
  ∀ state : Local × AdaptiveCtxDynamicKnownKeys.SourceState,
    Prod.map id project <$> (evaluate impl x).run state = y.run (project state) ∧
    ∀ result ∈ support ((evaluate impl x).run state), Clean state.2 result.2.2

variable (impl : QueryImpl AdaptiveCtxDynamicKnownKeys.Spec (StateT AdaptiveCtxDynamicKnownKeys.SourceState ProbComp))

/-- Pure programs are related. -/
theorem rel_pure {X : Type} (value : X) :
    Rel impl (pure value : StateT Local (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) X) (pure value) := by
  intro state
  rw [pure_evaluate]
  refine ⟨by simp [project], fun result supported => ?_⟩
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  subst supported
  exact clean_refl _

/-- Relation is preserved by bind. -/
theorem rel_bind {X Y : Type} {x : StateT Local (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) X}
    {y : StateT (RawCtxSharedPrimitive.SharedState Local) ProbComp X}
    {f : X → StateT Local (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) Y}
    {g : X → StateT (RawCtxSharedPrimitive.SharedState Local) ProbComp Y}
    (first : Rel impl x y) (rest : ∀ value, Rel impl (f value) (g value)) :
    Rel impl (x >>= f) (y >>= g) := by
  intro state
  rw [bind_evaluate]
  constructor
  · rw [StateT.run_bind, StateT.run_bind, ← (first state).1, map_bind, bind_map_left]
    exact bind_congr fun result => (rest result.1 result.2).1
  · intro result supported
    rw [StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, reached, final⟩ := supported
    exact clean_trans ((first state).2 middle reached) ((rest middle.1 middle.2).2 result final)

/-- Relation is preserved by mapping. -/
theorem rel_map {X Y : Type} (h : X → Y) {x : StateT Local (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) X}
    {y : StateT (RawCtxSharedPrimitive.SharedState Local) ProbComp X} (related : Rel impl x y) :
    Rel impl (h <$> x) (h <$> y) := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  exact rel_bind impl related fun value => rel_pure impl (h value)

/-- Relation is preserved by a Rust result continuation. -/
theorem rel_continue {V X : Type} (result : RustM V)
    {f : V → StateT Local (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) (RustM X)}
    {g : V → StateT (RawCtxSharedPrimitive.SharedState Local) ProbComp (RustM X)}
    (related : ∀ value, result = .ok value → Rel impl (f value) (g value)) :
    Rel impl (PqxdhInitialGenericBuilder.continueRust result f) (PqxdhInitialGenericBuilder.continueRust result g) := by
  cases result with
  | ok value => exact related value rfl
  | fail error => exact rel_pure impl _
  | div => exact rel_pure impl _

/-- Relation is preserved by a conditional with the same condition. -/
theorem rel_ite {X : Type} (condition : Prop) [Decidable condition]
    {x₁ x₂ : StateT Local (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) X}
    {y₁ y₂ : StateT (RawCtxSharedPrimitive.SharedState Local) ProbComp X}
    (positive : condition → Rel impl x₁ y₁) (negative : ¬condition → Rel impl x₂ y₂) :
    Rel impl (if condition then x₁ else x₂) (if condition then y₁ else y₂) := by
  split_ifs with holds
  · exact positive holds
  · exact negative holds

end Relation

section Builder
open PqxdhNativeSharedPrefix PqxdhSelectedStateInterpreter PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
variable {ι I D K X Response Shared A N C : Type} {extra : OracleSpec ι}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder)

local notation "challenger" => AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key

/-- The key-free registration callbacks of the compiled Server builder: the source-local callbacks with forwarded coins. -/
noncomputable def compiledAux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec
    (StateT (Local A N C) (OracleComp AdaptiveCtxDynamicKnownKeys.Spec)) :=
  fun request => PqxdhSelectedCallbackCompiler.lower (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response)
    (Shared := Shared) pre application initial selector aux (.inl (.inr (.inr (.inr (.inr request)))))

/-- The key-free send and receive calls of the compiled Server builder. The send is the compiled selected send; an outer selected-nonce stop keeps the kernel and returns no ciphertext, and `send_rel` shows that no such stop occurs when the send derives a known slot. The builder makes no receive. -/
noncomputable def compiledCalls : RawCtxChainOwner.Calls RawCtxSelectedMessageReveals.Kernel
    (StateT (Local A N C) (OracleComp AdaptiveCtxDynamicKnownKeys.Spec)) where
  receive kernel _ _ := pure (kernel, .None)
  send kernel context := fun state => (fun result => (result.getD (kernel, none), state)) <$>
    RawCtxSelectedSendCompiler.send source writer prior parent target nonce next kernel context

/-- The compiled registration callbacks simulate the source-local callbacks with only forwarded shared-ROM effects. -/
theorem aux_rel (request : PqxdhServerRegistrationPublication.AuxSpec.Domain) :
    Rel challenger (compiledAux (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response)
        (Shared := Shared) pre application initial selector aux request)
      (PqxdhSelectedFirstRecord.serverAux (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response)
        (Shared := Shared) pre application initial selector aux request) := by
  intro state
  constructor
  · exact PqxdhSelectedInitialOwnerCompiler.external_project pre application initial selector aux source key read
      (.inr (.inr (.inr (.inr request)))) state
  · intro result supported
    have forwarded := RawCtxSourceSharedRom.forward_complete true (RawCtxUniversalDecoder.decoder read) source.crypto key
      ((PqxdhSelectedCallbackCompiler.callback (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response)
        (Shared := Shared) pre application initial selector aux (.inr (.inr (.inr (.inr request))))).run state.1) state.2
    simp only [StateT.run] at forwarded
    simp only [compiledAux, PqxdhSelectedCallbackCompiler.lower, evaluate, StateT.run] at supported
    rw [forwarded] at supported
    simp only [Functor.map_map, support_map, Set.mem_image] at supported
    obtain ⟨middle, _, rfl⟩ := supported
    exact ⟨_, rfl⟩

/-- A send whose derived slot is not the selected hidden slot changes only the CTX cache and selected public log. -/
theorem send_clean (kernel : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (known : ∀ pending chosen, RawCtxInterpretedSend.normalBegin kernel context = .requested pending →
      (RawCtxInterpretedSend.ready pending
        (RawCtxSelectedSendCompiler.deriveValue prior parent target nonce next pending.request)).material ≠ .hidden chosen)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) (result : Option (RawCtxSelectedMessageReveals.Kernel ×
      Option RawCtxSourceSend.Encrypted) × AdaptiveCtxDynamicKnownKeys.SourceState)
    (supported : result ∈ support ((simulateQ challenger
      (RawCtxSelectedSendCompiler.send source writer prior parent target nonce next kernel context)).run state)) :
    Clean state result.2 := by
  rw [RawCtxSelectedSendCompiler.send_cases] at supported
  cases started : RawCtxInterpretedSend.normalBegin kernel context with
  | exhausted entry actual =>
    simp only [started, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact clean_refl _
  | requested pending =>
    simp only [started] at supported
    cases material : (RawCtxInterpretedSend.ready pending
        (RawCtxSelectedSendCompiler.deriveValue prior parent target nonce next pending.request)).material with
    | hidden chosen => exact False.elim (known pending chosen started material)
    | known value =>
      have arguments : RawCtxInterpretedArguments.sealArguments (RawCtxInterpretedSend.ready pending
          (RawCtxSelectedSendCompiler.deriveValue prior parent target nonce next pending.request)) =
          ⟨.known value, (RawCtxInterpretedSend.ready pending
            (RawCtxSelectedSendCompiler.deriveValue prior parent target nonce next pending.request)).sequence,
            (RawCtxInterpretedSend.ready pending
            (RawCtxSelectedSendCompiler.deriveValue prior parent target nonce next pending.request)).context⟩ := by
        simp only [RawCtxInterpretedArguments.sealArguments, material]
      simp only [RawCtxSelectedSealConsumer.sealing, arguments, simulateQ_map, StateT.run_map,
        RawCtxSelectedSealConsumer.known_call, Functor.map_map, support_map, Set.mem_image] at supported
      obtain ⟨middle, _, rfl⟩ := supported
      exact ⟨_, rfl⟩

/-- A compiled send whose derived slot is known simulates the selected-material source send. -/
theorem send_rel (kernel : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (known : ∀ pending chosen, RawCtxInterpretedSend.normalBegin kernel context = .requested pending →
      (RawCtxInterpretedSend.ready pending
        (RawCtxSelectedSendCompiler.deriveValue prior parent target nonce next pending.request)).material ≠ .hidden chosen) :
    Rel challenger ((compiledCalls (A := A) (N := N) (C := C) source writer prior parent target nonce next).send kernel context)
      ((PqxdhSelectedMessageBeacon.materialCalls (A := Local A N C) source writer prior parent key target nonce next).send kernel context) := by
  intro state
  have noStop : ¬ RawCtxSelectedSendCompiler.Stops prior parent target nonce next kernel context state.2 := by
    unfold RawCtxSelectedSendCompiler.Stops
    cases started : RawCtxInterpretedSend.normalBegin kernel context with
    | exhausted entry actual => simp only [not_false_eq_true]
    | requested pending =>
      rintro ⟨value, material, _, _⟩
      exact known pending value started material
  have main := RawCtxSelectedSendCompiler.send_source source writer prior parent key target nonce next read kernel context state
  rw [ite_eq_right_of_eq_false _ _ (eq_false noStop)] at main
  constructor
  · change Prod.map id project <$> (pair <$> (simulateQ challenger ((fun result => (result.getD (kernel, none), state.1)) <$>
      RawCtxSelectedSendCompiler.send source writer prior parent target nonce next kernel context)).run state.2) = _
    have unfolded : Prod.map id project <$> (pair <$> (simulateQ challenger ((fun result => (result.getD (kernel, none), state.1)) <$>
        RawCtxSelectedSendCompiler.send source writer prior parent target nonce next kernel context)).run state.2) =
        (fun result => (result.1.getD (kernel, none), result.2)) <$>
          (Prod.map id RawCtxSelectedReceiveCompiler.project <$> (RawCtxSelectedReceiveCompiler.evaluated source key read
            (RawCtxSelectedSendCompiler.send source writer prior parent target nonce next kernel context)).run state) := by
      simp only [simulateQ_map, StateT.run_map, Functor.map_map]
      rw [show (RawCtxSelectedReceiveCompiler.evaluated source key read
          (RawCtxSelectedSendCompiler.send source writer prior parent target nonce next kernel context)).run state =
          (fun result => (result.1, (state.1, result.2))) <$> (simulateQ challenger
            (RawCtxSelectedSendCompiler.send source writer prior parent target nonce next kernel context)).run state.2 from rfl,
        Functor.map_map]
      rfl
    rw [unfolded, main, Functor.map_map]
    simp only [Option.getD_some, Prod.mk.eta, id_map']
    rfl
  · intro result supported
    change result ∈ support (pair <$> (simulateQ challenger ((fun result => (result.getD (kernel, none), state.1)) <$>
      RawCtxSelectedSendCompiler.send source writer prior parent target nonce next kernel context)).run state.2) at supported
    simp only [simulateQ_map, StateT.run_map, Functor.map_map, support_map, Set.mem_image] at supported
    obtain ⟨middle, reached, rfl⟩ := supported
    exact send_clean source writer prior parent key target nonce next read kernel context known state.2 middle reached

/-- The first derived send slot of `kernel` for `context` is not the selected hidden slot. -/
def KnownSend (kernel : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext) : Prop :=
  ∀ pending chosen, RawCtxInterpretedSend.normalBegin kernel context = .requested pending →
    (RawCtxInterpretedSend.ready pending
      (RawCtxSelectedSendCompiler.deriveValue prior parent target nonce next pending.request)).material ≠ .hidden chosen

open PqxdhInitialGenericPublication in
/-- The compiled registration first send and publication simulate the selected-material source ones when the send slot is known. -/
theorem after_rel {Metadata PeerMetadata Consumed : Type} (candidate : pqxdh.ServerRegistrationCandidate)
    (authenticated : Pqxdh.Bytes) (kernel : RawCtxSelectedMessageReveals.Kernel) (metadata : PeerMetadata)
    (state : State RawCtxSelectedMessageReveals.Kernel Metadata PeerMetadata Consumed)
    (known : KnownSend prior parent target nonce next kernel
      (PqxdhServerRegistrationPublication.firstContext candidate authenticated)) :
    Rel challenger
      (afterInitialization (compiledCalls (A := A) (N := N) (C := C) source writer prior parent target nonce next)
        (compiledAux (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared)
          pre application initial selector aux) candidate authenticated kernel metadata state)
      (afterInitialization (PqxdhSelectedMessageBeacon.materialCalls (A := Local A N C) source writer prior parent key target nonce next)
        (PqxdhSelectedFirstRecord.serverAux (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response)
          (Shared := Shared) pre application initial selector aux) candidate authenticated kernel metadata state) := by
  unfold afterInitialization
  refine rel_bind _ (send_rel source writer prior parent key target nonce next read kernel _ known) fun sent => ?_
  rcases sent with ⟨advanced, encrypted⟩
  refine rel_bind _ (aux_rel pre application initial selector aux source key read _) fun _ => ?_
  cases encrypted with
  | none => exact rel_pure _ _
  | some encrypted =>
    refine rel_bind _ (aux_rel pre application initial selector aux source key read _) fun serialized => ?_
    cases serialized with
    | none => exact rel_pure _ _
    | some serialized => exact rel_pure _ _

open PqxdhInitialGenericBuilder in
/-- The compiled registration candidate simulates the selected-material source candidate when every first send of the initial kernel is known. -/
theorem candidate_rel {Metadata PeerMetadata Consumed : Type} (initialKernel : RustM RawCtxSelectedMessageReveals.Kernel)
    (pending : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State RawCtxSelectedMessageReveals.Kernel Metadata PeerMetadata Consumed)
    (known : ∀ kernel, initialKernel = .ok kernel → ∀ context, KnownSend prior parent target nonce next kernel context) :
    Rel challenger
      (candidate (compiledCalls (A := A) (N := N) (C := C) source writer prior parent target nonce next)
        (compiledAux (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared)
          pre application initial selector aux) initialKernel pending data metadata state)
      (candidate (PqxdhSelectedMessageBeacon.materialCalls (A := Local A N C) source writer prior parent key target nonce next)
        (PqxdhSelectedFirstRecord.serverAux (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response)
          (Shared := Shared) pre application initial selector aux) initialKernel pending data metadata state) := by
  unfold candidate
  refine rel_bind _ (aux_rel pre application initial selector aux source key read _) fun valid => ?_
  refine rel_ite _ _ (fun _ => rel_pure _ _) fun _ => ?_
  refine rel_bind _ (aux_rel pre application initial selector aux source key read _) fun reserved => ?_
  refine rel_ite _ _ (fun _ => rel_pure _ _) fun _ => ?_
  refine rel_continue _ _ fun kernel initialized => ?_
  refine rel_ite _ _ (fun _ => rel_pure _ _) fun _ => ?_
  refine rel_ite _ _ (fun _ => ?_) fun _ => rel_pure _ _
  refine rel_bind _ (aux_rel pre application initial selector aux source key read _) fun allocated => ?_
  refine rel_ite _ _ (fun _ => rel_pure _ _) fun _ => ?_
  refine rel_continue _ _ fun binding _ => ?_
  exact rel_map _ _ (after_rel pre application initial selector aux source writer prior parent key target nonce next read
    pending _ kernel metadata state (known kernel initialized _))

open PqxdhInitialGenericBuilder in
/-- The compiled Ready builder simulates the selected-material source Ready builder when every first send of the initial kernel is known. -/
theorem ready_rel {Metadata PeerMetadata Consumed : Type} (initialKernel : RustM RawCtxSelectedMessageReveals.Kernel)
    (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State RawCtxSelectedMessageReveals.Kernel Metadata PeerMetadata Consumed)
    (known : ∀ kernel, initialKernel = .ok kernel → ∀ context, KnownSend prior parent target nonce next kernel context) :
    Rel challenger
      (readyBuild source (compiledCalls (A := A) (N := N) (C := C) source writer prior parent target nonce next)
        (compiledAux (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared)
          pre application initial selector aux) initialKernel binding ready metadata state)
      (readyBuild source (PqxdhSelectedMessageBeacon.materialCalls (A := Local A N C) source writer prior parent key target nonce next)
        (PqxdhSelectedFirstRecord.serverAux (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response)
          (Shared := Shared) pre application initial selector aux) initialKernel binding ready metadata state) := by
  unfold readyBuild usedBuild
  refine rel_continue _ _ fun following _ => ?_
  cases following with
  | Err error => exact rel_pure _ _
  | Ok following =>
    refine rel_continue _ _ fun prepared _ => ?_
    cases prepared with
    | Err error => exact rel_pure _ _
    | Ok value =>
      exact candidate_rel pre application initial selector aux source writer prior parent key target nonce next read
        initialKernel value _ metadata state known

variable {M P : Type} {S B : Nat} (sender : M → Std.U64)

/-- The key-free compiled first Server builder: the same consumed input, allocation and application gates, first seal and publication as the selected-material builder, with the compiled send and the source-local callbacks. -/
noncomputable def compiledBuild (initialKernel : RustM RawCtxSelectedMessageReveals.Kernel) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) :
    StateT (PqxdhSelectedPostCompiler.Front M P I D K S B) (StateT (Local A N C) (OracleComp AdaptiveCtxDynamicKnownKeys.Spec))
      (RustM (Option PqxdhServerRegistrationPublication.Response)) := fun before =>
  let current := PqxdhSelectedFirstRecord.consumeFront index ready before
  let input := PqxdhSelectedFirstRecord.selectedServer sender index current
  PqxdhSelectedFirstRecord.reinstallServer index current <$> PqxdhInitialGenericBuilder.readyBuild source
    (compiledCalls source writer prior parent target nonce next)
    (compiledAux (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared)
      pre application initial selector aux) initialKernel
    ⟨input.server.identity, input.identityKeyId⟩ ready metadata input

/-- The compiled first Server builder simulates the selected-material builder of `PqxdhSelectedFirstRecord` when every first send of the initial kernel is known: the projected output and source state agree, and the CTX state changes only in its cache and selected public log. -/
theorem build_rel (initialKernel : RustM RawCtxSelectedMessageReveals.Kernel) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (before : PqxdhSelectedPostCompiler.Front M P I D K S B)
    (known : ∀ kernel, initialKernel = .ok kernel → ∀ context, KnownSend prior parent target nonce next kernel context) :
    Rel challenger ((compiledBuild pre application initial selector aux source writer prior parent target nonce next sender
        initialKernel index metadata ready).run before)
      ((PqxdhSelectedFirstRecord.selectedBuild pre application initial selector aux source writer prior parent key target nonce next
        sender initialKernel index metadata ready).run before) :=
  rel_map _ _ (ready_rel pre application initial selector aux source writer prior parent key target nonce next read
    initialKernel _ ready metadata _ known)

end Builder

section Alias
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf RawCtxSelectedParentTable

/-- Outside the initial half alias of the 64-byte initializer response, every first send of the all-known Server kernel derives a known slot for the Beacon selected root: the Server sends on the first half, the selected Beacon root is the second half. -/
theorem initial_known {S B : Nat} (source : FixedHkdfSha512NoSaltSource) (block : HmacBlock) (b : Fin B)
    (nonce : NonceOutput) (next : RootOutput) (separate : ¬RawCtxSendLineageCollision.InitialAlias block)
    (kernel : RawCtxSelectedMessageReveals.Kernel)
    (initialized : PqxdhSelectedFirstRecord.initialKernel (RawCtxSelectedInitialConstructor.response64 block) = .ok kernel)
    (context : RawCtxSourceSend.SealContext) :
    KnownSend (productionStream source.crypto) none
      (PqxdhInitialSourceExperiment.root source (List.Vector.replicate 32 0) (RawCtxSelectedInitialConstructor.response64 block)
        (.beacon b : RawCtxProtocolReveals.Owner S B)) nonce next kernel context := by
  intro pending chosen admitted hidden
  unfold PqxdhSelectedFirstRecord.initialKernel at initialized
  cases created : PqxdhInitialReplyErasure.kernelOf false (RawCtxSelectedInitialConstructor.response64 block) with
  | fail error => simp [created] at initialized; cases initialized
  | div => simp [created] at initialized; cases initialized
  | ok server =>
    rw [created] at initialized
    have kernelEq : kernel = PqxdhSelectedMessageBeacon.knownKernel server.refined := (RustM.ok.inj initialized).symm
    have chain := RawCtxSelectedSendAddress.selected_chain (productionStream source.crypto)
      (PqxdhInitialSourceExperiment.root source (List.Vector.replicate 32 0) (RawCtxSelectedInitialConstructor.response64 block)
        (.beacon b : RawCtxProtocolReveals.Owner S B)) nonce chosen next kernel context pending admitted hidden
    have beaconCreated : PqxdhInitialReplyErasure.kernelOf true (RawCtxSelectedInitialConstructor.response64 block) =
        ok (PqxdhInitialRootAudit.kernel (List.Vector.replicate 32 0, RawCtxSelectedInitialConstructor.response64 block)) :=
      PqxdhBeaconPhase2Publication.normalInitial_exact _ _
    apply separate
    refine (RawCtxSendLineageCollision.initial_source_event source.crypto block _ server beaconCreated created).mp ?_
    subst kernelEq
    change server.refined.send_chain = RawCtxFreshChainCut.concreteChain
      (RawCtxSelectedQueryTrace.rootVector (PqxdhInitialRootAudit.kernel
        (List.Vector.replicate 32 0, RawCtxSelectedInitialConstructor.response64 block)).refined.send_chain) at chain
    apply BeaconcryptCore.Refinement.RepresentationBridge.absChain_injective
    have vectors := congrArg RawCtxSelectedQueryTrace.rootVector chain
    rw [RawCtxSelectedQueryTrace.rootVector_concrete] at vectors
    exact (congrArg Subtype.val vectors).symm

end Alias

section Ghost
open AdaptiveCtxDynamicKnownKeys CtxRomAuth AdaptiveCtxReceive

/-- Erase the selected public-hash log, which the challenger records but never reads. -/
def clearLog (state : SourceState) : SourceState := RawCtxSourceSharedRom.install state (state.cache, [])

/-- Erasing the log twice is erasing it once. -/
theorem clearLog_idem (state : SourceState) : clearLog (clearLog state) = clearLog state := rfl

/-- The local CTX operation reads no public-hash log: erasing the log before or after the operation gives the same result. -/
theorem local_ghost (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) (query : ReceiveSpec.Domain)
    (entry : AdaptiveCtxSharedHash.Local) :
    (fun result => (result.1, { result.2 with publicInputs := [] })) <$> (AdaptiveCtxSharedHash.localImpl decode c key query).run entry =
      (fun result => (result.1, { result.2 with publicInputs := [] })) <$>
        (AdaptiveCtxSharedHash.localImpl decode c key query).run { entry with publicInputs := [] } := by
  rcases query with (coin | (hash | input)) | raw
  · simp [AdaptiveCtxSharedHash.localImpl, StateT.run]
  · simp [AdaptiveCtxSharedHash.localImpl, StateT.run]
  · simp only [AdaptiveCtxSharedHash.localImpl, StateT.run, AdaptiveCtxSharedHash.localSeal]
    split_ifs <;> simp
  · simp only [AdaptiveCtxSharedHash.localImpl, StateT.run, AdaptiveCtxSharedHash.localRaw]
    split <;> simp

/-- The real selected operation acts on the local CTX history and keeps the suffix dictionary. -/
theorem modes_local (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) (query : ReceiveSpec.Domain)
    (entry : AdaptiveCtxSharedModes.Entry) :
    (AdaptiveCtxSharedModes.localImpl true decode c key query).run entry =
      (fun result => (result.1, (result.2, entry.2))) <$> (AdaptiveCtxSharedHash.localImpl decode c key query).run entry.1 := by
  simp only [AdaptiveCtxSharedModes.localImpl, ite_true, StateT.run, map_eq_bind_pure_comp]
  rfl

/-- One challenger operation reads no selected public-hash log. -/
theorem source_ghost_step (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) (query : Spec.Domain) (state : SourceState) :
    Prod.map id clearLog <$> (sourceImpl true decode c key query).run state =
      Prod.map id clearLog <$> (sourceImpl true decode c key query).run (clearLog state) := by
  cases query with
  | inl selected =>
    have ghost := congrArg (fun work => (fun result => (result.1.1, clearLog
      ({ state with selected := (result.1.2, state.selected.2), cache := result.2 } : SourceState))) <$>
        (simulateQ AdaptiveCtxSharedHash.hashImpl work).run state.cache) (local_ghost decode c key selected state.selected.1)
    simp only [simulateQ_map, StateT.run_map, Functor.map_map] at ghost
    change Prod.map id clearLog <$> (do
        let result ← (simulateQ AdaptiveCtxSharedHash.hashImpl
          ((AdaptiveCtxSharedModes.localImpl true decode c key selected).run state.selected)).run state.cache
        pure (result.1.1, { state with selected := result.1.2, cache := result.2 })) =
      Prod.map id clearLog <$> (do
        let result ← (simulateQ AdaptiveCtxSharedHash.hashImpl
          ((AdaptiveCtxSharedModes.localImpl true decode c key selected).run (clearLog state).selected)).run (clearLog state).cache
        pure (result.1.1, { clearLog state with selected := result.1.2, cache := result.2 }))
    rw [modes_local, modes_local]
    simp only [simulateQ_map, StateT.run_map, map_bind, map_pure, bind_map_left] at ghost ⊢
    simp only [bind_pure_comp]
    exact ghost
  | inr known =>
    simp only [sourceImpl, StateT.run, map_bind, map_pure]
    rfl

/-- An idempotent state erasure that commutes with every step of an interpreter commutes with every complete program. -/
theorem erase_program {ι σ X : Type} {spec : OracleSpec ι} (impl : QueryImpl spec (StateT σ ProbComp)) (erase : σ → σ)
    (idempotent : ∀ state, erase (erase state) = erase state)
    (step : ∀ query state, Prod.map id erase <$> (impl query).run state = Prod.map id erase <$> (impl query).run (erase state))
    (client : OracleComp spec X) (state : σ) :
    Prod.map id erase <$> (simulateQ impl client).run state = Prod.map id erase <$> (simulateQ impl client).run (erase state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => simp [idempotent]
  | query_bind query continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    have left : ((impl query).run state >>= fun result =>
        Prod.map id erase <$> (simulateQ impl (continuation result.1)).run result.2) =
        (Prod.map id erase <$> (impl query).run state) >>= fun result =>
          Prod.map id erase <$> (simulateQ impl (continuation result.1)).run result.2 := by
      rw [bind_map_left]
      exact bind_congr fun result => ih result.1 result.2
    have right : ((impl query).run (erase state) >>= fun result =>
        Prod.map id erase <$> (simulateQ impl (continuation result.1)).run result.2) =
        (Prod.map id erase <$> (impl query).run (erase state)) >>= fun result =>
          Prod.map id erase <$> (simulateQ impl (continuation result.1)).run result.2 := by
      rw [bind_map_left]
      exact bind_congr fun result => ih result.1 result.2
    rw [left, right, step]

/-- Every complete challenger program reads no selected public-hash log. -/
theorem source_ghost {X : Type} (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) (client : OracleComp Spec X)
    (state : SourceState) :
    Prod.map id clearLog <$> (simulateQ (sourceImpl true decode c key) client).run state =
      Prod.map id clearLog <$> (simulateQ (sourceImpl true decode c key) client).run (clearLog state) :=
  erase_program _ clearLog clearLog_idem (source_ghost_step decode c key) client state

end Ghost

section Budgets
open PqxdhNativeSharedPrefix PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry AdaptiveCtxDynamicKnownBounds AdaptiveCtxQueryBounds
variable {ι I D K X Response Shared A N C M P : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))

/-- Source-local callbacks make no selected seal request. -/
theorem external_no_seal (query : (PqxdhSelectedCallbackCompiler.External extra I D K X Response Shared).Domain)
    (state : Local A N C) :
    ((PqxdhSelectedCallbackCompiler.lower pre application initial selector aux (.inl query)).run state).IsQueryBoundP
      (TargetClass SourceSeal) 0 := by
  change (simulateQ RawCtxSourceSharedRom.forward
    ((PqxdhSelectedCallbackCompiler.callback pre application initial selector aux query).run state)).IsQueryBoundP _ 0
  simp only [RawCtxSourceSharedRom.forward, QueryImpl.simulateQ_compose]
  apply RawCtxSelectedSealConsumer.lifted_bound
  change (simulateQ AdaptiveCtxSharedTarget.forward
    ((PqxdhSelectedCallbackCompiler.callback pre application initial selector aux query).run state)).IsQueryBoundP SourceSeal 0
  apply AdaptiveCtxSharedTarget.forward_bound
  simp only [AdaptiveCtxSharedTarget.forward_seal_class]
  exact isQueryBoundP_false _ 0

/-- Source-local callbacks make no shared-ROM hash request. -/
theorem external_no_hash (query : (PqxdhSelectedCallbackCompiler.External extra I D K X Response Shared).Domain)
    (state : Local A N C) :
    ((PqxdhSelectedCallbackCompiler.lower pre application initial selector aux (.inl query)).run state).IsQueryBoundP
      HashRoute 0 := by
  change (simulateQ RawCtxSourceSharedRom.forward
    ((PqxdhSelectedCallbackCompiler.callback pre application initial selector aux query).run state)).IsQueryBoundP _ 0
  simp only [RawCtxSourceSharedRom.forward, QueryImpl.simulateQ_compose]
  apply RawCtxSelectedSealConsumer.lifted_bound
  change (simulateQ AdaptiveCtxSharedTarget.forward
    ((PqxdhSelectedCallbackCompiler.callback pre application initial selector aux query).run state)).IsQueryBoundP SourceHash 0
  apply AdaptiveCtxSharedTarget.forward_bound
  simpa only [AdaptiveCtxSharedTarget.forward_hash_class] using
    PqxdhSelectedCallbackCompiler.callback_no_hash pre application initial selector aux query state

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)

/-- Every compiled post request makes at most one request of any class that the source-local callbacks never use. -/
theorem post_step (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate]
    (externalZero : ∀ query state, ((PqxdhSelectedCallbackCompiler.lower (extra := extra) (I := I) (D := D) (K := K) (X := X)
      (Response := Response) (Shared := Shared) pre application initial selector aux (.inl query)).run state).IsQueryBoundP predicate 0)
    (query : (PqxdhInitialGenericPost.Spec extra S B).Domain)
    (before : PqxdhSelectedPostCompiler.State M P I D K A N C S B) :
    (((PqxdhSelectedPostCompiler.impl pre application initial selector aux source writer prior parent target nonce next sender route read
      query).run).run before).IsQueryBoundP predicate 1 := by
  rcases query with (request | request) | request
  · simp only [PqxdhSelectedPostCompiler.impl, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff]
    have actual := RawCtxSelectedFamilyLiveCompiler.step_queries source writer prior parent target nonce next sender route read
      request before.1.roles
    exact (IsQueryBoundP.of_imp (fun _ _ => True.intro) ((isQueryBoundP_true_iff _ _).mpr actual)).mono
      (by cases request <;> simp only [RawCtxRevealBudgets.weight] <;> omega)
  · simp only [PqxdhSelectedPostCompiler.impl, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff]
    exact (externalZero _ before.2).mono (by omega)
  · cases request with
    | finish index raw =>
      simp only [PqxdhSelectedPostCompiler.impl, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff]
      apply (PqxdhSelectedInitialOwnerCompiler.owner_finish_queries (extra := extra) (X := X) (Response := Response)
        (Shared := Shared) raw (before.1.roles.1.2 index)).simulateQ_run_of_step
      · intro query selected state
        cases query with
        | inl query => exact False.elim selected
        | inr request =>
          simp only [PqxdhSelectedInitialOwnerCompiler.lower, StateT.run, isQueryBoundP_map_iff]
          exact IsQueryBoundP.of_imp (fun _ _ => True.intro)
            ((isQueryBoundP_true_iff _ _).mpr (PqxdhSelectedBeaconCompiler.finish_queries prior parent target nonce next read
              request.control request.before request.candidate request.kernel request.application))
      · intro query excluded state
        cases query with
        | inl query => exact externalZero query state
        | inr request => exact False.elim (excluded True.intro)

/-- The compiled post client makes at most `qPost` requests of any class used at most once per post request. -/
theorem post_client (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate]
    (step : ∀ query (before : PqxdhSelectedPostCompiler.State M P I D K A N C S B),
      (((PqxdhSelectedPostCompiler.impl (extra := extra) pre application initial selector aux source writer prior parent target nonce next
        sender route read query).run).run before).IsQueryBoundP predicate 1)
    {Result : Type} (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result) (qPost : Nat)
    (bounded : work.IsTotalQueryBound qPost) (before : PqxdhSelectedPostCompiler.State M P I D K A N C S B) :
    (PqxdhSelectedPostCompiler.client pre application initial selector aux source writer prior parent target nonce next sender route read
      work before).IsQueryBoundP predicate qPost := by
  induction work using OracleComp.inductionOn generalizing qPost before with
  | pure value => trivial
  | query_bind query continuation ih =>
    rw [isTotalQueryBound_query_bind_iff] at bounded
    obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt bounded.1)
    simp only [PqxdhSelectedPostCompiler.client, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
      StateT.run_bind]
    rw [Nat.succ_eq_add_one, Nat.add_comm]
    apply isQueryBoundP_bind (step query before)
    rintro ⟨none | answer, after⟩ _
    · trivial
    · exact ih answer remaining (by simpa using bounded.2 answer) after

/-- Separate caps over a finite partition bound the total number of requests by their sum. -/
theorem total_of_kinds {Kind ι Result : Type} [Fintype Kind] [DecidableEq Kind] {spec : OracleSpec ι}
    (classify : spec.Domain → Kind) (client : OracleComp spec Result) (budget : Kind → Nat)
    (bounded : ∀ kind, client.IsQueryBoundP (fun query => classify query = kind) (budget kind)) :
    client.IsTotalQueryBound (∑ kind, budget kind) := by
  induction client using OracleComp.inductionOn generalizing budget with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [isQueryBoundP_query_bind_iff] at bounded
    have positive : 0 < budget (classify query) := by simpa using (bounded (classify query)).1
    have step := FinitePartitionQueryBounds.bill_step (fun _ => 1) budget (classify query) positive
    simp only [FinitePartitionQueryBounds.bill, one_mul] at step
    rw [isTotalQueryBound_query_bind_iff]
    refine ⟨by omega, fun answer => ?_⟩
    have rest := ih answer (Function.update budget (classify query) (budget (classify query) - 1)) (fun kind => by
      by_cases same : classify query = kind
      · subst kind
        simpa only [Function.update_self, ite_true] using (bounded (classify query)).2 answer
      · simpa only [Function.update_of_ne (Ne.symm same), same, ite_false] using (bounded kind).2 answer)
    rwa [show (∑ kind, budget kind) - 1 = ∑ kind, Function.update budget (classify query) (budget (classify query) - 1) kind by omega]

/-- A local compiled program makes at most `bound` requests of the class from every local state. -/
def Uses {Local X : Type} (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate] (bound : Nat)
    (x : StateT Local (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) X) : Prop :=
  ∀ state, (x.run state).IsQueryBoundP predicate bound

section Uses
variable {Local : Type} (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate]

/-- Pure programs make no request. -/
theorem uses_pure {X : Type} (bound : Nat) (value : X) :
    Uses predicate bound (pure value : StateT Local (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) X) :=
  fun _ => trivial

/-- Request budgets add along bind. -/
theorem uses_bind {X Y : Type} {first second bound : Nat} {x : StateT Local (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) X}
    {f : X → StateT Local (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) Y}
    (head : Uses predicate first x) (tail : ∀ value, Uses predicate second (f value)) (sum : first + second ≤ bound) :
    Uses predicate bound (x >>= f) := by
  intro state
  rw [StateT.run_bind]
  exact (isQueryBoundP_bind (head state) fun result _ => tail result.1 result.2).mono sum

/-- Request budgets are monotone. -/
theorem uses_mono {X : Type} {small large : Nat} {x : StateT Local (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) X}
    (bounded : Uses predicate small x) (le : small ≤ large) : Uses predicate large x :=
  fun state => (bounded state).mono le

/-- Mapping adds no request. -/
theorem uses_map {X Y : Type} {bound : Nat} (h : X → Y) {x : StateT Local (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) X}
    (bounded : Uses predicate bound x) : Uses predicate bound (h <$> x) := by
  rw [map_eq_bind_pure_comp]
  exact uses_bind predicate bounded (fun value => uses_pure predicate 0 _) (by omega)

/-- A Rust result continuation keeps the budget. -/
theorem uses_continue {V X : Type} {bound : Nat} (result : RustM V)
    {f : V → StateT Local (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) (RustM X)}
    (bounded : ∀ value, Uses predicate bound (f value)) :
    Uses predicate bound (PqxdhInitialGenericBuilder.continueRust result f) := by
  cases result with
  | ok value => exact bounded value
  | fail error => exact uses_pure predicate bound _
  | div => exact uses_pure predicate bound _

/-- A conditional keeps the budget of both branches. -/
theorem uses_ite {X : Type} {bound : Nat} (condition : Prop) [Decidable condition]
    {x₁ x₂ : StateT Local (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) X}
    (positive : Uses predicate bound x₁) (negative : Uses predicate bound x₂) :
    Uses predicate bound (if condition then x₁ else x₂) := by
  split_ifs
  · exact positive
  · exact negative

end Uses

open PqxdhInitialGenericBuilder PqxdhInitialGenericPublication in
/-- The compiled Ready builder makes at most one request of any class that the source-local callbacks never use: only its first send can make one. -/
theorem ready_uses (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate]
    (externalZero : ∀ query state, ((PqxdhSelectedCallbackCompiler.lower (extra := extra) (I := I) (D := D) (K := K) (X := X)
      (Response := Response) (Shared := Shared) pre application initial selector aux (.inl query)).run state).IsQueryBoundP predicate 0)
    {Metadata PeerMetadata Consumed : Type} (initialKernel : RustM RawCtxSelectedMessageReveals.Kernel)
    (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State RawCtxSelectedMessageReveals.Kernel Metadata PeerMetadata Consumed) :
    Uses predicate 1 (readyBuild source (compiledCalls (A := A) (N := N) (C := C) source writer prior parent target nonce next)
      (compiledAux (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared)
        pre application initial selector aux) initialKernel binding ready metadata state) := by
  have auxZero : ∀ request, Uses predicate 0 (compiledAux (extra := extra) (I := I) (D := D) (K := K) (X := X)
      (Response := Response) (Shared := Shared) pre application initial selector aux request) :=
    fun request => externalZero _
  have sendOne : ∀ kernel context, Uses predicate 1
      ((compiledCalls (A := A) (N := N) (C := C) source writer prior parent target nonce next).send kernel context) := by
    intro kernel context state
    change ((fun result => (result.getD (kernel, none), state)) <$>
      RawCtxSelectedSendCompiler.send source writer prior parent target nonce next kernel context).IsQueryBoundP predicate 1
    rw [isQueryBoundP_map_iff]
    exact IsQueryBoundP.of_imp (fun _ _ => True.intro)
      ((isQueryBoundP_true_iff _ _).mpr (RawCtxSelectedSendCompiler.send_queries source writer prior parent target nonce next
        kernel context))
  have after : ∀ (candidate : pqxdh.ServerRegistrationCandidate) authenticated kernel,
      Uses predicate 1 (afterInitialization (compiledCalls (A := A) (N := N) (C := C) source writer prior parent target nonce next)
        (compiledAux (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared)
          pre application initial selector aux) candidate authenticated kernel metadata state) := by
    intro candidate authenticated kernel
    unfold afterInitialization
    refine uses_bind predicate (sendOne _ _) (fun sent => ?_) (show 1 + 0 ≤ 1 by omega)
    rcases sent with ⟨advanced, encrypted⟩
    refine uses_bind predicate (auxZero _) (fun _ => ?_) (show 0 + 0 ≤ 0 by omega)
    cases encrypted with
    | none => exact uses_pure predicate 0 _
    | some encrypted =>
      refine uses_bind predicate (auxZero _) (fun serialized => ?_) (show 0 + 0 ≤ 0 by omega)
      cases serialized with
      | none => exact uses_pure predicate 0 _
      | some serialized => exact uses_pure predicate 0 _
  unfold readyBuild usedBuild
  refine uses_continue predicate _ fun following => ?_
  cases following with
  | Err error => exact uses_pure predicate 1 _
  | Ok following =>
    refine uses_continue predicate _ fun prepared => ?_
    cases prepared with
    | Err error => exact uses_pure predicate 1 _
    | Ok value =>
      unfold candidate
      refine uses_bind predicate (auxZero _) (fun valid => ?_) (show 0 + 1 ≤ 1 by omega)
      refine uses_ite predicate _ (uses_pure predicate 1 _) ?_
      refine uses_bind predicate (auxZero _) (fun reserved => ?_) (show 0 + 1 ≤ 1 by omega)
      refine uses_ite predicate _ (uses_pure predicate 1 _) ?_
      refine uses_continue predicate _ fun kernel => ?_
      refine uses_ite predicate _ (uses_pure predicate 1 _) ?_
      refine uses_ite predicate _ ?_ (uses_pure predicate 1 _)
      refine uses_bind predicate (auxZero _) (fun allocated => ?_) (show 0 + 1 ≤ 1 by omega)
      refine uses_ite predicate _ (uses_pure predicate 1 _) ?_
      refine uses_continue predicate _ fun binding => ?_
      exact uses_map predicate _ (after _ _ kernel)

/-- A forwarded shared-ROM program makes no selected raw-opening request. -/
theorem forward_no_open {Result : Type} (work : OracleComp AdaptiveCtxSharedHash.HashSpec Result) :
    (simulateQ RawCtxSourceSharedRom.forward work).IsQueryBoundP (TargetClass AdaptiveCtxReceive.IsRawQuery) 0 := by
  simp only [RawCtxSourceSharedRom.forward, QueryImpl.simulateQ_compose]
  apply RawCtxSelectedSealConsumer.lifted_bound
  change (simulateQ AdaptiveCtxSharedTarget.forward work).IsQueryBoundP AdaptiveCtxReceive.IsRawQuery 0
  apply AdaptiveCtxSharedTarget.forward_bound
  simp only [AdaptiveCtxSharedTarget.forward_raw_class]
  exact isQueryBoundP_false work 0

/-- A forwarded shared-ROM program makes no selected seal request. -/
theorem forward_no_seal {Result : Type} (work : OracleComp AdaptiveCtxSharedHash.HashSpec Result) :
    (simulateQ RawCtxSourceSharedRom.forward work).IsQueryBoundP (TargetClass SourceSeal) 0 := by
  simp only [RawCtxSourceSharedRom.forward, QueryImpl.simulateQ_compose]
  apply RawCtxSelectedSealConsumer.lifted_bound
  change (simulateQ AdaptiveCtxSharedTarget.forward work).IsQueryBoundP SourceSeal 0
  apply AdaptiveCtxSharedTarget.forward_bound
  simp only [AdaptiveCtxSharedTarget.forward_seal_class]
  exact isQueryBoundP_false work 0

end Budgets

section Generic
open PqxdhNativeSharedPrefix PqxdhSelectedStateInterpreter PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open RawCtxSelectedParentTable PqxdhSelectedFirstRecord PqxdhFirstBeaconRecordIntegrity PqxdhCorrelatedExpand
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
    (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
    (before : PqxdhInitialOriginPostPath.Front M P I D K S B) (selected : RawCtxProtocolReveals.Owner S B)
    (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)
    (store : RawCtxSelectiveChainGame.Store) (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)

local notation "target" => PqxdhInitialSourceExperiment.root source previousRoot response64 selected
local notation "challenger" => AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder decode) source.crypto key

/-- The key-free first-record CTX client after the preparation: the compiled first Server builder followed by the executable post client; it returns whether the post client did not stop and returned `true`. -/
noncomputable def firstClient : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool := do
  let built ← ((compiledBuild pre application initial selector aux source writer (productionStream source.crypto) none target
    nonce next sender (initialKernel response64) index metadata ready).run (initialFront before)).run
      (initialShared shared privateState cache store).1
  let result ← ((simulateQ (PqxdhSelectedPostCompiler.impl pre application initial selector aux source writer
    (productionStream source.crypto) none target nonce next sender route decode) (post built.1.1)).run).run (built.1.2, built.2)
  pure (decide (result.1 = some true))

/-- The first client makes at most one builder request plus `qPost` post requests of any class that the source-local callbacks never use. -/
theorem firstClient_uses (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate]
    (externalZero : ∀ query state, ((PqxdhSelectedCallbackCompiler.lower (extra := extra) (I := I) (D := D) (K := K) (X := X)
      (Response := Response) (Shared := PqxdhPhase2DecapsulationRouting.Shared) pre application initial selector aux
        (.inl query)).run state).IsQueryBoundP predicate 0)
    (qPost : Nat) (postBound : ∀ reply, (post reply).IsTotalQueryBound qPost) :
    (firstClient pre application initial selector aux source writer previousRoot response64 sender route decode index metadata ready
      post before selected shared privateState cache store nonce next).IsQueryBoundP predicate (1 + qPost) := by
  unfold firstClient
  refine isQueryBoundP_bind ((uses_map predicate _ (ready_uses pre application initial selector aux source writer
    (productionStream source.crypto) none target nonce next predicate externalZero (initialKernel response64) _ ready metadata _))
      (initialShared shared privateState cache store).1) fun built _ => ?_
  refine (isQueryBoundP_bind (post_client pre application initial selector aux source writer (productionStream source.crypto) none
    target nonce next sender route decode predicate (post_step pre application initial selector aux source writer
      (productionStream source.crypto) none target nonce next sender route decode predicate externalZero)
    (post built.1.1) qPost (postBound _) (built.1.2, built.2)) (m := 0) fun _ _ => ?_).mono (by omega)
  simp

/-- The executable post bit from a full compiled state. -/
noncomputable def postBit (reply : RustM (Option PqxdhServerRegistrationPublication.Response))
    (start : PqxdhSelectedPostCompiler.Full M P I D K A N RootOracle.QueryCache S B) : ProbComp Bool :=
  (fun result => decide (result.1 = some true)) <$>
    (evaluate challenger (simulateQ (PqxdhSelectedPostCompiler.impl pre application initial selector aux source writer
      (productionStream source.crypto) none target nonce next sender route decode) (post reply)).run).run start

/-- The executable post bit reads no selected public-hash log. -/
theorem postBit_ghost (reply : RustM (Option PqxdhServerRegistrationPublication.Response))
    (state : PqxdhSelectedPostCompiler.State M P I D K A N RootOracle.QueryCache S B)
    (component : AdaptiveCtxDynamicKnownKeys.SourceState) :
    postBit pre application initial selector aux source writer previousRoot response64 sender route decode post selected key nonce next
        reply (state, component) =
      postBit pre application initial selector aux source writer previousRoot response64 sender route decode post selected key nonce next
        reply (state, clearLog component) := by
  have ghost := congrArg (fun work => (fun result : (Option Bool × PqxdhSelectedPostCompiler.State M P I D K A N RootOracle.QueryCache S B) ×
      AdaptiveCtxDynamicKnownKeys.SourceState => decide (result.1.1 = some true)) <$> work)
    (source_ghost (RawCtxUniversalDecoder.decoder decode) source.crypto key
      (((simulateQ (PqxdhSelectedPostCompiler.impl pre application initial selector aux source writer
        (productionStream source.crypto) none target nonce next sender route decode) (post reply)).run).run state) component)
  simp only [Functor.map_map, Prod.map_fst, id_eq] at ghost
  simp only [postBit, evaluate, StateT.run, Functor.map_map, pair]
  convert ghost using 3
  all_goals rfl

/-- When every first send of the initial Server kernel is known, C4's compiled first-record run is exactly the key-free first client evaluated by the selected-key challenger from any start that differs from the initial challenger only by the preparation cache `shared.2` and a public-hash log. -/
theorem run_client
    (known : ∀ kernel, initialKernel response64 = .ok kernel → ∀ context,
      KnownSend (productionStream source.crypto) none target nonce next kernel context)
    (log : List Pqxdh.Bytes) :
    compiledRun pre application initial selector aux source writer previousRoot response64 sender route decode index metadata ready
        post before selected shared privateState cache store key nonce next =
      Prod.fst <$> (simulateQ challenger (firstClient pre application initial selector aux source writer previousRoot response64
        sender route decode index metadata ready post before selected shared privateState cache store nonce next)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log)) := by
  have related := build_rel pre application initial selector aux source writer (productionStream source.crypto) none key target
    nonce next decode sender (initialKernel response64) index metadata ready (initialFront before) known
    ((initialShared shared privateState cache store).1,
      RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log))
  simp only [evaluate, StateT.run] at related
  have clientEq : Prod.fst <$> (simulateQ challenger (firstClient pre application initial selector aux source writer previousRoot
      response64 sender route decode index metadata ready post before selected shared privateState cache store nonce next)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log)) =
      (simulateQ challenger (((compiledBuild pre application initial selector aux source writer (productionStream source.crypto) none
        target nonce next sender (initialKernel response64) index metadata ready).run (initialFront before)).run
          (initialShared shared privateState cache store).1)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log)) >>= fun result =>
        postBit pre application initial selector aux source writer previousRoot response64 sender route decode post selected key
          nonce next result.1.1.1 ((result.1.1.2, result.1.2), result.2) := by
    simp only [firstClient, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure]
    refine bind_congr fun result => ?_
    simp only [postBit, bind_pure_comp]
    change _ = (fun result => decide (result.1 = some true)) <$> (pair <$> (simulateQ challenger
      (((simulateQ (PqxdhSelectedPostCompiler.impl pre application initial selector aux source writer
        (productionStream source.crypto) none target nonce next sender route decode) (post result.1.1.1)).run).run
          (result.1.1.2, result.1.2))).run result.2)
    rw [Functor.map_map]
    rfl
  have cleaned : ((simulateQ challenger (((compiledBuild pre application initial selector aux source writer
      (productionStream source.crypto) none target nonce next sender (initialKernel response64) index metadata ready).run
        (initialFront before)).run (initialShared shared privateState cache store).1)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log)) >>= fun result =>
        postBit pre application initial selector aux source writer previousRoot response64 sender route decode post selected key
          nonce next result.1.1.1 ((result.1.1.2, result.1.2), result.2)) =
      ((simulateQ challenger (((compiledBuild pre application initial selector aux source writer
      (productionStream source.crypto) none target nonce next sender (initialKernel response64) index metadata ready).run
        (initialFront before)).run (initialShared shared privateState cache store).1)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log)) >>= fun result =>
        postBit pre application initial selector aux source writer previousRoot response64 sender route decode post selected key
          nonce next result.1.1.1 ((result.1.1.2, result.1.2),
            { AdaptiveCtxDynamicKnownKeys.initialSource with cache := result.2.cache })) := by
    refine bind_congr_of_forall_mem_support _ fun result supported => ?_
    obtain ⟨shared', clean⟩ := related.2 (pair result) (by
      simp only [support_map, Set.mem_image]
      exact ⟨result, supported, rfl⟩)
    rw [postBit_ghost]
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
  rw [clientEq, cleaned]
  unfold compiledRun
  rw [build, bind_map_left, bind_map_left]
  rfl

end Generic

section Observer
open RawCtxSelectedAuthenticationObserver AdaptiveCtxReceive CtxRomAuth

/-- The monitored gap game: the selected-key challenger runs the monitored client, and the event is that the client returned `true` while the ordinary authentication observer did not win. -/
noncomputable def gapGame (decode : RawDecoder) (c : Pqxdh.Crypto) (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool) :
    ProbComp Bool := do
  let key ← $ᵗ CtxKey
  let result ← (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true decode c key) (monitor client initialState)).run
    AdaptiveCtxDynamicKnownKeys.initialSource
  pure (result.1.1 && !won decode result.1.2)

/-- A Boolean client's `true` mass in the selected-key source experiment is at most the ordinary observer's winning mass plus the gap game. -/
theorem client_le_decision (decode : RawDecoder) (c : Pqxdh.Crypto) (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool) :
    𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true decode c client] {true} ≤
      𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true decode c (decision decode client)] {true} +
        𝒟[gapGame decode c client] {true} := by
  have erased : client = Prod.fst <$> monitor client initialState := (monitor_erase client initialState).symm
  unfold AdaptiveCtxDynamicKnownKeys.sourceGame gapGame decision
  conv_lhs => rw [erased]
  simp only [simulateQ_map, StateT.run_map, map_bind, Functor.map_map]
  refine PqxdhFirstBeaconRecordIntegrity.true_bind_le _ _ _ _ fun key => ?_
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  refine PqxdhFirstBeaconRecordIntegrity.true_bind_le _ _ _ _ fun result => ?_
  cases result.1.1 <;> cases won decode result.1.2 <;> simp

end Observer

/-- Pointwise domination of Boolean continuations is preserved by bind. -/
theorem true_bind_mono {α : Type} (mx : ProbComp α) (f g : α → ProbComp Bool)
    (le : ∀ a, 𝒟[f a] {true} ≤ 𝒟[g a] {true}) : 𝒟[mx >>= f] {true} ≤ 𝒟[mx >>= g] {true} := by
  have pointwise : ∀ a, Pr{let x ← f a}[x = true] ≤ Pr{let x ← g a}[x = true] := fun a => by
    rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton]
    exact le a
  rw [← prEvent_eq_evalDist_singleton (mx >>= f), ← prEvent_eq_evalDist_singleton (mx >>= g)]
  simp only [OracleComp.prEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left (pointwise a) zero_le

section Prepared
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity CtxRomAuth AdaptiveCtxSharedHash
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

/-- The private preparation packet of the shared-ROM preparation. -/
abbrev Packet := PqxdhSourceSharedPreparation.Packet
  (PqxdhSourceSharedPreparation.LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program) KemSK

/-- The key-free preparation prelude: the complete shared-ROM preparation, then the 64-byte initializer response, the selected nonce and the next chain, all drawn through the shared ROM's uniform interface. -/
noncomputable def prelude : OracleComp HashSpec
    (Packet (M := M) (P := P) (I := I) (K := K) (A := A) (KemSK := KemSK) setup program × HmacBlock × NonceOutput × RootOutput) := do
  let packet ← PqxdhSourceSharedPreparation.prepare setup env callbacks program post attachedVerify primitives baseImpl kem
  let initialBlock ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ HmacBlock)
  let nonce ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ NonceOutput)
  let chain ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ RootOutput)
  pure (packet, initialBlock, nonce, chain)

/-- Restoring the reached cache in the prelude's packet gives the prepared context of C4's compiled game. -/
noncomputable def restoreSample
    (sample : Packet (M := M) (P := P) (I := I) (K := K) (A := A) (KemSK := KemSK) setup program × HmacBlock × NonceOutput × RootOutput)
    (cache : CtxRO.QueryCache) :=
  (PqxdhSourceSharedPreparation.restore setup env callbacks program post attachedVerify primitives kem sample.1 cache ∅,
    sample.2.1, sample.2.2.1, sample.2.2.2)

/-- Evaluating the prelude from the empty ROM and restoring its cache is C4's preparation and three uniform draws. -/
theorem prelude_source :
    (fun result => restoreSample setup env callbacks kem attachedVerify primitives program post result.1 result.2) <$>
      (simulateQ hashImpl (prelude setup env callbacks baseImpl kem attachedVerify primitives program post)).run ∅ =
    (do
      let context ← PqxdhCorrelatedExtractFamily.prepare baseImpl kem
        (PqxdhAuthenticatedRootExperiment.protocol env0 kem attachedVerify primitives program post)
      let initialBlock ← $ᵗ HmacBlock
      let nonce ← $ᵗ NonceOutput
      let chain ← $ᵗ RootOutput
      pure (context, initialBlock, nonce, chain)) := by
  rw [← PqxdhSourceSharedPreparation.prepare_empty setup env callbacks program post attachedVerify primitives baseImpl kem]
  simp only [prelude, simulateQ_bind, StateT.run_bind, map_bind, RawCtxSelectiveSharedRom.coins_complete, bind_map_left]
  refine bind_congr fun result => ?_
  refine bind_congr fun initialBlock => ?_
  refine bind_congr fun nonce => ?_
  refine bind_congr fun chain => ?_
  simp only [simulateQ_pure, StateT.run_pure, map_pure, restoreSample]

/-- The key-free suffix after the prelude: completed preparations give `false`; a pending preparation runs the key-free first client with the prepared callbacks of the packet's own KEM secret and challenge. -/
noncomputable def suffix (target : Target S (B + 1))
    (sample : Packet (M := M) (P := P) (I := I) (K := K) (A := A) (KemSK := KemSK) setup program × HmacBlock × NonceOutput × RootOutput) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool :=
  match PqxdhSourceSharedInput.input setup env callbacks program post attachedVerify primitives baseImpl kem
      target.owner target.number target.ancestors target.disclosed sample.1 with
  | .inl _ => pure false
  | .inr input => firstClient
      (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        sample.1.secretKey sample.1.ciphertext)
      (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        sample.1.secretKey sample.1.ciphertext)
      (initialLocal (A := A) (N := BareState 1) (env0).source input.selectedMessage zeroRoot
        (RawCtxSelectedInitialConstructor.response64 sample.2.1))
      (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A)
        (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem sample.1.secretKey sample.1.ciphertext))
      (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks)
      (env0).source (env0).recordWriter zeroRoot (RawCtxSelectedInitialConstructor.response64 sample.2.1)
      (env0).senderId (env0).route (env0).decode input.index input.metadata { input.ready with root := zeroRoot } input.post
      input.before input.selected input.shared input.privateState input.cache emptyStore sample.2.2.1 sample.2.2.2

/-- The constructed key-free CTX client of the first Beacon record: the forwarded preparation prelude followed by the suffix. -/
noncomputable def fullClient (target : Target S (B + 1)) : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool :=
  simulateQ RawCtxSourceSharedRom.forward (prelude setup env callbacks baseImpl kem attachedVerify primitives program post) >>=
    suffix setup env callbacks baseImpl kem attachedVerify primitives program post target

/-- A pending prepared input keeps the requested owner. -/
theorem input_selected (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (packet : Packet (M := M) (P := P) (I := I) (K := K) (A := A) (KemSK := KemSK) setup program)
    (input : PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response) (A := A)
      (S := S) (B := B) (setup := setup))
    (pending : PqxdhSourceSharedInput.input setup env callbacks program post attachedVerify primitives baseImpl kem
      owner number ancestors disclosed packet = .inr input) :
    input.selected = owner := by
  unfold PqxdhSourceSharedInput.input PqxdhInitialPreparedSourceInput.input at pending
  split at pending
  · cases pending
  · cases pending
    rfl

/-- Resource contract of the shared-ROM preparation: `PqxdhSourceSharedPreparation.prepare` for the post `post` makes at most `qPrepare` public-hash requests on every path. It is a query count of an existing library program, not a probability bound, and it does not mention the selected key or any secret. Production satisfies it because the preparation's program, post, callbacks and generators each make finitely many requests; `prepare_hash_budget` discharges it with `69 * qMain + 1 + 69 * qPost` from the caps taken by `PqxdhSourceSharedPreparationResources.prepare`. -/
def PrepareHashBudget (qPrepare : Nat) : Prop :=
  (PqxdhSourceSharedPreparation.prepare setup env callbacks program post attachedVerify primitives baseImpl kem).IsQueryBoundP
    (HashClass true) qPrepare

/-- The preparation hash contract is satisfiable: from the source callback, generator, program and post caps of `PqxdhSourceSharedPreparationResources.prepare`, the preparation makes at most `69 * qMain + 1 + 69 * qPost` public-hash requests. -/
theorem prepare_hash_budget (qPost qSelector qLocal qPeer qPlaintext qWriter : Nat)
    (postBound : ∀ selection response, (post selection response).IsTotalQueryBound qPost)
    (peerBound : ∀ state, (callbacks.reservePeer.run state).IsTotalQueryBound qPeer)
    (plaintextBound : ∀ size state, ((callbacks.reservePlaintext size).run state).IsTotalQueryBound qPlaintext)
    (writerBound : ∀ fields state, ((callbacks.responseWrite fields).run state).IsTotalQueryBound qWriter)
    (qEphemeral qEncaps : Nat)
    (ephemeralBound : (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) env.ephemeralGen).IsTotalQueryBound qEphemeral)
    (nativeEncapsBound : ∀ target,
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (env.native.encaps target)).IsTotalQueryBound qEncaps)
    (encapsBound : ∀ target, (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.encaps target)).IsTotalQueryBound qEncaps)
    (qPre qOne qPhase1Write qMain : Nat)
    (preBound : ∀ identity, (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPre)
    (oneBound : ∀ identity before target,
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (setup.oneTime identity before target)).IsTotalQueryBound qOne)
    (phase1WriteBound : ∀ candidate state, ((callbacks.phase1Write candidate).run state).IsTotalQueryBound qPhase1Write)
    (mainBound : ∀ published, (program.main published).IsTotalQueryBound qMain)
    (qKeygen : Nat)
    (keygenBound : (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (selectorBound : ∀ secret query state,
      (evalKem baseImpl kem secret ((borrowedSelector attachedVerify primitives 1 query).run state)).IsTotalQueryBound qSelector)
    (localBound : ∀ secret query state, PqxdhOrdinaryNativeCache.sourceSafe query →
      ((PqxdhOrdinaryNativeCache.cacheFree attachedVerify primitives 1 env.source env.localImpl baseImpl kem secret query).run
        state).IsTotalQueryBound qLocal) :
    PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program post (69 * qMain + 1 + 69 * qPost) :=
  PqxdhSourceSharedPreparationResources.prepare setup env callbacks program post attachedVerify primitives baseImpl kem
    qPost qSelector qLocal qPeer qPlaintext qWriter postBound peerBound plaintextBound writerBound
    qEphemeral qEncaps ephemeralBound nativeEncapsBound encapsBound qPre qOne qPhase1Write qMain
    preBound oneBound phase1WriteBound mainBound qKeygen keygenBound selectorBound localBound true

/-- The forwarded prelude has the hash budget of the shared-ROM preparation: the three uniform draws add no hash request. -/
theorem prelude_hash (qPrepare : Nat)
    (prepareHash : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program post qPrepare) :
    (simulateQ RawCtxSourceSharedRom.forward (prelude setup env callbacks baseImpl kem attachedVerify primitives program post)).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.HashRoute qPrepare := by
  have inner : (prelude setup env callbacks baseImpl kem attachedVerify primitives program post).IsQueryBoundP
      (HashClass true) qPrepare := by
    unfold prelude
    refine (isQueryBoundP_bind (show (PqxdhSourceSharedPreparation.prepare setup env callbacks program post attachedVerify primitives
      baseImpl kem).IsQueryBoundP (HashClass true) qPrepare from prepareHash) fun packet _ =>
      isQueryBoundP_bind (RawCtxSelectiveSharedRom.coins_no_hash _) fun initialBlock _ =>
        isQueryBoundP_bind (RawCtxSelectiveSharedRom.coins_no_hash _) fun nonce _ =>
          isQueryBoundP_bind (RawCtxSelectiveSharedRom.coins_no_hash _) (m := 0) fun chain _ => ?_).mono (by omega)
    simp
  simp only [RawCtxSourceSharedRom.forward, QueryImpl.simulateQ_compose]
  apply RawCtxSelectedSealConsumer.lifted_bound
  change (simulateQ AdaptiveCtxSharedTarget.forward (prelude setup env callbacks baseImpl kem attachedVerify primitives program post)).IsQueryBoundP
    AdaptiveCtxQueryBounds.SourceHash qPrepare
  apply AdaptiveCtxSharedTarget.forward_bound
  simpa only [AdaptiveCtxSharedTarget.forward_hash_class] using inner

/-- A pending prepared input carries the post of its own selection. -/
theorem input_post (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (packet : Packet (M := M) (P := P) (I := I) (K := K) (A := A) (KemSK := KemSK) setup program)
    (input : PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response) (A := A)
      (S := S) (B := B) (setup := setup))
    (pending : PqxdhSourceSharedInput.input setup env callbacks program post attachedVerify primitives baseImpl kem
      owner number ancestors disclosed packet = .inr input) :
    ∃ selection, input.post = post selection := by
  unfold PqxdhSourceSharedInput.input PqxdhInitialPreparedSourceInput.input at pending
  split at pending
  · cases pending
  · cases pending
    exact ⟨_, rfl⟩

/-- The constructed client's request budget in any class that the source-local callbacks never use: the forwarded prelude's budget, one builder request and the post budget. -/
theorem fullClient_uses (target : Target S (B + 1)) (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate]
    (externalZero : ∀ (secret : KemSK) (challenge : MlKem768Ciphertext) (selectedMessage : Message) (response : PqxdhInitialRootLabelService.Response)
      query state, ((PqxdhSelectedCallbackCompiler.lower (extra := SelectorSpec baseSpec)
        (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem secret challenge)
        (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem secret challenge)
        (initialLocal (A := A) (N := BareState 1) (env0).source selectedMessage zeroRoot response)
        (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A)
          (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem secret challenge))
        (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) (.inl query)).run state).IsQueryBoundP predicate 0)
    (qPrelude : Nat)
    (preludeBound : (simulateQ RawCtxSourceSharedRom.forward
      (prelude setup env callbacks baseImpl kem attachedVerify primitives program post)).IsQueryBoundP predicate qPrelude)
    (qPost : Nat) (postBound : ∀ selection reply, (post selection reply).IsTotalQueryBound qPost) :
    (fullClient setup env callbacks baseImpl kem attachedVerify primitives program post target).IsQueryBoundP predicate
      (qPrelude + (1 + qPost)) := by
  refine isQueryBoundP_bind preludeBound fun sample _ => ?_
  unfold suffix
  split
  · simp
  · rename_i input pending
    obtain ⟨selection, selected⟩ := input_post setup env callbacks baseImpl kem attachedVerify primitives program post _ _ _ _
      sample.1 input pending
    apply firstClient_uses (predicate := predicate) (externalZero := externalZero _ _ _ _) (qPost := qPost)
    exact fun reply => selected ▸ postBound selection reply

/-- C4's compiled game with the initial half-alias runs mapped to `false`. -/
noncomputable def separatedGame (target : Target S (B + 1)) : ProbComp Bool := do
  let context ← PqxdhCorrelatedExtractFamily.prepare baseImpl kem
    (PqxdhAuthenticatedRootExperiment.protocol env0 kem attachedVerify primitives program post)
  let initialBlock ← $ᵗ HmacBlock
  let nonce ← $ᵗ NonceOutput
  let chain ← $ᵗ RootOutput
  let key ← $ᵗ RootOutput
  @ite _ (RawCtxSendLineageCollision.InitialAlias initialBlock) (Classical.propDecidable _) (pure false)
    (compiledObserve setup env callbacks baseImpl kem attachedVerify primitives program post target context initialBlock nonce chain key)

/-- Pointwise after the prelude: outside the initial half alias, C4's compiled continuation for the first Beacon record equals the key-free suffix evaluated by the selected-key challenger from the reached cache and public log; on the alias it is `false`. -/
theorem observe_le (b : Fin (B + 1))
    (sample : Packet (M := M) (P := P) (I := I) (K := K) (A := A) (KemSK := KemSK) setup program × HmacBlock × NonceOutput × RootOutput)
    (cache : CtxRO.QueryCache) (log : List Pqxdh.Bytes) (key : RootOutput) :
    𝒟[@ite _ (RawCtxSendLineageCollision.InitialAlias sample.2.1) (Classical.propDecidable _) (pure false)
      (compiledObserve setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)
        (restoreSample setup env callbacks kem attachedVerify primitives program post sample cache).1
        sample.2.1 sample.2.2.1 sample.2.2.2 key)] {true} ≤
    𝒟[Prod.fst <$> (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder (env0).decode)
        (env0).source.crypto key) (suffix setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b) sample)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (cache, log))] {true} := by
  classical
  by_cases aliased : RawCtxSendLineageCollision.InitialAlias sample.2.1
  · rw [ite_eq_left_iff.mpr fun impossible => absurd aliased impossible]
    simp [ ]
  · rw [ite_eq_right_iff.mpr fun holds => absurd holds aliased]
    apply le_of_eq
    congr 1
    unfold compiledObserve suffix restoreSample
    rw [← PqxdhSourceSharedInput.input_cache setup env callbacks program post attachedVerify primitives baseImpl kem]
    cases pending : PqxdhSourceSharedInput.input setup env callbacks program post attachedVerify primitives baseImpl kem
        (firstBeacon b).owner (firstBeacon b).number (firstBeacon b).ancestors (firstBeacon b).disclosed sample.1 with
    | inl decision => simp [PqxdhSourceSharedInput.restore]
    | inr input =>
      have owner := input_selected setup env callbacks baseImpl kem attachedVerify primitives program post _ _ _ _ sample.1 input pending
      simp only [PqxdhSourceSharedInput.restore]
      have known : ∀ kernel, initialKernel (RawCtxSelectedInitialConstructor.response64 sample.2.1) = .ok kernel → ∀ context,
          KnownSend (productionStream (env0).source.crypto) none (PqxdhInitialSourceExperiment.root (env0).source zeroRoot
            (RawCtxSelectedInitialConstructor.response64 sample.2.1) (firstBeacon b).owner) sample.2.2.1 sample.2.2.2 kernel context :=
        fun kernel initialized context => initial_known (S := S) (env0).source sample.2.1 b sample.2.2.1 sample.2.2.2
          aliased kernel initialized context
      rw [owner] at *
      rw [run_client (known := known) (log := log)]
      rfl

/-- Sampling the selected key first: the separated compiled game is dominated by the constructed key-free client in the ordinary selected-key CTX source experiment. -/
theorem separated_le_client (b : Fin (B + 1)) :
    𝒟[separatedGame setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)] {true} ≤
    𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
      (fullClient setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b))] {true} := by
  have reorder : separatedGame setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b) =
      (do
        let result ← (simulateQ AdaptiveCtxSharedTarget.sharedImpl
          (prelude setup env callbacks baseImpl kem attachedVerify primitives program post)).run (∅, [])
        let key ← $ᵗ RootOutput
        @ite _ (RawCtxSendLineageCollision.InitialAlias result.1.2.1) (Classical.propDecidable _) (pure false)
          (compiledObserve setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)
            (restoreSample setup env callbacks kem attachedVerify primitives program post result.1 result.2.1).1
            result.1.2.1 result.1.2.2.1 result.1.2.2.2 key)) := by
    have shared := AdaptiveCtxSharedTarget.cache_schedule (prelude setup env callbacks baseImpl kem attachedVerify primitives program post) (∅, [])
    have source := prelude_source setup env callbacks baseImpl kem attachedVerify primitives program post
    rw [← shared, Functor.map_map] at source
    have regroup : separatedGame setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b) =
        (do
          let context ← PqxdhCorrelatedExtractFamily.prepare baseImpl kem
            (PqxdhAuthenticatedRootExperiment.protocol env0 kem attachedVerify primitives program post)
          let initialBlock ← $ᵗ HmacBlock
          let nonce ← $ᵗ NonceOutput
          let chain ← $ᵗ RootOutput
          pure (context, initialBlock, nonce, chain)) >>= fun sample => (do
            let key ← $ᵗ RootOutput
            @ite _ (RawCtxSendLineageCollision.InitialAlias sample.2.1) (Classical.propDecidable _) (pure false)
              (compiledObserve setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)
                sample.1 sample.2.1 sample.2.2.1 sample.2.2.2 key)) := by
      unfold separatedGame
      simp only [bind_assoc, pure_bind]
    rw [regroup, ← source, bind_map_left]
    rfl
  rw [reorder]
  refine (true_bind_mono _ _ (fun result => do
    let key ← $ᵗ RootOutput
    Prod.fst <$> (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder (env0).decode)
      (env0).source.crypto key) (suffix setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)
        result.1)).run (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource result.2)) ?_).trans (le_of_eq ?_)
  · exact fun (result : (Packet (M := M) (P := P) (I := I) (K := K) (A := A) (KemSK := KemSK) setup program × HmacBlock ×
      NonceOutput × RootOutput) × AdaptiveCtxSharedTarget.SharedState) => true_bind_mono _ _ _ fun key =>
      observe_le setup env callbacks baseImpl kem attachedVerify primitives program post b result.1 result.2.1 result.2.2 key
  have exchanged := RawCtxPrefixKeyOrder.source_game true (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
    (prelude setup env callbacks baseImpl kem attachedVerify primitives program post)
    (suffix setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b))
  have mapped := exchanged.map Prod.fst
  simp only [map_bind] at mapped
  rw [mapped.symm.evalDist_eq]
  rfl

/-- The initial half-alias game: the actual preparation and the same four draws, reporting whether the two halves of the 64-byte initializer response are equal. -/
noncomputable def aliasGame : ProbComp Bool := do
  let _ ← PqxdhCorrelatedExtractFamily.prepare baseImpl kem
    (PqxdhAuthenticatedRootExperiment.protocol env0 kem attachedVerify primitives program post)
  let initialBlock ← $ᵗ HmacBlock
  let _ ← $ᵗ NonceOutput
  let _ ← $ᵗ RootOutput
  let _ ← $ᵗ RootOutput
  pure (@decide (RawCtxSendLineageCollision.InitialAlias initialBlock) (Classical.propDecidable _))

/-- The initial half alias of one uniform 64-byte response has probability at most `2^-256`. -/
theorem alias_bound :
    𝒟[aliasGame setup env callbacks baseImpl kem attachedVerify primitives program post] {true} ≤ (1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) := by
  classical
  rw [← prEvent_eq_evalDist_singleton _ true]
  unfold aliasGame
  -- Stated over an abstract draw, used after generalizing `$ᵗ HmacBlock`: the concrete draw exceeds the recursion depth.
  have aliasStep : ∀ (block : ProbComp HmacBlock) (rest : HmacBlock → ProbComp Bool),
      (∀ b ∈ support block, ¬ RawCtxSendLineageCollision.InitialAlias b → Pr{let y ← rest b}[y = true] = 0) →
      Pr{let y ← block >>= rest}[y = true] ≤ Pr{let b ← block}[RawCtxSendLineageCollision.InitialAlias b] :=
    fun block rest h => prEvent_bind_le_prEvent_of_support block rest _ _ h
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun context _ => ?_
  have uniform := RawCtxSendLineageCollision.initial_alias_uniform
  generalize sampledBlock : ($ᵗ HmacBlock : ProbComp HmacBlock) = block at uniform ⊢
  refine (aliasStep block _ ?_).trans uniform
  intro initialBlock _ separate
  rw [OracleComp.prEvent_eq_zero_iff]
  simp [separate]

/-- C4's compiled game is dominated by the initial half-alias probability plus the separated compiled game. -/
theorem compiled_le_separated (target : Target S (B + 1)) :
    𝒟[compiledGame setup env callbacks baseImpl kem attachedVerify primitives program post target] {true} ≤
      (1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) +
        𝒟[separatedGame setup env callbacks baseImpl kem attachedVerify primitives program post target] {true} := by
  refine le_trans ?_ (add_le_add (alias_bound setup env callbacks baseImpl kem attachedVerify primitives program post) le_rfl)
  unfold compiledGame separatedGame aliasGame
  refine true_bind_le _ _ _ _ fun context => ?_
  refine true_bind_le _ _ _ _ fun initialBlock => ?_
  refine true_bind_le _ _ _ _ fun nonce => ?_
  refine true_bind_le _ _ _ _ fun chain => ?_
  refine PqxdhFirstBeaconRecordIntegrity.true_bind_le _ _ _ _ fun key => ?_
  classical
  by_cases aliased : RawCtxSendLineageCollision.InitialAlias initialBlock
  · rw [ite_eq_left_iff.mpr fun impossible => absurd aliased impossible, show (@decide (RawCtxSendLineageCollision.InitialAlias initialBlock) (Classical.propDecidable _)) = true from
      @decide_eq_true _ (Classical.propDecidable _) aliased]
    refine le_add_right ?_
    rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_pure]
    simp only [↓reduceIte]
    exact prEvent_le_one _
  · rw [ite_eq_right_iff.mpr fun holds => absurd holds aliased]
    exact le_add_self

open RawCtxSelectedAuthenticationObserver AdaptiveCtxDynamicKnownBounds AdaptiveCtxQueryBounds AdaptiveCtxReceive
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation

/-- The ordinary CTX authentication loss of the constructed first-record client: the IND$ advantage of the constructed validation reduction, the hash-guessing term, twice the sum of the INT-CTXT advantages of the constructed attempt-indexed reductions, and the raw-guessing term. -/
noncomputable def ctxLoss (target : Target S (B + 1)) (fallback : ModifiedNonceAeadForgery) (qHash qRaw : Nat) : ℝ≥0∞ :=
  ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage (env0).source.crypto
    (AdaptiveCtxPrefixValidation.validationReduction (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
      (AdaptiveCtxDynamicKnownKeys.decisionClient (env0).source.crypto
        (decision (RawCtxUniversalDecoder.decoder (env0).decode)
          (fullClient setup env callbacks baseImpl kem attachedVerify primitives program post target))) qHash)) +
  (qHash : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
  2 * ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage (env0).source.crypto
    (AdaptiveRawNonceAead.indexedReduction (baseDecoder (RawCtxUniversalDecoder.decoder (env0).decode)) fallback
      (AdaptiveCtxReceive.wrapped (RawCtxUniversalDecoder.decoder (env0).decode)
        (AdaptiveCtxDynamicKnownKeys.decisionClient (env0).source.crypto
          (decision (RawCtxUniversalDecoder.decoder (env0).decode)
            (fullClient setup env callbacks baseImpl kem attachedVerify primitives program post target)))) index) +
  (qRaw : ℝ≥0∞) / (2 ^ 512 : Nat)

/-- The CTX loss is finite. -/
theorem ctxLoss_ne_top (target : Target S (B + 1)) (fallback : ModifiedNonceAeadForgery) (qHash qRaw : Nat) :
    ctxLoss setup env callbacks baseImpl kem attachedVerify primitives program post target fallback qHash qRaw ≠ ⊤ := by
  unfold ctxLoss
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ?_⟩, ?_⟩, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.inv_ne_top.mpr (by positivity))
  · refine ENNReal.mul_ne_top (by norm_num) (ENNReal.sum_ne_top.mpr fun index _ => ?_)
    exact prEvent_ne_top _
  · exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)

/-- C4's compiled first Beacon record game is bounded by the initial half-alias term `2^-256`, the ordinary CTX authentication loss of the constructed key-free client, and the explicit gap game in which the constructed client returns `true` while the ordinary observer does not win. -/
theorem compiled_ctx_bound (b : Fin (B + 1)) (fallback : ModifiedNonceAeadForgery) (qHash qSeal qRaw : Nat)
    (hashBound : (fullClient setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)).IsQueryBoundP
      HashRoute qHash)
    (sealBound : (fullClient setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)).IsQueryBoundP
      (TargetClass SourceSeal) qSeal)
    (rawBound : (fullClient setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)).IsQueryBoundP
      (TargetClass IsRawQuery) qRaw)
    (small : qSeal < 2 ^ 96) :
    𝒟[compiledGame setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)] {true} ≤
      (1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) +
      ctxLoss setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b) fallback qHash qRaw +
      𝒟[gapGame (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
        (fullClient setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b))] {true} := by
  refine (compiled_le_separated setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)).trans ?_
  rw [add_assoc]
  refine add_le_add le_rfl ?_
  refine (separated_le_client setup env callbacks baseImpl kem attachedVerify primitives program post b).trans ?_
  refine (client_le_decision _ _ _).trans (add_le_add ?_ le_rfl)
  exact authentication_bound _ _ fallback _ qHash qSeal qRaw hashBound sealBound rawBound small

end Prepared

section Final
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity CtxRomAuth AdaptiveCtxSharedHash
open RawCtxSelectedAuthenticationObserver AdaptiveCtxDynamicKnownBounds AdaptiveCtxQueryBounds AdaptiveCtxReceive
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅

/-- The post budget of the certificate: the sum of its per-kind caps. -/
def postTotal {post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)}
    (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post0) : Nat :=
  ∑ kind, c.postBudget kind

/-- The forgery proxy post makes at most the certificate's total post budget of requests. -/
theorem forgery_total (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post0) (selection : program.Selection)
    (reply : RustM (Option PqxdhServerRegistrationPublication.Response)) :
    (forgeryPost env0 program post0 selection reply).IsTotalQueryBound
      (postTotal setup env callbacks baseImpl kem program c) :=
  (isQueryBoundP_true_iff _ _).mp ((forgery_query_bound env0 program post0 selection reply (fun _ => True) _).mpr
    ((isQueryBoundP_true_iff _ _).mpr (total_of_kinds PqxdhPhase2SourceSchedulerBounds.classify (post0 selection reply)
      c.postBudget (c.postBound selection reply))))

/-- First Beacon record integrity for the protocol-derived key of Beacon `b`'s first record in the HB-112 experiment. The left side is exactly C4's `first_beacon_forgery_le`: the actual game with the forgery proxy post minus its constant-`false` continuation. It is bounded by the first-record target loss and the completed-branch root loss (advantages of C1's constructed reductions), the ordinary CTX authentication loss `ctxLoss` of the constructed key-free client `fullClient` (IND$ advantage of the constructed validation reduction, `qHash/2^128`, twice the INT-CTXT advantages of the constructed attempt-indexed reductions, `qRaw/2^512`), the statistical initial half-alias term `2^-256`, the explicit gap game (the constructed client returns `true` while the ordinary observer does not win) and C4's explicit restricted stop game; the last two are game terms that are not yet bounded by assumption terms. The raw-opening and seal budgets are derived from the certificate's post budget `qPost` (one builder request plus one per post request); the hash budget adds the hash budget `qPrelude` of the shared-ROM preparation `PqxdhSourceSharedPreparation.prepare`, given by the resource contract `PrepareHashBudget`, which `prepare_hash_budget` discharges (as `69 * qMain + 1 + 69 * qPost`) from the caps taken by `PqxdhSourceSharedPreparationResources.prepare`. -/
theorem first_beacon_record_integrity
    (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (b : Fin (B + 1)) (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post0)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem (env0).native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect (env0).source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (ctxFallback : ModifiedNonceAeadForgery) (qPrelude : Nat)
    (prepareHash : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0)
      qPrelude)
    (small : 1 + postTotal setup env callbacks baseImpl kem program c < 2 ^ 96) :
    (𝒟[PqxdhInitialRootEventSecrecy.actual env0 baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0)
        (.beacon b) 1#u64 [] []] {true}).toReal -
      (𝒟[PqxdhInitialRootEventExperiment.actual env0 baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0)
        (PqxdhFirstRecordTarget.rejectAll env0 program)] {true}).toReal ≤
    PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (forgeryPost env0 program post0)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (forgeryPost env0 program post0)
        (certificate env0 baseImpl kem program post0 c)) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0)
      hmac fallback ordinaryFallback +
    (ctxLoss setup env callbacks baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0) (firstBeacon b)
      ctxFallback (qPrelude + (1 + postTotal setup env callbacks baseImpl kem program c))
      (1 + postTotal setup env callbacks baseImpl kem program c)).toReal +
    1 / 2 ^ 256 +
    (𝒟[gapGame (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
      (fullClient setup env callbacks baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0)
        (firstBeacon b))] {true}).toReal +
    (𝒟[stopGame setup env callbacks baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0)
      (firstBeacon b)] {true}).toReal := by
  have postBound := forgery_total setup env callbacks baseImpl kem program post0 c
  have hashBound := fullClient_uses setup env callbacks baseImpl kem attachedVerify primitives program
    (forgeryPost env0 program post0) (firstBeacon b) HashRoute
    (fun _ _ _ _ query state => external_no_hash _ _ _ _ _ query state) qPrelude
    (prelude_hash setup env callbacks baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0) qPrelude
      prepareHash) _ postBound
  have sealBound := fullClient_uses setup env callbacks baseImpl kem attachedVerify primitives program
    (forgeryPost env0 program post0) (firstBeacon b) (TargetClass SourceSeal)
    (fun _ _ _ _ query state => external_no_seal _ _ _ _ _ query state) 0 (forward_no_seal _) _ postBound
  have rawBound := fullClient_uses setup env callbacks baseImpl kem attachedVerify primitives program
    (forgeryPost env0 program post0) (firstBeacon b) (TargetClass AdaptiveCtxReceive.IsRawQuery)
    (fun _ _ _ _ query state => PqxdhSelectedInitialOwnerCompiler.external_no_open _ _ _ _ _ query state) 0 (forward_no_open _) _
      postBound
  rw [Nat.zero_add] at sealBound rawBound
  have reduced := first_beacon_forgery_le setup env callbacks baseImpl kem attachedVerify primitives program post0 b c
    compatible adapter functional hmac correct fallback ordinaryFallback
  have compiled := compiled_ctx_bound setup env callbacks baseImpl kem attachedVerify primitives program
    (forgeryPost env0 program post0) b ctxFallback _ _ _ hashBound sealBound rawBound (by omega)
  have aliasFinite : (1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top ENNReal.one_ne_top (by positivity)
  have gapFinite := PqxdhFirstRecordTarget.true_ne_top (gapGame (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
    (fullClient setup env callbacks baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0) (firstBeacon b)))
  have lossFinite := ctxLoss_ne_top setup env callbacks baseImpl kem attachedVerify primitives program
    (forgeryPost env0 program post0) (firstBeacon b) ctxFallback (qPrelude + (1 + postTotal setup env callbacks baseImpl kem program c))
    (1 + postTotal setup env callbacks baseImpl kem program c)
  have real := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨aliasFinite, lossFinite⟩, gapFinite⟩) compiled
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨aliasFinite, lossFinite⟩) gapFinite,
    ENNReal.toReal_add aliasFinite lossFinite] at real
  have half : ((1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞)).toReal = 1 / 2 ^ 256 := by
    rw [ENNReal.toReal_div, ENNReal.toReal_pow]
    norm_num
  rw [half] at real
  linarith

end Final

end BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.clean_refl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.clean_refl

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.clean_trans' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.clean_trans

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.rel_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.rel_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.rel_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.rel_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.rel_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.rel_map

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.rel_continue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.rel_continue

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.rel_ite' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.rel_ite

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.aux_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.aux_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.send_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.send_clean

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.send_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.send_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.after_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.after_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.candidate_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.candidate_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.ready_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.ready_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.build_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.build_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.initial_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.initial_known

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.clearLog_idem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.clearLog_idem

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.local_ghost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.local_ghost

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.modes_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.modes_local

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.source_ghost_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.source_ghost_step

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.erase_program' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.erase_program

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.source_ghost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.source_ghost

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.external_no_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.external_no_seal

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.external_no_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.external_no_hash

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.post_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.post_step

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.post_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.post_client

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.total_of_kinds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.total_of_kinds

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.uses_pure' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.uses_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.uses_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.uses_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.uses_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.uses_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.uses_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.uses_map

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.uses_continue' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.uses_continue

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.uses_ite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.uses_ite

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.ready_uses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.ready_uses

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.forward_no_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.forward_no_open

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.forward_no_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.forward_no_seal

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.firstClient_uses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.firstClient_uses

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.postBit_ghost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.postBit_ghost

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.run_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.run_client

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.client_le_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.client_le_decision

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.true_bind_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.true_bind_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.prelude_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.prelude_source

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.input_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.input_selected

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.prepare_hash_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.prepare_hash_budget

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.prelude_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.prelude_hash

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.input_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.input_post

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.fullClient_uses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.fullClient_uses

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.observe_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.observe_le

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.separated_le_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.separated_le_client

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.alias_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.alias_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.compiled_le_separated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.compiled_le_separated

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.ctxLoss_ne_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.ctxLoss_ne_top

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.compiled_ctx_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.compiled_ctx_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.forgery_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.forgery_total

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.first_beacon_record_integrity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCtx.first_beacon_record_integrity
