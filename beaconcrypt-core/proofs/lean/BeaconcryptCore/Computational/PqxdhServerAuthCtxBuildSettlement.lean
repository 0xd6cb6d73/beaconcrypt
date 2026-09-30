import BeaconcryptCore.Computational.PqxdhServerAuthCtxSend
import BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement
open PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhServerAuthCtxCalls (Chain Material Kernel Residual step interpret initial)
open RawCtxMaterialInterpretation
open PqxdhServerRegistrationPublication (AuxSpec Response registrationWitness)

/-- Existing concrete peers retain all cached values as ordinary known material. -/
def known (kernel : ConcreteRatchetKernel) : Kernel :=
  mapRefined RawCtxSelectedMessageKey.Slot.known (PqxdhServerAuthSendFactor.known kernel)

/-- A structural image of the all-known material embedding; it excludes no byte alias. -/
def Settled (kernel : Kernel) : Prop :=
  ∃ original : RawCtxSelectedChain.Kernel, kernel = mapRefined RawCtxSelectedMessageKey.Slot.known original

/-- Full native interpretation still uses the same chain resolver as the checked Server factor. -/
def native (key : RootOutput) (kernel : Kernel) : ConcreteRatchetKernel :=
  PqxdhServerAuthSendFactor.resolve (interpret key kernel)

/-- A fixed dummy interpretation is used only after the actual source path proves every material slot known. -/
def resolve : Kernel → ConcreteRatchetKernel := native ⟨List.replicate 32 0, by simp⟩

theorem native_known (key : RootOutput) (kernel : ConcreteRatchetKernel) :
    native key (known kernel) = kernel := by
  rw [native, known, interpret, RawCtxSelectedMessageKey.known_kernel]
  rfl

theorem settled_native (key : RootOutput) (kernel : Kernel) (settled : Settled kernel) :
    native key kernel = resolve kernel := by
  obtain ⟨original, rfl⟩ := settled
  exact (congrArg PqxdhServerAuthSendFactor.resolve
    (RawCtxSelectedMessageKey.known_kernel key original)).trans
      (congrArg PqxdhServerAuthSendFactor.resolve
        (RawCtxSelectedMessageKey.known_kernel ⟨List.replicate 32 0, by simp⟩ original)).symm



section States
variable {Metadata PeerMetadata Consumed : Type}

def embed (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed :=
  ⟨⟨state.server.identity, fun kid => (state.server.peers kid).map
      (fun peer => ⟨peer.identity, known peer.kernel, peer.metadata⟩), state.server.metadata⟩,
    state.identityKeyId, state.control, state.consumed⟩

theorem native_embed (key : RootOutput)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    PqxdhInitialGenericPublication.native (native key) (embed state) = state := by
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
  exact ⟨_, rfl⟩

theorem native_settled (key : RootOutput)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (settled : StateSettled state) :
    PqxdhInitialGenericPublication.native (native key) state =
      PqxdhInitialGenericPublication.native resolve state := by
  rcases state with ⟨⟨identity, peers, metadata⟩, identityKeyId, control, consumed⟩
  simp only [PqxdhInitialGenericPublication.native, RawCtxGenericRoleStorage.nativeServer]
  congr
  funext kid
  cases found : peers kid with
  | none => rfl
  | some peer =>
      simp only [Option.map_some]
      rw [settled_native key peer.kernel (settled kid peer found)]

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


/-- Source send advancement leaves every original receive-material slot untouched. -/
theorem settled_ready (pending : RawCtxChainSend.Kdf Chain Chain Material RawCtxSourceSend.SealContext)
    (reply : Chain × Material) (settled : Settled pending.entry) :
    Settled (RawCtxChainSend.ready pending reply).advanced := by
  obtain ⟨original, same⟩ := settled
  refine ⟨{ original with control := pending.committed_control, send_chain := reply.1 }, ?_⟩
  simp only [RawCtxChainSend.ready, same, mapRefined]

/-- Literal source initialization creates only empty material slots, independently of every selected message key. -/
theorem initial_known (beacon : Bool) (other : RootOutput) :
    initial beacon other = mapRefined RawCtxSelectedMessageKey.Slot.known <$>
      RawCtxSelectedInitialConstructor.initial beacon other :=
  from_counters_map RawCtxSelectedMessageKey.Slot.known
    (RawCtxSelectedInitialConstructor.sendSlot beacon other)
    (RawCtxSelectedInitialConstructor.receiveSlot beacon other) 0#u64 0#u64

/-- The actual initial Server kernel is a known-material image before its first send. -/
theorem initial_ok (other : RootOutput) :
    ∃ kernel, initial false other = ok kernel ∧ Settled kernel := by
  obtain ⟨original, built, _⟩ := PqxdhServerAuthSendFactor.initial_ok other
  rw [initial_known, built]
  exact ⟨_, rfl, ⟨original, rfl⟩⟩


section Send
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Concrete source chain steps and the complete sealing callback, in the caller's original monad. -/
noncomputable def labels (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (sealer : PqxdhServerAuthCtxSend.Pending → m (Option RawCtxSourceSend.Encrypted)) :
    QueryImpl (RawCtxChainSend.SendSpec Chain Chain Material RawCtxSourceSend.SealContext
      RawCtxSourceSend.Encrypted) m
  | .inl chain => pure (step source rest chain)
  | .inr pending => sealer pending

/-- Only the actual send callback is used by the Server builder; the receive callback remains arbitrary and uninspected. -/
noncomputable def calls (receiveCall : Kernel → Std.U64 → RawCtxWholeOwner.OpenContext →
    m (Kernel × core.option.Option RawCtxWholeOwner.Decrypted))
    (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (sealer : PqxdhServerAuthCtxSend.Pending → m (Option RawCtxSourceSend.Encrypted)) :
    RawCtxChainOwner.Calls Kernel m :=
  { receive := receiveCall
    send := fun entry context => simulateQ (labels source rest sealer) (RawCtxChainSend.execute entry context) }

/-- Exhaustion returns the old state; otherwise the exact advanced state retains only known cached material. All sealer effects and optional writer outcomes remain in the original monad. -/
theorem send_shape (receiveCall : Kernel → Std.U64 → RawCtxWholeOwner.OpenContext →
    m (Kernel × core.option.Option RawCtxWholeOwner.Decrypted))
    (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (sealer : PqxdhServerAuthCtxSend.Pending → m (Option RawCtxSourceSend.Encrypted))
    (entry : Kernel) (settled : Settled entry) (context : RawCtxSourceSend.SealContext) :
    (calls receiveCall source rest sealer).send entry context = pure (entry, none) ∨
      ∃ (advanced : Kernel) (sealing : m (Option RawCtxSourceSend.Encrypted)),
        Settled advanced ∧ (calls receiveCall source rest sealer).send entry context =
          (fun sealed => (advanced, sealed)) <$> sealing := by
  rcases PqxdhServerAuthSendFactor.send_begin entry context with
    ⟨other, begun⟩ | ⟨pending, begun, entryEq, _⟩
  · left
    simp only [calls, RawCtxChainSend.execute, begun, RawCtxChainSend.program, simulateQ_pure]
  · right
    refine ⟨(RawCtxChainSend.ready pending (step source rest pending.request)).advanced,
      sealer (RawCtxChainSend.ready pending (step source rest pending.request)),
      settled_ready _ _ (entryEq.symm ▸ settled), ?_⟩
    simp only [calls, RawCtxChainSend.execute, begun, RawCtxChainSend.program,
      simulateQ_bind, simulateQ_spec_query, simulateQ_map, labels, pure_bind, bind_pure_comp]

end Send

/-- Pointwise equality on structural known-material images extends to the complete peer map without changing any metadata. -/
theorem state_agree {Metadata PeerMetadata Consumed : Type}
    (left right : Kernel → ConcreteRatchetKernel)
    (agree : ∀ kernel, Settled kernel → left kernel = right kernel)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (settled : StateSettled state) :
    PqxdhInitialGenericPublication.native left state = PqxdhInitialGenericPublication.native right state := by
  rcases state with ⟨⟨identity, peers, metadata⟩, identityKeyId, control, consumed⟩
  simp only [PqxdhInitialGenericPublication.native, RawCtxGenericRoleStorage.nativeServer]
  congr
  funext kid
  cases found : peers kid with
  | none => rfl
  | some peer =>
      simp only [Option.map_some]
      rw [agree peer.kernel (settled kid peer found)]

section Settle
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable {Metadata PeerMetadata Consumed : Type}
variable (receiveCall : Kernel → Std.U64 → RawCtxWholeOwner.OpenContext →
    m (Kernel × core.option.Option RawCtxWholeOwner.Decrypted))
    (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (sealer : PqxdhServerAuthCtxSend.Pending → m (Option RawCtxSourceSend.Encrypted))
    (aux : QueryImpl AuxSpec m) (left right : Kernel → ConcreteRatchetKernel)
    (agree : ∀ kernel, Settled kernel → left kernel = right kernel)
include agree

theorem settle_after (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (entry : Kernel) (materialKnown : Settled entry) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (settled : StateSettled state) :
    Prod.map id (PqxdhInitialGenericPublication.native left) <$>
      PqxdhInitialGenericPublication.afterInitialization (calls receiveCall source rest sealer) aux
        candidate authenticated entry metadata state =
    Prod.map id (PqxdhInitialGenericPublication.native right) <$>
      PqxdhInitialGenericPublication.afterInitialization (calls receiveCall source rest sealer) aux
        candidate authenticated entry metadata state := by
  have base := state_agree left right agree state settled
  simp only [PqxdhInitialGenericPublication.afterInitialization]
  rcases send_shape receiveCall source rest sealer entry materialKnown (PqxdhServerRegistrationPublication.firstContext candidate authenticated)
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
              state_agree left right agree _ (publish_settled state settled candidate advanced fresh metadata)]

theorem settle_candidate_kernel (kernel : Kernel) (materialKnown : Settled kernel) (candidate : pqxdh.ServerRegistrationCandidate)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (settled : StateSettled state) :
    Functor.map (Prod.map id (PqxdhInitialGenericPublication.native left)) <$>
      PqxdhInitialGenericBuilder.candidate (calls receiveCall source rest sealer) aux
        (ok kernel) candidate data metadata state =
    Functor.map (Prod.map id (PqxdhInitialGenericPublication.native right)) <$>
      PqxdhInitialGenericBuilder.candidate (calls receiveCall source rest sealer) aux
        (ok kernel) candidate data metadata state := by
  have base := state_agree left right agree state settled
  simp only [PqxdhInitialGenericBuilder.candidate, PqxdhInitialGenericBuilder.continueRust, map_bind]
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
            | fail error => simp only [map_pure]; rfl
            | div => simp only [map_pure]; rfl
            | ok binding =>
                simp only [Functor.map_map]
                have after := settle_after receiveCall source rest sealer aux left right agree candidate
                  (absBytes binding.bytes ++ data.getD registrationWitness) kernel materialKnown metadata state settled
                have lifted := congrArg (fun work => RustM.ok <$> work) after
                simpa only [Functor.map_map, Function.comp_def, RawCtxMaterialInterpretation.rust_map_ok] using lifted
        · simp only [fits, ite_false, map_pure, RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq, base]

theorem settle_candidate (otherChain : RootOutput) (candidate : pqxdh.ServerRegistrationCandidate)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (settled : StateSettled state) :
    Functor.map (Prod.map id (PqxdhInitialGenericPublication.native left)) <$>
      PqxdhInitialGenericBuilder.candidate (calls receiveCall source rest sealer) aux
        (initial false otherChain) candidate data metadata state =
    Functor.map (Prod.map id (PqxdhInitialGenericPublication.native right)) <$>
      PqxdhInitialGenericBuilder.candidate (calls receiveCall source rest sealer) aux
        (initial false otherChain) candidate data metadata state := by
  obtain ⟨kernel, built, materialKnown⟩ := initial_ok otherChain
  rw [built]
  exact settle_candidate_kernel receiveCall source rest sealer aux left right agree kernel materialKnown candidate data metadata state settled

theorem settle_generic (otherChain : RootOutput) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (settled : StateSettled state) :
    Functor.map (Prod.map id (PqxdhInitialGenericPublication.native left)) <$>
      PqxdhServerAuthSendFactor.genericBuild (calls receiveCall source rest sealer) aux
        (initial false otherChain) pending data metadata state =
    Functor.map (Prod.map id (PqxdhInitialGenericPublication.native right)) <$>
      PqxdhServerAuthSendFactor.genericBuild (calls receiveCall source rest sealer) aux
        (initial false otherChain) pending data metadata state := by
  have base := state_agree left right agree state settled
  unfold PqxdhServerAuthSendFactor.genericBuild
  cases next : pqxdh.server_next_key_id state.control with
  | fail error => simp only [PqxdhInitialGenericBuilder.continueRust, map_pure]; rfl
  | div => simp only [PqxdhInitialGenericBuilder.continueRust, map_pure]; rfl
  | ok result =>
      cases result with
      | Err error =>
          simp only [PqxdhInitialGenericBuilder.continueRust, map_pure,
            RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq, base]
      | Ok keyId =>
          simp only [PqxdhInitialGenericBuilder.continueRust]
          cases prepared : pqxdh.server_prepare_commit state.control pending ⟨state.server.identity, state.identityKeyId⟩
            (if (state.server.peers keyId).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
          | fail error => simp only [map_pure]; rfl
          | div => simp only [map_pure]; rfl
          | ok value => cases value with
            | Err error =>
                simp only [map_pure, RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq, base]
            | Ok value =>
                exact settle_candidate receiveCall source rest sealer aux left right agree otherChain value data metadata state settled

end Settle


/-- The complete concrete initial Server builder removes the selected material interpretation from every final peer kernel. Its actual initializer and existing peers discharge all structural premises; sealing, erasure, writer and publication effects remain unchanged. -/
theorem build_settled {m : Type → Type} [Monad m] [LawfulMonad m]
    {Metadata PeerMetadata Consumed : Type}
    (receiveCall : Kernel → Std.U64 → RawCtxWholeOwner.OpenContext →
      m (Kernel × core.option.Option RawCtxWholeOwner.Decrypted))
    (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (sealer : PqxdhServerAuthCtxSend.Pending → m (Option RawCtxSourceSend.Encrypted))
    (aux : QueryImpl AuxSpec m) (key other : RootOutput) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    Functor.map (Prod.map id (PqxdhInitialGenericPublication.native (native key))) <$>
      PqxdhServerAuthSendFactor.genericBuild (calls receiveCall source rest sealer) aux
        (initial false other) pending data metadata (embed state) =
    Functor.map (Prod.map id (PqxdhInitialGenericPublication.native resolve)) <$>
      PqxdhServerAuthSendFactor.genericBuild (calls receiveCall source rest sealer) aux
        (initial false other) pending data metadata (embed state) :=
  settle_generic receiveCall source rest sealer aux (native key) resolve (settled_native key)
    other pending data metadata (embed state) (embed_settled state)

/-- The sealer abstraction is instantiated by the literal source callback, retaining its complete shared cache and optional writer result. -/
theorem source_send {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (key : RootOutput) (rest : Residual)
    (receiveCall : Kernel → Std.U64 → RawCtxWholeOwner.OpenContext →
      StateT (RawCtxSharedPrimitive.SharedState A) ProbComp
        (Kernel × core.option.Option RawCtxWholeOwner.Decrypted))
    (entry : Kernel) (context : RawCtxSourceSend.SealContext) :
    (calls receiveCall source rest (PqxdhServerAuthCtxSend.sourceSealing source writer key)).send entry context =
      simulateQ (PqxdhServerAuthCtxSend.sourceHandler source writer key rest)
        (RawCtxChainSend.execute entry context) := rfl

/-- The executable sealer is the literal ordinary CTX callback in OptionT, so repeated-nonce refusal remains an outer stop rather than becoming optional writer failure. No selected key is an argument. -/
theorem compiled_send (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (rest : Residual)
    (receiveCall : Kernel → Std.U64 → RawCtxWholeOwner.OpenContext →
      OptionT (OracleComp AdaptiveCtxDynamicKnownKeys.Spec)
        (Kernel × core.option.Option RawCtxWholeOwner.Decrypted))
    (entry : Kernel) (context : RawCtxSourceSend.SealContext) :
    ((calls receiveCall source rest (fun pending => OptionT.mk
      (RawCtxSelectedSealConsumer.sealing source.crypto writer (PqxdhServerAuthCtxSend.sealing pending)))).send
        entry context).run = PqxdhServerAuthCtxSend.send source writer rest entry context := rfl

end BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.native_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.native_known
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.settled_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.settled_native
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.native_embed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.native_embed
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.embed_settled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.embed_settled
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.native_settled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.native_settled
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.publish_settled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.publish_settled
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.settled_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.settled_ready
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.initial_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.initial_known
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.initial_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.initial_ok
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.send_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.send_shape
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.state_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.state_agree
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.settle_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.settle_after
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.settle_candidate_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.settle_candidate_kernel
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.settle_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.settle_candidate
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.settle_generic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.settle_generic
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.build_settled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.build_settled
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.source_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.source_send
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.compiled_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement.compiled_send
