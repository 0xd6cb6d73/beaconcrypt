import BeaconcryptCore.Computational.RawCtxChainInitialization
import BeaconcryptCore.Computational.RawCtxChainOpeningArguments

/-!
A private selected slot contains either an unavailable chain marker or a known native chain. The selected full76 reply is reused for every unavailable request, including both directions and rollback/retry. Known inputs keep actual fixed-source HKDF evaluation. Actual material, counters, slots and context remain native. The opening and sealing adapters omit only chain fields proved unread by their source getters.

In the real branch, arbitrary live slot states map to the entire original source owner and primitive state through every adaptive optional reply. Rebasing may hide all byte-equal live chains; distinct slot syntax never proves different bytes. The interpreter functions take no target input or recursive root interpretation. Fixed-source KDF is pure only under the existing functional/native contract; deterministic evaluations and source work are not free.

This is the selected real-source factor, not yet an everywhere-consistent random input table. A known chain may equal the selected input, including a newly returned next chain; random-mode reconciliation requires its explicit candidate/exposure event. Public services, current-chain/skipped-key disclosures, permitted earlier root/identity/KEM knowledge and the native reached cut remain to be composed. Snapshot, persistence and restoration services are excluded from this proof task.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedChain
open RawCtxChainInterpretation RawCtxMaterialInterpretation

/-- A private live-chain slot; `hidden` carries no target bytes. -/
inductive Slot where
  | hidden
  | known : RatchetChain → Slot

def interpret (target : RatchetChain) : Slot → RatchetChain
  | .hidden => target
  | .known chain => chain

noncomputable def hide (target chain : RatchetChain) : Slot :=
  @ite Slot (chain = target) (Classical.propDecidable _) .hidden (.known chain)

abbrev Kernel := RefinedRatchet Slot Slot RatchetMaterial

def nativeKernel (target : RatchetChain) (entry : Kernel) : ConcreteRatchetKernel :=
  ⟨mapChains (interpret target) (interpret target) entry⟩

noncomputable def rebase (target : RatchetChain) (entry : ConcreteRatchetKernel) : Kernel :=
  mapChains (hide target) (hide target) entry.refined

/-- The selected full response is reused on every hidden input; public known-input work stays actual. -/
noncomputable def step (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (challenge : RatchetKdfResponse) (slot : Slot) : Slot × RatchetMaterial :=
  let decoded := RawCtxInterpretedReceive.decodeResponse (match slot with
    | .hidden => challenge
    | .known chain => RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest chain))
  (.known decoded.1, decoded.2)

/-- In the real world all source bytes and complete material projections are retained, including aliases. -/
theorem step_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (target : RatchetChain) (slot : Slot) :
    RawCtxInterpretedReceive.decodeResponse
      (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest (interpret target slot))) =
      Prod.map (interpret target) id
        (step source (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target)) slot) := by
  cases slot <;> rfl

/-- All equal live byte values are hidden, not just one syntactic owner handle. -/
theorem interpret_hide (target chain : RatchetChain) : interpret target (hide target chain) = chain := by
  unfold hide
  split <;> simp_all only [interpret]

/-- Rebasing retains both live chains, every slot, all sequence/control fields and the full native kernel. -/
theorem native_rebase (target : RatchetChain) (entry : ConcreteRatchetKernel) :
    nativeKernel target (rebase target entry) = entry := by
  simp only [nativeKernel, rebase, mapChains, interpret_hide]

/-- Used only to fill source fields which no primitive callback reads. -/
def unusedChain : RatchetChain := ⟨⟨List.replicate 32 0#u8, by simp⟩⟩

noncomputable def receiveLabels {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) :
    QueryImpl (RawCtxChainReceive.ReceiveSpec Slot Slot RatchetMaterial
      RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted)
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl slot => pure (step source challenge slot)
  | .inr pending => RawCtxSourceChainHandles.receiveNative source writer
      (.inr (RawCtxInterpretedOpening.toNative
        (mapOpeningChains (fun _ => unusedChain) (fun _ => unusedChain) pending)))

noncomputable def sendLabels {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) :
    QueryImpl (RawCtxChainSend.SendSpec Slot Slot RatchetMaterial
      RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted)
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl slot => pure (step source challenge slot)
  | .inr pending => RawCtxSourceChainHandles.sendNative source writer
      (.inr (RawCtxInterpretedSend.nativeSeal
        (RawCtxChainSend.nativeSeal (fun _ => unusedChain) (fun _ => unusedChain) pending)))

/-- The fixed native KDF has no primitive-state effect; only its actual complete response is replaced by its equal decoded slot. -/
theorem receive_kdf {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (target : RatchetChain) (slot : Slot) :
    RawCtxInterpretedReceive.decodeResponse <$>
      RawCtxSourceChainHandles.receiveNative (Auxiliary := Auxiliary) source writer
        (.inl (RawCtxChainSend.nativeRequest (interpret target slot))) =
      (fun reply => (interpret target reply.1, reply.2)) <$>
        receiveLabels source writer
          (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target)) (.inl slot) := by
  simp only [receiveLabels, RawCtxSourceChainHandles.receiveNative, QueryImpl.compose, RawCtxWholeOwner.adapter,
    RawCtxMixedOwner.receiveAdapter, OracleSpec.query, simulateQ_query]
  simp [RawCtxSourceMaterialLabels.nativeImpl, RawCtxMixedShared.sharedImpl,
    QueryImpl.compose, RawCtxMixedShared.sharedAdapter, RawCtxSourceOpen.nativeAdapter,
    RawCtxMixedOwner.receiveLift, OracleSpec.query]
  change RawCtxInterpretedReceive.decodeResponse <$>
    (pure (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest (interpret target slot))) :
      StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp RatchetKdfResponse) = _
  simp only [map_pure, step_source, Prod.map_def, id_eq]

/-- Source send and receive retain one common native KDF branch. -/
theorem send_kdf {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (target : RatchetChain) (slot : Slot) :
    RawCtxInterpretedReceive.decodeResponse <$>
      RawCtxSourceChainHandles.sendNative (Auxiliary := Auxiliary) source writer
        (.inl (RawCtxChainSend.nativeRequest (interpret target slot))) =
      (fun reply => (interpret target reply.1, reply.2)) <$>
        sendLabels source writer
          (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target)) (.inl slot) :=
  receive_kdf source writer target slot

/-- Sealing reads material, sequence and context; omitted chain bytes are never passed to its actual primitive. -/
theorem send_seal {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (target : RatchetChain) (challenge : RatchetKdfResponse)
    (pending : RawCtxChainSend.Seal Slot Slot RatchetMaterial RawCtxSourceSend.SealContext) :
    RawCtxSourceChainHandles.sendNative (Auxiliary := Auxiliary) source writer
      (.inr (RawCtxInterpretedSend.nativeSeal
        (RawCtxChainSend.nativeSeal (interpret target) (interpret target) pending))) =
      sendLabels source writer challenge (.inr pending) := rfl

/-- Complete native send continues from the rebased state with no target bytes in the selected interpreter. -/
theorem send_source {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (target : RatchetChain) (entry : Kernel) (context : RawCtxSourceSend.SealContext) :
    simulateQ (RawCtxSourceChainHandles.sendNative (Auxiliary := Auxiliary) source writer)
      (RawCtxSourceSend.send (nativeKernel target entry) context) =
      (fun result => (nativeKernel target result.1, result.2)) <$>
        simulateQ (sendLabels source writer
          (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target)))
          (RawCtxChainSend.execute entry context) := by
  rw [nativeKernel, RawCtxInterpretedSend.send_native, simulateQ_map, ← QueryImpl.simulateQ_compose]
  have mapped := RawCtxChainSend.execute_native (interpret target) (interpret target)
    (sendLabels source writer (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target)))
    (RawCtxSourceChainHandles.sendNative (Auxiliary := Auxiliary) source writer ∘ₛ RawCtxInterpretedSend.nativeAdapter)
    ?_ ?_ entry context
  · rw [mapped, Functor.map_map]
    rfl
  · exact fun request => (simulateQ_map (RawCtxSourceChainHandles.sendNative source writer)
      ((RawCtxSourceSend.SendSpec RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted).query
        (.inl (RawCtxChainSend.nativeRequest (interpret target request))))
      RawCtxInterpretedReceive.decodeResponse).trans
        ((congrArg (fun work => RawCtxInterpretedReceive.decodeResponse <$> work)
          (simulateQ_spec_query (RawCtxSourceChainHandles.sendNative source writer)
            (.inl (RawCtxChainSend.nativeRequest (interpret target request))))).trans
              (send_kdf source writer target request))
  · exact fun pending => (simulateQ_spec_query (RawCtxSourceChainHandles.sendNative source writer) _).trans
      (send_seal source writer target _ pending)

/-- Source opening omits only chain fields that its actual selected getters never read. -/
theorem receive_open {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (target : RatchetChain) (challenge : RatchetKdfResponse)
    (pending : RawCtxInterpretedOpening.Opening Slot Slot RatchetMaterial RawCtxWholeOwner.OpenContext) :
    RawCtxSourceChainHandles.receiveNative (Auxiliary := Auxiliary) source writer
      (.inr (RawCtxInterpretedOpening.toNative
        (mapOpeningChains (interpret target) (interpret target) pending))) =
      receiveLabels source writer challenge (.inr pending) :=
  RawCtxChainOpeningArguments.native_chains source writer
    (interpret target) (fun _ => unusedChain) (interpret target) (fun _ => unusedChain) pending

/-- Every skipped derivation, optional failure and rollback retains the complete source receive under the same selected response. -/
theorem receive_source {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (target : RatchetChain) (entry : Kernel) (requested : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    simulateQ (RawCtxSourceChainHandles.receiveNative (Auxiliary := Auxiliary) source writer)
      (RawCtxOwnerOracle.receive (nativeKernel target entry) requested context) =
      (fun result => (nativeKernel target result.1, result.2)) <$>
        simulateQ (receiveLabels source writer
          (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target)))
          (RawCtxChainReceive.execute entry requested context) := by
  rw [nativeKernel, RawCtxInterpretedReceive.receive_native, simulateQ_map, ← QueryImpl.simulateQ_compose]
  have mapped := RawCtxChainReceive.execute_native (interpret target) (interpret target)
    (receiveLabels source writer (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target)))
    (RawCtxSourceChainHandles.receiveNative (Auxiliary := Auxiliary) source writer ∘ₛ RawCtxInterpretedReceive.nativeAdapter)
    ?_ ?_ entry requested context
  · simpa only [Functor.map_map, nativeKernel] using congrArg
      (fun work => (fun result => (ConcreteRatchetKernel.mk result.1, result.2)) <$> work) mapped
  · exact fun request => (simulateQ_map (RawCtxSourceChainHandles.receiveNative source writer)
      ((RawCtxOwnerOracle.ReceiveSpec RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted).query
        (.inl (RawCtxChainSend.nativeRequest (interpret target request))))
      RawCtxInterpretedReceive.decodeResponse).trans
        ((congrArg (fun work => RawCtxInterpretedReceive.decodeResponse <$> work)
          (simulateQ_spec_query (RawCtxSourceChainHandles.receiveNative source writer)
            (.inl (RawCtxChainSend.nativeRequest (interpret target request))))).trans
              (receive_kdf source writer target request))
  · exact fun pending => (simulateQ_spec_query (RawCtxSourceChainHandles.receiveNative source writer) _).trans
      (receive_open source writer target _ pending)

noncomputable def calls {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) :
    RawCtxChainOwner.Calls Kernel (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  { receive := fun entry requested context =>
      simulateQ (receiveLabels source writer challenge) (RawCtxChainReceive.execute entry requested context)
    send := fun entry context =>
      simulateQ (sendLabels source writer challenge) (RawCtxChainSend.execute entry context) }

/-- The same hidden response serves both directions and every adaptive retry while the complete owner and shared primitive state remain related. -/
theorem source_schedule {Auxiliary Metadata Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (target : RatchetChain) (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (state : RawCtxChainOwner.State Kernel Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (RawCtxMixedOwner.sourceImpl (RawCtxSourceMaterialLabels.nativeImpl source writer) senderId decode) client).run
      (RawCtxChainOwner.nativeState (nativeKernel target) state.1, state.2) =
      Prod.map id (Prod.map (RawCtxChainOwner.nativeState (nativeKernel target)) id) <$>
        (simulateQ (RawCtxChainOwner.sourceImpl
          (calls source writer (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target)))
          senderId decode) client).run state :=
  RawCtxChainOwner.source_schedule (nativeKernel target)
    (calls source writer (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target)))
    (RawCtxSourceMaterialLabels.nativeImpl source writer)
    (receive_source source writer target) (send_source source writer target) senderId decode client state

end BeaconcryptCore.Computational.RawCtxSelectedChain

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChain.step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChain.step_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChain.interpret_hide' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChain.interpret_hide

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChain.native_rebase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChain.native_rebase

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChain.receive_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChain.receive_kdf

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChain.send_kdf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChain.send_kdf

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChain.send_seal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChain.send_seal

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChain.send_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChain.send_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChain.receive_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChain.receive_open

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChain.receive_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChain.receive_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChain.source_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChain.source_schedule
