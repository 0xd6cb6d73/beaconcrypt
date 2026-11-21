import BeaconcryptCore.Computational.RawCtxInterpretedSend

/-!
These source getter and primitive adapters carry arbitrary private material labels through the complete existing receive and send drivers. The actual prepared-slot lookup retains absent or mistagged material, sequence and original context; native specialization identifies the existing getter normalizers. Distinct labels may denote the same material. Opening and sealing preserve the original optional primitive reply and API metadata wrapping before source publication.

The higher capability-handler equations are derived from explicit equations for the selected primitive input and the decoded native KDF response. These are operational realization obligations in an arbitrary lawful monad, not cryptographic assumptions. The native KDF still returns its actual full typed response before decoding. Full stateful corollaries retain every primitive poststate and optional result, and every selective underlying query budget is unchanged.

The interpretation is a fixed function for this comparison. No inverse material lookup, independent key table, fixed KDF law, nonce freshness, callback correctness or honest-state premise is introduced. A concrete label/challenger backend must still realize the low-level primitive equations. Source getters, response conversion, label interpretation, local cryptographic work and API wrapping remain computation; oracle budgets do not prove native timing, allocation or library equality. Whole-owner/raw/mixed compilation, actual label generation, evolving-key and reveal/restore policies, and global security remain separate. Inputs, labels, source state and contexts are private interpreter data, not additions to network, reveal, snapshot or persistence interfaces.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
open OracleComp OracleSpec

namespace BeaconcryptCore.Computational.RawCtxInterpretedArguments

open RawCtxMaterialInterpretation
open RawCtxInterpretedOpening hiding sequence

structure Input (Material Context : Type) where
  material : Material
  sequence : Std.U64
  context : Context

def mapInput {Material Value Context : Type} (interpret : Material → Value) (input : Input Material Context) :
    Input Value Context := ⟨interpret input.material, input.sequence, input.context⟩

/-- The selected source sequence getter is total for every represented opening. -/
theorem sequence_total {Material Context : Type} (pending : Opening RatchetChain RatchetChain Material Context) :
    ∃ result, RawCtxInterpretedOpening.sequence pending = ok result := by
  cases hprepared : pending.prepared <;> simp [RawCtxInterpretedOpening.sequence, hprepared]

/-- The actual prepared-slot getter is total, retaining absent and mistagged material. -/
theorem material_total {Material Context : Type} (pending : Opening RatchetChain RatchetChain Material Context) :
    ∃ result, material pending = ok result := by
  cases hprepared : pending.prepared <;>
    simp only [material, hprepared, lift, control.capacity_eq_ok, bind_tc_ok]
  case PreparedReceiveCachedCase prepared =>
    split
    · exact ⟨_, rfl⟩
    · rw [control.array_index_eq_ok _ _ (by scalar_tac)]
      simp only [bind_tc_ok, core.option.Option.as_ref]
      split <;> simp_all only [bind_tc_ok]
      all_goals first | exact ⟨_, rfl⟩ | split <;> exact ⟨_, rfl⟩
  case PreparedReceiveFutureCase future => exact ⟨_, rfl⟩

noncomputable def openArguments {Material Context : Type}
    (pending : Opening RatchetChain RatchetChain Material Context) : Option (Input Material Context) :=
  match (material_total pending).choose with
  | .None => none
  | .Some selected => some ⟨selected, (sequence_total pending).choose, pending.context⟩

/-- Exact selected arguments commute with an arbitrary material interpretation. -/
theorem openArguments_map {Material Value Context : Type} (interpret : Material → Value)
    (pending : Opening RatchetChain RatchetChain Material Context) :
    openArguments (mapOpening interpret pending) = (openArguments pending).map (mapInput interpret) := by
  have hm : (material_total (mapOpening interpret pending)).choose =
      mapOption interpret (material_total pending).choose := by
    apply RustM.ok.inj
    exact (material_total (mapOpening interpret pending)).choose_spec.symm.trans
      ((material_map interpret pending).trans (by
        simpa only [rust_map_ok] using congrArg (fun result => mapOption interpret <$> result)
          (material_total pending).choose_spec))
  have hs : (sequence_total (mapOpening interpret pending)).choose = (sequence_total pending).choose := by
    apply RustM.ok.inj
    exact (sequence_total (mapOpening interpret pending)).choose_spec.symm.trans
      ((sequence_map interpret pending).trans (sequence_total pending).choose_spec)
  simp only [openArguments, hm, hs]
  cases (material_total pending).choose <;> rfl

def toOpenInput (input : Input RatchetMaterial RawCtxWholeOwner.OpenContext) : RawCtxWholeOwner.OpenInput :=
  ⟨input.material, input.sequence, input.context⟩

def toSealInput (input : Input RatchetMaterial RawCtxSourceSend.SealContext) : RawCtxSourceSend.SealInput :=
  ⟨input.material, input.sequence, input.context⟩

/-- The generic normalizer gives exactly the native getter arguments, including missing material. -/
theorem openArguments_native (pending : Opening RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext) :
    RawCtxWholeOwner.arguments (toNative pending) = (openArguments pending).map toOpenInput := by
  have hm : ((toNative pending).material_total).choose = (material_total pending).choose := by
    apply RustM.ok.inj
    exact (toNative pending).material_total.choose_spec.symm.trans
      ((native_material pending).trans (material_total pending).choose_spec)
  have hs : ((toNative pending).sequence_total).choose = (sequence_total pending).choose := by
    apply RustM.ok.inj
    exact (toNative pending).sequence_total.choose_spec.symm.trans
      ((native_sequence pending).trans (sequence_total pending).choose_spec)
  simp only [RawCtxWholeOwner.arguments, openArguments, hm, hs]
  cases (material_total pending).choose <;> rfl

abbrev OpenSpec (Material : Type) :=
  (SymmetricRatchetKdfRequest →ₒ (RatchetChain × Material)) +
    (Input Material RawCtxWholeOwner.OpenContext →ₒ core.option.Option Pqxdh.Bytes)

def decrypted {Material : Type} (input : Input Material RawCtxWholeOwner.OpenContext)
    (plaintext : Pqxdh.Bytes) : RawCtxWholeOwner.Decrypted :=
  ⟨plaintext, input.context.frame.sender, input.sequence⟩

noncomputable def openAdapter {Material : Type} :
    QueryImpl (RawCtxInterpretedReceive.ReceiveSpec Material RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted)
      (OracleComp (OpenSpec Material))
  | .inl request => liftM ((OpenSpec Material).query (.inl request))
  | .inr pending =>
    match openArguments pending with
    | none => pure .None
    | some input => do
      let reply ← (OpenSpec Material).query (.inr input)
      pure (RawCtxOwnerResult.mapReply (decrypted input) reply)

/-- Selected primitive equality discharges the full source opening adapter equation. -/
theorem openAdapter_interpreted {Material : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Material → RatchetMaterial)
    (native : QueryImpl RawCtxWholeOwner.PrimitiveSpec m) (labels : QueryImpl (OpenSpec Material) m)
    (opening : ∀ input, native (.inr (toOpenInput (mapInput interpret input))) = labels (.inr input))
    (pending : Opening RatchetChain RatchetChain Material RawCtxWholeOwner.OpenContext) :
    simulateQ native (RawCtxWholeOwner.adapter (.inr (toNative (mapOpening interpret pending)))) =
      simulateQ labels (openAdapter (.inr pending)) := by
  simp only [RawCtxWholeOwner.adapter, openArguments_native, openArguments_map, Option.map_map, openAdapter]
  cases h : openArguments pending with
  | none => simp
  | some input =>
    simp only [Option.map_some, Function.comp_apply, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
    rw [opening input]
    rfl

/-- Complete native receive interpretation follows from primitive-input and decoded-KDF equations. -/
theorem receive_interpreted {Material : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Material → RatchetMaterial)
    (native : QueryImpl RawCtxWholeOwner.PrimitiveSpec m) (labels : QueryImpl (OpenSpec Material) m)
    (kdf : ∀ request, RawCtxInterpretedReceive.decodeResponse <$> native (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (opening : ∀ input, native (.inr (toOpenInput (mapInput interpret input))) = labels (.inr input))
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (target : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) :
    simulateQ native (simulateQ RawCtxWholeOwner.adapter
      (RawCtxOwnerOracle.receive ⟨mapRefined interpret entry⟩ target context)) =
      (fun result => (ConcreteRatchetKernel.mk (mapRefined interpret result.1), result.2)) <$>
        simulateQ labels (simulateQ openAdapter (RawCtxInterpretedReceive.receive entry target context)) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  apply RawCtxInterpretedReceive.receive_interpreted
  · intro request
    simpa [QueryImpl.compose, RawCtxWholeOwner.adapter, openAdapter, OracleSpec.query] using kdf request
  · exact openAdapter_interpreted interpret native labels opening

def sealArguments {Material : Type} (pending : RawCtxInterpretedSend.Seal Material RawCtxSourceSend.SealContext) :
    Input Material RawCtxSourceSend.SealContext := ⟨pending.material, pending.sequence, pending.context⟩

/-- Sealing arguments retain source sequence and context under material interpretation. -/
theorem sealArguments_map {Material Value : Type} (interpret : Material → Value)
    (pending : RawCtxInterpretedSend.Seal Material RawCtxSourceSend.SealContext) :
    sealArguments (RawCtxInterpretedSend.mapSeal interpret pending) = mapInput interpret (sealArguments pending) := rfl

/-- Generic sealing arguments specialize to the actual source getter product. -/
theorem sealArguments_native (pending : RawCtxInterpretedSend.Seal RatchetMaterial RawCtxSourceSend.SealContext) :
    RawCtxSourceSend.arguments (RawCtxInterpretedSend.nativeSeal pending) = toSealInput (sealArguments pending) := rfl

abbrev SealSpec (Material : Type) :=
  (SymmetricRatchetKdfRequest →ₒ (RatchetChain × Material)) +
    (Input Material RawCtxSourceSend.SealContext →ₒ Option Pqxdh.Bytes)

def encrypted {Material : Type} (input : Input Material RawCtxSourceSend.SealContext)
    (ciphertext : Pqxdh.Bytes) : RawCtxSourceSend.Encrypted :=
  ⟨ciphertext, input.context.targetId, input.sequence⟩

def sealAdapter {Material : Type} :
    QueryImpl (RawCtxInterpretedSend.SendSpec Material RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted)
      (OracleComp (SealSpec Material))
  | .inl request => liftM ((SealSpec Material).query (.inl request))
  | .inr pending => do
    let ciphertext ← (SealSpec Material).query (.inr (sealArguments pending))
    pure (ciphertext.map (encrypted (sealArguments pending)))

/-- Selected primitive equality preserves source optional ciphertext and API metadata wrapping. -/
theorem sealAdapter_interpreted {Material : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Material → RatchetMaterial)
    (native : QueryImpl RawCtxSourceSend.PrimitiveSpec m) (labels : QueryImpl (SealSpec Material) m)
    (sealing : ∀ input, native (.inr (toSealInput (mapInput interpret input))) = labels (.inr input))
    (pending : RawCtxInterpretedSend.Seal Material RawCtxSourceSend.SealContext) :
    simulateQ native (RawCtxSourceSend.adapter (.inr (RawCtxInterpretedSend.nativeSeal
      (RawCtxInterpretedSend.mapSeal interpret pending)))) =
      simulateQ labels (sealAdapter (.inr pending)) := by
  simp only [RawCtxSourceSend.adapter, sealArguments_native, sealArguments_map, sealAdapter,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  rw [sealing (sealArguments pending)]
  rfl

/-- Complete native send interpretation follows from primitive-input and decoded-KDF equations. -/
theorem send_interpreted {Material : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Material → RatchetMaterial)
    (native : QueryImpl RawCtxSourceSend.PrimitiveSpec m) (labels : QueryImpl (SealSpec Material) m)
    (kdf : ∀ request, RawCtxInterpretedReceive.decodeResponse <$> native (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (sealing : ∀ input, native (.inr (toSealInput (mapInput interpret input))) = labels (.inr input))
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (context : RawCtxSourceSend.SealContext) :
    simulateQ native (simulateQ RawCtxSourceSend.adapter
      (RawCtxSourceSend.send ⟨mapRefined interpret entry⟩ context)) =
      (fun result => (ConcreteRatchetKernel.mk (mapRefined interpret result.1), result.2)) <$>
        simulateQ labels (simulateQ sealAdapter (RawCtxInterpretedSend.send entry context)) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  apply RawCtxInterpretedSend.send_interpreted
  · intro request
    simpa [QueryImpl.compose, RawCtxSourceSend.adapter, sealAdapter, OracleSpec.query] using kdf request
  · exact sealAdapter_interpreted interpret native labels sealing

/-- The actual receive comparison retains the whole primitive poststate and actual optional API result. -/
theorem receive_state {Material PrimitiveState ι : Type} {base : OracleSpec ι}
    (interpret : Material → RatchetMaterial)
    (native : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (labels : QueryImpl (OpenSpec Material) (StateT PrimitiveState (OracleComp base)))
    (kdf : ∀ request, RawCtxInterpretedReceive.decodeResponse <$> native (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (opening : ∀ input, native (.inr (toOpenInput (mapInput interpret input))) = labels (.inr input))
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (target : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) (state : PrimitiveState) :
    (simulateQ native (simulateQ RawCtxWholeOwner.adapter
      (RawCtxOwnerOracle.receive ⟨mapRefined interpret entry⟩ target context))).run state =
      (fun result => ((ConcreteRatchetKernel.mk (mapRefined interpret result.1.1), result.1.2), result.2)) <$>
        (simulateQ labels (simulateQ openAdapter (RawCtxInterpretedReceive.receive entry target context))).run state := by
  simpa only [StateT.run_map] using congrArg (fun work : StateT PrimitiveState (OracleComp base)
      (ConcreteRatchetKernel × core.option.Option RawCtxWholeOwner.Decrypted) => work.run state)
    (receive_interpreted interpret native labels kdf opening entry target context)

/-- The actual send comparison retains the whole primitive poststate and advanced source kernel. -/
theorem send_state {Material PrimitiveState ι : Type} {base : OracleSpec ι}
    (interpret : Material → RatchetMaterial)
    (native : QueryImpl RawCtxSourceSend.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (labels : QueryImpl (SealSpec Material) (StateT PrimitiveState (OracleComp base)))
    (kdf : ∀ request, RawCtxInterpretedReceive.decodeResponse <$> native (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (sealing : ∀ input, native (.inr (toSealInput (mapInput interpret input))) = labels (.inr input))
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (context : RawCtxSourceSend.SealContext)
    (state : PrimitiveState) :
    (simulateQ native (simulateQ RawCtxSourceSend.adapter
      (RawCtxSourceSend.send ⟨mapRefined interpret entry⟩ context))).run state =
      (fun result => ((ConcreteRatchetKernel.mk (mapRefined interpret result.1.1), result.1.2), result.2)) <$>
        (simulateQ labels (simulateQ sealAdapter (RawCtxInterpretedSend.send entry context))).run state := by
  simpa only [StateT.run_map] using congrArg (fun work : StateT PrimitiveState (OracleComp base)
      (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) => work.run state)
    (send_interpreted interpret native labels kdf sealing entry context)

/-- Every selective underlying receive-query budget is preserved by complete interpretation. -/
theorem receive_query_bounds {Material PrimitiveState ι : Type} {base : OracleSpec ι}
    (interpret : Material → RatchetMaterial)
    (native : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (labels : QueryImpl (OpenSpec Material) (StateT PrimitiveState (OracleComp base)))
    (kdf : ∀ request, RawCtxInterpretedReceive.decodeResponse <$> native (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (opening : ∀ input, native (.inr (toOpenInput (mapInput interpret input))) = labels (.inr input))
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (target : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) (state : PrimitiveState)
    (predicate : base.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ native (simulateQ RawCtxWholeOwner.adapter
      (RawCtxOwnerOracle.receive ⟨mapRefined interpret entry⟩ target context))).run state).IsQueryBoundP predicate budget ↔
      ((simulateQ labels (simulateQ openAdapter (RawCtxInterpretedReceive.receive entry target context))).run state).IsQueryBoundP predicate budget := by
  rw [receive_state interpret native labels kdf opening entry target context state, isQueryBoundP_map_iff]

/-- Every selective underlying send-query budget is preserved by complete interpretation. -/
theorem send_query_bounds {Material PrimitiveState ι : Type} {base : OracleSpec ι}
    (interpret : Material → RatchetMaterial)
    (native : QueryImpl RawCtxSourceSend.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (labels : QueryImpl (SealSpec Material) (StateT PrimitiveState (OracleComp base)))
    (kdf : ∀ request, RawCtxInterpretedReceive.decodeResponse <$> native (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (sealing : ∀ input, native (.inr (toSealInput (mapInput interpret input))) = labels (.inr input))
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (context : RawCtxSourceSend.SealContext)
    (state : PrimitiveState) (predicate : base.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ native (simulateQ RawCtxSourceSend.adapter
      (RawCtxSourceSend.send ⟨mapRefined interpret entry⟩ context))).run state).IsQueryBoundP predicate budget ↔
      ((simulateQ labels (simulateQ sealAdapter (RawCtxInterpretedSend.send entry context))).run state).IsQueryBoundP predicate budget := by
  rw [send_state interpret native labels kdf sealing entry context state, isQueryBoundP_map_iff]

end BeaconcryptCore.Computational.RawCtxInterpretedArguments

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedArguments.sequence_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedArguments.sequence_total

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedArguments.material_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedArguments.material_total

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedArguments.openArguments_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedArguments.openArguments_map

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedArguments.openArguments_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedArguments.openArguments_native

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedArguments.openAdapter_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedArguments.openAdapter_interpreted

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedArguments.receive_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedArguments.receive_interpreted

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedArguments.sealArguments_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedArguments.sealArguments_map

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedArguments.sealArguments_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedArguments.sealArguments_native

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedArguments.sealAdapter_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedArguments.sealAdapter_interpreted

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedArguments.send_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedArguments.send_interpreted

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedArguments.receive_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedArguments.receive_state

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedArguments.send_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedArguments.send_state

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedArguments.receive_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedArguments.receive_query_bounds

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedArguments.send_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedArguments.send_query_bounds
