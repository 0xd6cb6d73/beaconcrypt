import BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness
import BeaconcryptCore.Computational.RawCtxGenericFamilyRead

/-!
Opaque selected-message slots use the actual extracted skipped-key lookup. The complete generic server/beacon family supplies the original owner and optional installed kernel, so missing peers and inactive phases reject exactly as the source. Interpreting a successful read reconstructs its actual optional reply and the appended native history. A separate key-free emission operation withholds a hidden key and marks the resulting source freshness event false; it never fabricates a reply to continue after secret disclosure.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedMessageReveals
open PqxdhSecretInputKdf RawCtxSelectedMessageKey RawCtxSelectedMessageFreshness RawCtxFreshChainCut
open RawCtxProtocolReveals (Request)
open RawCtxMaterialInterpretation
variable {M P I D K A : Type} {S B : Nat}

abbrev Kernel := RefinedRatchet RatchetChain RatchetChain Slot

def nativeKernel (key : RootOutput) (entry : Kernel) : ConcreteRatchetKernel :=
  ⟨mapRefined (interpret key) entry⟩

noncomputable def skipped (entry : Kernel) (sequence : Std.U64) : core.option.Option Slot :=
  (refined_receive_key_total entry sequence).choose

/-- Opaque lookup is the normal result of the same total extracted guarded slot lookup, including malformed tags and missing entries. -/
theorem skipped_exact (entry : Kernel) (sequence : Std.U64) :
    refined_receive_key entry sequence = ok (skipped entry sequence) :=
  (refined_receive_key_total entry sequence).choose_spec

/-- Material interpretation preserves the actual optional skipped-key reply without an injectivity, cache-consistency or successful-lookup premise. -/
theorem skipped_map (key : RootOutput) (entry : Kernel) (sequence : Std.U64) :
    RawCtxProtocolReveals.skippedKey (nativeKernel key entry) sequence =
      mapOption (interpret key) (skipped entry sequence) := by
  have native := RawCtxProtocolReveals.skipped_exact (nativeKernel key entry) sequence
  change refined_receive_key (mapRefined (interpret key) entry) sequence = _ at native
  rw [receive_key_map, skipped_exact, rust_map_ok] at native
  exact (RustM.ok.inj native).symm

noncomputable def reply : (request : Request S B) → Option Kernel → (RawCtxSelectedMessageFreshness.RevealSpec S B).Range request
  | .sendChain _, none | .receiveChain _, none | .skippedKey _ _, none => .None
  | .sendChain _, some entry => .Some entry.send_chain
  | .receiveChain _, some entry => .Some entry.receive_chain
  | .skippedKey _ sequence, some entry => skipped entry sequence

def interpretReply (key : RootOutput) : (request : Request S B) →
    (RawCtxSelectedMessageFreshness.RevealSpec S B).Range request → (RawCtxProtocolReveals.RevealSpec S B).Range request
  | .sendChain _, value | .receiveChain _, value => value
  | .skippedKey _ _, value => mapOption (interpret key) value

/-- Interpreting the private observation preserves its original owner, requested sequence and complete optional reply. -/
theorem observation_reply (key : RootOutput) (request : Request S B)
    (value : (RawCtxSelectedMessageFreshness.RevealSpec S B).Range request) :
    interpretObservation key ⟨request, value⟩ = ⟨request, interpretReply key request value⟩ := by
  cases request <;> cases value <;> rfl

/-- The actual native read consumes the same optional kernel and returns the exact interpretation of its opaque-material read. -/
theorem reply_exact (key : RootOutput) (request : Request S B) (entry : Option Kernel) :
    RawCtxGenericFamilyRead.nativeValue (nativeKernel key) (request, entry) =
      interpretReply key request (reply request entry) := by
  cases request <;> cases entry <;> first | rfl | exact skipped_map key _ _

abbrev Roles (M P I D K : Type) (S B : Nat) := RawCtxGenericRoleFamily.Roles Kernel M P I D K S B
abbrev State (M P I D K : Type) (S B : Nat) := Roles M P I D K S B × History S B

def nativeState (key : RootOutput) (state : State M P I D K S B) : RawCtxProtocolReveals.State M P I D K S B :=
  (RawCtxGenericRoleFamily.nativeRoles (nativeKernel key) state.1, interpretHistory key state.2)

noncomputable def selectedReply (request : Request S B) (roles : Roles M P I D K S B) :=
  reply request (RawCtxGenericRoleFamily.selectedKernel (RawCtxGenericFamilyRead.requestOwner request) roles)

noncomputable def step (request : Request S B) (state : State M P I D K S B) :
    (RawCtxSelectedMessageFreshness.RevealSpec S B).Range request × State M P I D K S B :=
  let value := selectedReply request state.1
  (value, (state.1, note ⟨request, value⟩ state.2))

/-- The complete source server/beacon family selects the same original peer or phase and gives the exact interpreted reply, including every missing-owner and inactive-phase rejection. -/
theorem source_reply (key : RootOutput) (request : Request S B) (roles : Roles M P I D K S B) :
    RawCtxProtocolReveals.reveal request (RawCtxGenericRoleFamily.nativeRoles (nativeKernel key) roles) =
      interpretReply key request (selectedReply request roles) :=
  (RawCtxGenericFamilyRead.source_value (nativeKernel key) request roles).symm.trans
    (reply_exact key request _)

/-- An actual source read preserves the full role family and shared primitive state while appending precisely the interpreted optional reply at the original timestamp. -/
theorem source_step (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (key : RootOutput) (request : Request S B) (state : State M P I D K S B)
    (ambient : RawCtxSharedPrimitive.SharedState A) :
    ((RawCtxProtocolReveals.sourceImpl source writer S B sender route decode) (.inr request)).run
      (nativeState key state, ambient) =
      pure (interpretReply key request (step request state).1, (nativeState key (step request state).2, ambient)) := by
  simp only [RawCtxProtocolReveals.sourceImpl, StateT.run, nativeState, source_reply, step, interpret_note,
    observation_reply]

/-- Emit the original API optional value when available; a returned hidden slot stops the source comparison before disclosure. -/
def emit : (request : Request S B) → (RawCtxSelectedMessageFreshness.RevealSpec S B).Range request →
    Option ((RawCtxProtocolReveals.RevealSpec S B).Range request)
  | .sendChain _, value | .receiveChain _, value => some value
  | .skippedKey _ _, .None => some .None
  | .skippedKey _ _, .Some (.known material) => some (.Some material)
  | .skippedKey _ _, .Some (.hidden _) => none

/-- Every emitted optional source read reply is the exact native value and requires no selected key. -/
theorem emit_exact (key : RootOutput) (request : Request S B)
    (value : (RawCtxSelectedMessageFreshness.RevealSpec S B).Range request)
    (native : (RawCtxProtocolReveals.RevealSpec S B).Range request) (emitted : emit request value = some native) :
    interpretReply key request value = native := by
  cases request with
  | sendChain _ => exact Option.some.inj emitted
  | receiveChain _ => exact Option.some.inj emitted
  | skippedKey _ _ =>
    cases value with
    | none => exact Option.some.inj emitted
    | some material =>
      cases material with
      | hidden _ => contradiction
      | known _ => exact Option.some.inj emitted

/-- Emission stops exactly for a successful hidden skipped-key lookup; rejection and every known alias remain ordinary replies. -/
theorem stopped_iff (request : Request S B)
    (value : (RawCtxSelectedMessageFreshness.RevealSpec S B).Range request) :
    emit request value = none ↔ hiddenObservation ⟨request, value⟩ = true := by
  cases request <;> cases value <;> simp only [emit, hiddenObservation, reduceCtorEq, Bool.false_eq_true]
  rename_i material
  cases material <;> simp

/-- Withholding an unavailable read occurs only after an actual source disclosure that makes the original selected-record freshness false. -/
theorem source_stopped (key : RootOutput) (request : Request S B) (state : State M P I D K S B)
    (remaining prior : List RatchetChain) (stopped : emit request (step request state).1 = none) :
    ¬ RawCtxLiveLineage.Fresh (concreteChain key :: remaining) prior (nativeState key (step request state).2).2 := by
  have returned := (stopped_iff request (step request state).1).mp stopped
  exact hidden_stops key remaining prior (note ⟨request, selectedReply request state.1⟩ state.2)
    state.2.position ⟨request, selectedReply request state.1⟩ (by simp [note]) returned

/-- Every permitted emitted reply agrees with the complete actual source read, including its full family, unchanged shared state and original disclosure log. -/
theorem source_admitted (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (key : RootOutput) (request : Request S B) (state : State M P I D K S B)
    (ambient : RawCtxSharedPrimitive.SharedState A)
    (native : (RawCtxProtocolReveals.RevealSpec S B).Range request)
    (emitted : emit request (step request state).1 = some native) :
    ((RawCtxProtocolReveals.sourceImpl source writer S B sender route decode) (.inr request)).run
      (nativeState key state, ambient) = pure (native, (nativeState key (step request state).2, ambient)) := by
  rw [source_step, emit_exact key request (step request state).1 native emitted]

/-- Each actual read appends one attempted observation even on rejection and keeps every owner field unchanged. -/
theorem step_fields (request : Request S B) (state : State M P I D K S B) :
    (step request state).2.1 = state.1 ∧ (step request state).2.2.position = state.2.position + 1 ∧
      (step request state).2.2.observations = state.2.observations ++ [(state.2.position, ⟨request, (step request state).1⟩)] :=
  ⟨rfl, rfl, rfl⟩

/-- One actual optional source read adds at most one stopped CTX key probe, preserving all earlier candidates and repetitions. -/
theorem step_probe_bound (prior : List RatchetChain) (request : Request S B) (state : State M P I D K S B) :
    (keys prior (step request state).2.2).length ≤ (keys prior state.2).length + 1 := by
  simp only [step, keys, List.length_map, known_note, List.length_append]
  exact Nat.add_le_add_left (candidates_length ⟨request, selectedReply request state.1⟩) _

/-- Native reveal lookup and copying sample no random bytes; their source read attempt and candidate costs are still counted separately. -/
theorem source_uniform (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (key : RootOutput) (request : Request S B) (state : State M P I D K S B)
    (ambient : RawCtxSharedPrimitive.SharedState A) :
    (((RawCtxProtocolReveals.sourceImpl source writer S B sender route decode) (.inr request)).run
      (nativeState key state, ambient)).IsTotalQueryBound 0 := by
  rw [source_step]
  trivial

end BeaconcryptCore.Computational.RawCtxSelectedMessageReveals

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.skipped_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.skipped_exact
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.skipped_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.skipped_map
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.observation_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.observation_reply
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.reply_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.reply_exact
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.source_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.source_reply
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.source_step
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.emit_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.emit_exact
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.stopped_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.stopped_iff
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.source_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.source_stopped
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.source_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.source_admitted
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.step_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.step_fields
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.step_probe_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.step_probe_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.source_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageReveals.source_uniform
