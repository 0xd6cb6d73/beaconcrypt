import BeaconcryptCore.Computational.RawCtxOwnerOracle
import BeaconcryptCore.Computational.RawCtxOwnerResult
import BeaconcryptCore.PanicFreedom.Effects

/-!
This adapter models one already-selected, established owner. It uses the actual extracted getter and receive effects, keeps both directional chains and all cached state together, and carries a separate complete primitive state through failures. Opening arguments contain no claimed plaintext. The true optional opening output is wrapped with its request metadata before source publication. Every raw call, including empty/parser/validation rejection, increments a separate ghost attempt counter.

The frame decoder remains an explicit function, the native associated-data array instantiation has length 153, and peer lookup has already selected this owner and its pinned sender. This module does not prove Cap'n Proto, native ownership/CAS, copied snapshots, dynamic peer/key routing, validity of arbitrary restored owners or the equality of a prepared sequence to the decoded target. It proves operational argument provenance, publication, rollback, unchanged metadata and adaptive attempt accounting, not cryptographic authentication.

The bounded client may adapt raw requests and stopping to the actual API option. It has only this raw interface; other network, random, reveal and compromise actions require the common experiment's additional interfaces and budgets. Exposing an unknown target plaintext here is declassification for a confidentiality experiment, not evidence that ProVerif exposes the same honest application result. The private primitive interpreter must separately instantiate actual KDF/CTX/AEAD contracts and their internal query costs; no independent evolving-key distribution or security conclusion is assumed by this adapter.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxWholeOwner

/-- API result metadata is constructed from the actual source opening capability. -/
structure Decrypted where
  plaintext : Pqxdh.Bytes
  keyId : Std.U64
  sequence : Std.U64

/-- The single decoded frame and original raw input are retained with the selected owner's AD. -/
structure OpenContext where
  raw : Pqxdh.Bytes
  frame : RawCtxReceive.DecodedFrame
  associatedData : Pqxdh.Bytes

/-- No plaintext is supplied to this private cryptographic opening interface. -/
structure OpenInput where
  material : RatchetMaterial
  sequence : Std.U64
  context : OpenContext

/-- Normalize only already-total extracted getter results, preserving the missing-material branch. -/
noncomputable def arguments (pending : ReceiveOpen OpenContext) : Option OpenInput :=
  match pending.material_total.choose with
  | .None => none
  | .Some material => some ⟨material, pending.sequence_total.choose, pending.context⟩

/-- Every opening input has exact source getter and context provenance. -/
theorem arguments_some (pending : ReceiveOpen OpenContext) (input : OpenInput)
    (h : arguments pending = some input) :
    pending.material = ok (.Some input.material) ∧
      pending.sequence = ok input.sequence ∧ input.context = pending.context := by
  unfold arguments at h
  split at h
  · cases h
  · cases Option.some.inj h
    exact ⟨by simpa only [‹pending.material_total.choose = _›] using pending.material_total.choose_spec,
      pending.sequence_total.choose_spec, rfl⟩

/-- Missing material returns rejection before any private cryptographic opening query. -/
theorem arguments_none (pending : ReceiveOpen OpenContext)
    (h : pending.material = ok .None) : arguments pending = none := by
  have hnone := RustM.ok.inj (pending.material_total.choose_spec.symm.trans h)
  simp only [arguments, hnone]

/-- Private primitive calls expose actual KDF and opening arguments, with no adversarial plaintext field. -/
abbrev PrimitiveSpec :=
  (SymmetricRatchetKdfRequest →ₒ RatchetKdfResponse) +
    (OpenInput →ₒ core.option.Option Pqxdh.Bytes)

/-- Construct the API value from the actual returned plaintext and the same prepared request. -/
def decrypted (input : OpenInput) (plaintext : Pqxdh.Bytes) : Decrypted :=
  ⟨plaintext, input.context.frame.sender, input.sequence⟩

/-- The adapter reads source getters, performs one real optional opening, and wraps before publication. -/
noncomputable def adapter :
    QueryImpl (RawCtxOwnerOracle.ReceiveSpec OpenContext Decrypted) (OracleComp PrimitiveSpec)
  | .inl request => liftM (PrimitiveSpec.query (.inl request))
  | .inr pending =>
      match arguments pending with
      | none => pure .None
      | some input => do
          let reply ← PrimitiveSpec.query (.inr input)
          pure (RawCtxOwnerResult.mapReply (decrypted input) reply)

/-- Missing source material makes no opening call and returns the actual rejection option. -/
theorem adapter_missing (pending : ReceiveOpen OpenContext)
    (h : pending.material = ok .None) : adapter (.inr pending) = pure .None := by
  simp only [adapter, arguments_none pending h]

/-- One present source material selects the exact private opening input and true returned option. -/
theorem adapter_present (pending : ReceiveOpen OpenContext) (input : OpenInput)
    (h : arguments pending = some input) : adapter (.inr pending) = (do
      let reply ← PrimitiveSpec.query (.inr input)
      pure (RawCtxOwnerResult.mapReply (decrypted input) reply)) := by
  simp only [adapter, h]

/-- One owner contains both directional chains, cache, counters and arbitrary retained role metadata. -/
structure Owner (Metadata : Type) where
  kernel : ConcreteRatchetKernel
  expectedSender : Std.U64
  associatedData : Pqxdh.Bytes
  metadata : Metadata

/-- A ghost attempt counter is outside the native ratchet and increments even before parser rejection. -/
structure OwnerState (Metadata : Type) where
  owner : Owner Metadata
  rawAttempts : Nat

/-- Reinstall the entire source kernel before returning the actual optional API value. -/
def publish {Metadata : Type} (state : OwnerState Metadata)
    (result : ConcreteRatchetKernel × core.option.Option Decrypted) :
    core.option.Option Decrypted × OwnerState Metadata :=
  (result.2, ⟨{ state.owner with kernel := result.1 }, state.rawAttempts + 1⟩)

/-- One raw operation serializes a whole owner; parser/validation failure does not take its kernel. -/
noncomputable def rawReceive {Metadata : Type} (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) : StateT (OwnerState Metadata) (OracleComp PrimitiveSpec)
      (core.option.Option Decrypted) := fun state =>
  if raw.isEmpty then pure (publish state (state.owner.kernel, .None)) else
  match decode raw with
  | none => pure (publish state (state.owner.kernel, .None))
  | some frame =>
      if RawCtxReceive.ValidFrame state.owner.expectedSender state.owner.associatedData frame then do
        let result ← simulateQ adapter (RawCtxOwnerOracle.receive state.owner.kernel frame.sequence
          ⟨raw, frame, state.owner.associatedData⟩)
        pure (publish state result)
      else pure (publish state (state.owner.kernel, .None))

/-- The complete primitive state lives outside the one owned protocol state. -/
noncomputable def rawGame {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : OwnerState Metadata) (primitive : PrimitiveState) :
    OracleComp base ((core.option.Option Decrypted × OwnerState Metadata) × PrimitiveState) :=
  (simulateQ impl ((rawReceive decode raw).run state)).run primitive

/-- Every raw result publishes one whole kernel, and rejection restores the complete entry kernel. -/
theorem rawGame_publication {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : OwnerState Metadata) (primitive : PrimitiveState)
    (result : (core.option.Option Decrypted × OwnerState Metadata) × PrimitiveState)
    (hsupport : result ∈ support (rawGame impl decode raw state primitive)) :
    ∃ kernel reply, result.1 = publish state (kernel, reply) ∧
      (reply = .None → kernel = state.owner.kernel) := by
  unfold rawGame rawReceive StateT.run at hsupport
  split at hsupport
  · change result ∈ support ((simulateQ impl
        (pure (publish state (state.owner.kernel, .None)))).run primitive) at hsupport
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hsupport
    exact ⟨state.owner.kernel, .None, congrArg Prod.fst hsupport, fun _ => rfl⟩
  · split at hsupport
    · change result ∈ support ((simulateQ impl
          (pure (publish state (state.owner.kernel, .None)))).run primitive) at hsupport
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hsupport
      exact ⟨state.owner.kernel, .None, congrArg Prod.fst hsupport, fun _ => rfl⟩
    · dsimp only at hsupport
      split at hsupport
      · rw [simulateQ_bind] at hsupport
        change result ∈ support (StateT.run _ primitive) at hsupport
        simp only [StateT.run_bind, simulateQ_pure, StateT.run_pure, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff] at hsupport
        obtain ⟨opened, hopen, rfl⟩ := hsupport
        rw [← QueryImpl.simulateQ_compose] at hopen
        exact ⟨opened.1.1, opened.1.2, rfl,
          RawCtxOwnerOracle.receive_failure_entry _ _ _ _ _ _ hopen⟩
      · change result ∈ support ((simulateQ impl
            (pure (publish state (state.owner.kernel, .None)))).run primitive) at hsupport
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hsupport
        exact ⟨state.owner.kernel, .None, congrArg Prod.fst hsupport, fun _ => rfl⟩

/-- Every raw attempt increments once while retaining the owner's pinned route, AD and complete metadata. -/
theorem rawGame_preserves_metadata {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : OwnerState Metadata) (primitive : PrimitiveState)
    (result : (core.option.Option Decrypted × OwnerState Metadata) × PrimitiveState)
    (hsupport : result ∈ support (rawGame impl decode raw state primitive)) :
    result.1.2.rawAttempts = state.rawAttempts + 1 ∧
      result.1.2.owner.expectedSender = state.owner.expectedSender ∧
      result.1.2.owner.associatedData = state.owner.associatedData ∧
      result.1.2.owner.metadata = state.owner.metadata := by
  obtain ⟨kernel, reply, hpublish, _⟩ := rawGame_publication impl decode raw state primitive result hsupport
  rw [hpublish]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Failed raw operations preserve the entire owner, including both chains, cache, route and role metadata. -/
theorem rawGame_failure_owner {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : OwnerState Metadata) (primitive : PrimitiveState)
    (result : (core.option.Option Decrypted × OwnerState Metadata) × PrimitiveState)
    (hsupport : result ∈ support (rawGame impl decode raw state primitive))
    (hfailure : result.1.1 = .None) : result.1.2.owner = state.owner := by
  obtain ⟨kernel, reply, hpublish, hrollback⟩ := rawGame_publication impl decode raw state primitive result hsupport
  have hreply : reply = .None := (congrArg Prod.fst hpublish).symm.trans hfailure
  simpa only [publish, hrollback hreply] using congrArg (fun result => result.2.owner) hpublish

/-- An adaptive client supplies only raw bytes and receives only the true optional API result. -/
abbrev RawSpec := Pqxdh.Bytes →ₒ core.option.Option Decrypted

/-- One state interpreter serializes the complete owner and the separate complete primitive state. -/
noncomputable def ownerImpl {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawSpec (StateT (OwnerState Metadata × PrimitiveState) (OracleComp base)) :=
  fun raw state => do
    let result ← rawGame impl decode raw state.1 state.2
    pure (result.1.1, (result.1.2, result.2))

/-- Each adaptive raw query increments exactly once and preserves immutable owner metadata. -/
theorem ownerImpl_step {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : OwnerState Metadata × PrimitiveState)
    (result : core.option.Option Decrypted × (OwnerState Metadata × PrimitiveState))
    (hsupport : result ∈ support ((ownerImpl impl decode raw).run state)) :
    result.2.1.rawAttempts = state.1.rawAttempts + 1 ∧
      result.2.1.owner.expectedSender = state.1.owner.expectedSender ∧
      result.2.1.owner.associatedData = state.1.owner.associatedData ∧
      result.2.1.owner.metadata = state.1.owner.metadata := by
  simp only [ownerImpl, StateT.run, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hsupport
  obtain ⟨received, hreceived, rfl⟩ := hsupport
  exact rawGame_preserves_metadata impl decode raw state.1 state.2 received hreceived

/-- Adaptive stopping and raw choices use the actual returned option, retaining one whole owner between calls. -/
noncomputable def scheduleGame {Metadata PrimitiveState Result : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp RawSpec Result)
    (state : OwnerState Metadata × PrimitiveState) :
    OracleComp base (Result × (OwnerState Metadata × PrimitiveState)) :=
  (simulateQ (ownerImpl impl decode) client).run state

/-- An arbitrary bounded raw schedule counts every attempt and preserves immutable metadata through every reply. -/
theorem scheduleGame_bounds {Metadata PrimitiveState Result : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp RawSpec Result)
    (qRaw : Nat) (hbound : client.IsTotalQueryBound qRaw)
    (state : OwnerState Metadata × PrimitiveState)
    (result : Result × (OwnerState Metadata × PrimitiveState))
    (hsupport : result ∈ support (scheduleGame impl decode client state)) :
    result.2.1.rawAttempts ≤ state.1.rawAttempts + qRaw ∧
      result.2.1.owner.expectedSender = state.1.owner.expectedSender ∧
      result.2.1.owner.associatedData = state.1.owner.associatedData ∧
      result.2.1.owner.metadata = state.1.owner.metadata := by
  unfold scheduleGame at hsupport
  induction client using OracleComp.inductionOn generalizing qRaw state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hsupport
      subst result
      exact ⟨Nat.le_add_right _ _, rfl, rfl, rfl⟩
  | query_bind raw rest ih =>
      rw [isTotalQueryBound_query_bind_iff] at hbound
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hsupport
      obtain ⟨step, hstep, hrest⟩ := hsupport
      have stepFacts := ownerImpl_step impl decode raw state step hstep
      have restFacts := ih step.1 (qRaw - 1) (hbound.2 step.1) step.2 result hrest
      exact ⟨by omega, restFacts.2.1.trans stepFacts.2.1,
        restFacts.2.2.1.trans stepFacts.2.2.1, restFacts.2.2.2.trans stepFacts.2.2.2⟩

end BeaconcryptCore.Computational.RawCtxWholeOwner

/--
info: 'BeaconcryptCore.Computational.RawCtxWholeOwner.arguments_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxWholeOwner.arguments_some

/--
info: 'BeaconcryptCore.Computational.RawCtxWholeOwner.arguments_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxWholeOwner.arguments_none

/--
info: 'BeaconcryptCore.Computational.RawCtxWholeOwner.adapter_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxWholeOwner.adapter_missing

/--
info: 'BeaconcryptCore.Computational.RawCtxWholeOwner.adapter_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxWholeOwner.adapter_present

/--
info: 'BeaconcryptCore.Computational.RawCtxWholeOwner.rawGame_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxWholeOwner.rawGame_publication

/--
info: 'BeaconcryptCore.Computational.RawCtxWholeOwner.rawGame_preserves_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxWholeOwner.rawGame_preserves_metadata

/--
info: 'BeaconcryptCore.Computational.RawCtxWholeOwner.rawGame_failure_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxWholeOwner.rawGame_failure_owner

/--
info: 'BeaconcryptCore.Computational.RawCtxWholeOwner.ownerImpl_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxWholeOwner.ownerImpl_step

/--
info: 'BeaconcryptCore.Computational.RawCtxWholeOwner.scheduleGame_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxWholeOwner.scheduleGame_bounds
