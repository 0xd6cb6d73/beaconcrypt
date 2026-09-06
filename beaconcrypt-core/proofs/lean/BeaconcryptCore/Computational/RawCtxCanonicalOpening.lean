import BeaconcryptCore.Computational.RawCtxSourceOpen
import BeaconcryptCore.Computational.AdaptiveCtxCanonical

/-!
This is an exact per-opening connection from the source-selected private capability to the existing canonical CTX raw kernel. The original decoded protected payload and the selected material's nonce determine an unclaimed target; prepared sequence, decoded sender and the owning AD remain exact. Under the already explicit ROM-total/ordinary-AEAD interface, the actual source computation and canonical computation return the same optional plaintext and full shared cache, including failed commitment lookups. Arbitrary continuations and arbitrary stateful hash interpretations retain complete output/state equality.

Canonical suffix and attempt instrumentation is added only for this selected opening. It is not the whole-owner outer raw-attempt counter: parse, KDF or missing-material rejection can happen before any opening. The decoder is parameterized by the material selected for this call. This does not identify one fixed decoder or independent uniform key across evolving ratchet states. The selectedDecoder theorem names source preparation provenance explicitly; transferring all failed callback occurrences through a complete owner schedule remains a separate source invariant. The previously proved successful-callback provenance is not assumed for the kernel equality, which retains every optional reply.

The shared-cache opening costs at most 64 byte-valued uniform-oracle calls and may use zero on a cache hit. Source hash/AEAD and KDF ledgers remain the separately checked native source ledgers; functional AEAD interpretation does not declare its local work free. Native optional hash failure remains modeled before the total-ROM specialization. Analysis-only typed record normalization, functional frame-reader and combined/detached AEAD contracts are unchanged. This module adds no primitive implementation proof, native codec refinement, key distribution/freshness assumption, multi-key security bound, consuming ratchet simulation, or final global composition theorem.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec

set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxCanonicalOpening
open CtxRomAuth CtxSplitCache AdaptiveCtxReceive AdaptiveCtxCanonical
open RawCtxSourceOpen

/-- The selected source capability supplies every field of an unclaimed opening target. -/
noncomputable def selectedTarget (input : RawCtxWholeOwner.OpenInput)
    (slices : RawCtxFrameDecoding.Slices)
    (hslices : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices)
    (had : input.context.associatedData.length = 153) : CtxUnclaimedAcceptance.Target :=
  ⟨sourceNonce input, sourceContext input had, sourceRecord input slices hslices⟩

/-- The actual source typed opening invokes the canonical optional opening on the same digest. -/
theorem typedOpen_target (c : Pqxdh.Crypto) (key : CtxKey)
    (target : CtxUnclaimedAcceptance.Target) :
    typedOpen c key target.nonce target.context target.record = (do
      let digest ← CtxRO.query ((), outerInput key target.nonce target.context target.record.tag)
      pure (targetOpen c key target digest)) := by
  rfl

/-- Canonical bookkeeping records this selected opening without changing any prior seal or nonce history. -/
def afterOpening (state : CanonicalState) (target : CtxUnclaimedAcceptance.Target)
    (cache : CtxRO.QueryCache) : CanonicalState :=
  ⟨{ state.ctx with cache := cache }, state.rawAttempts + 1,
    outerSuffix target.nonce target.context target.record.tag :: state.privateInputs⟩

/-- The actual source opening uses the same shared cache; only canonical bookkeeping is added. -/
noncomputable def sourceOpening (c : Pqxdh.Crypto) (input : RawCtxWholeOwner.OpenInput)
    (target : CtxUnclaimedAcceptance.Target) (state : CanonicalState) :
    ProbComp (Option Pqxdh.Bytes × CanonicalState) := do
  let result ← (simulateQ ctxRandomOracle (simulateQ (romAdapter c) (openInput input))).run state.ctx.cache
  pure (result.1, afterOpening state target result.2)

/-- One source-selected opening equals the canonical raw kernel, including the actual optional plaintext and full cache. -/
theorem sourceOpening_canonical (c : Pqxdh.Crypto) (input : RawCtxWholeOwner.OpenInput)
    (slices : RawCtxFrameDecoding.Slices)
    (hslices : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices)
    (had : input.context.associatedData.length = 153)
    (decode : RawDecoder) (state : CanonicalState)
    (hdecode : decode input.context.raw = some (selectedTarget input slices hslices had)) :
    sourceOpening c input (selectedTarget input slices hslices had) state =
      canonicalRaw decode c (sourceKey input) input.context.raw state := by
  simp only [sourceOpening, openInput_typed c input slices hslices had, typedOpen,
    simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    bind_assoc, pure_bind, canonicalRaw, hdecode, afterOpening, selectedTarget, targetOpen]

/-- Normalize the unchanged raw frame with the nonce actually selected by the owner for this opening. -/
noncomputable def selectedDecoder (material : RatchetMaterial) (expected : Std.U64)
    (ad : Pqxdh.Bytes) (decode : RawCtxReceive.FrameDecoder) : RawDecoder := fun raw =>
  if raw.isEmpty then none else
  match decode raw with
  | none => none
  | some frame =>
      if hvalid : RawCtxReceive.ValidFrame expected ad frame then
        match hslices : RawCtxFrameDecoding.fromPayload frame.payload with
        | none => none
        | some slices => some (selectedTarget ⟨material, frame.sequence, ⟨raw, frame, ad⟩⟩
            slices hslices hvalid.2.2)
      else none

/-- Actual decoded-frame and prepared-sequence provenance discharges the canonical decoder equation. -/
theorem selectedDecoder_source (input : RawCtxWholeOwner.OpenInput)
    (slices : RawCtxFrameDecoding.Slices)
    (hslices : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices)
    (decode : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (hraw : input.context.raw.isEmpty = false)
    (hdecode : decode input.context.raw = some input.context.frame)
    (hvalid : RawCtxReceive.ValidFrame expected input.context.associatedData input.context.frame)
    (hsequence : input.sequence = input.context.frame.sequence) :
    selectedDecoder input.material expected input.context.associatedData decode input.context.raw =
      some (selectedTarget input slices hslices hvalid.2.2) := by
  cases input with
  | mk material sequence context =>
    cases context with
    | mk raw frame ad =>
      simp only at hraw hdecode hvalid hsequence hslices ⊢
      subst sequence
      simp only [selectedDecoder, hraw, Bool.false_eq_true, if_false, hdecode,
        dif_pos hvalid]
      split <;> simp_all only [Option.some.injEq, reduceCtorEq]
      rename_i actual heq
      have equal := Option.some.inj (heq.symm.trans hslices)
      subst actual
      rfl

/-- The canonical decoder is derived from the actual source frame and selected nonce for this one opening. -/
theorem sourceOpening_selected (c : Pqxdh.Crypto) (input : RawCtxWholeOwner.OpenInput)
    (slices : RawCtxFrameDecoding.Slices)
    (hslices : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices)
    (decode : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (hraw : input.context.raw.isEmpty = false)
    (hdecode : decode input.context.raw = some input.context.frame)
    (hvalid : RawCtxReceive.ValidFrame expected input.context.associatedData input.context.frame)
    (hsequence : input.sequence = input.context.frame.sequence) (state : CanonicalState) :
    sourceOpening c input (selectedTarget input slices hslices hvalid.2.2) state =
      canonicalRaw (selectedDecoder input.material expected input.context.associatedData decode)
        c (sourceKey input) input.context.raw state := by
  exact sourceOpening_canonical c input slices hslices hvalid.2.2 _ state
    (selectedDecoder_source input slices hslices decode expected hraw hdecode hvalid hsequence)

/-- Arbitrary later computation receives the same real optional plaintext and complete canonical state. -/
theorem sourceOpening_continuation {Result : Type} (c : Pqxdh.Crypto)
    (input : RawCtxWholeOwner.OpenInput) (slices : RawCtxFrameDecoding.Slices)
    (hslices : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices)
    (had : input.context.associatedData.length = 153) (decode : RawDecoder) (state : CanonicalState)
    (hdecode : decode input.context.raw = some (selectedTarget input slices hslices had))
    (next : Option Pqxdh.Bytes × CanonicalState → ProbComp Result) :
    (sourceOpening c input (selectedTarget input slices hslices had) state >>= next) =
      (canonicalRaw decode c (sourceKey input) input.context.raw state >>= next) := by
  rw [sourceOpening_canonical c input slices hslices had decode state hdecode]

/-- Canonical opening makes at most one 64-byte digest draw; cache hits and malformed inputs retain smaller costs. -/
theorem canonicalRaw_uniform (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (raw : Pqxdh.Bytes) (state : CanonicalState) :
    (canonicalRaw decode c key raw state).IsTotalQueryBound 64 := by
  cases hdecode : decode raw with
  | none => simp only [canonicalRaw, hdecode]; trivial
  | some target =>
    unfold canonicalRaw
    rw [hdecode]
    simp only [bind_pure_comp]
    unfold IsTotalQueryBound
    rw [isQueryBound_map_iff]
    exact CtxComputationalSecurity.ctxRandomOracle_total_query_bound
      ((), outerInput key target.nonce target.context target.record.tag) state.ctx.cache

/-- The target retains the original protected payload and every actual source-selected context field. -/
theorem selectedTarget_fields (input : RawCtxWholeOwner.OpenInput)
    (slices : RawCtxFrameDecoding.Slices)
    (hslices : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices)
    (had : input.context.associatedData.length = 153) :
    let target := selectedTarget input slices hslices had
    target.nonce.toList = (BeaconcryptCore.Refinement.RepresentationBridge.absMaterial input.material).2 ∧
      target.context.ad.bytes = input.context.associatedData ∧
      target.context.ad.seq = input.sequence.val ∧
      target.context.ad.sid = input.context.frame.sender.val ∧
      target.record.encode = input.context.frame.payload ∧
      slices.baseCiphertext = target.record.body ++ target.record.tag := by
  exact ⟨rfl, rfl, rfl, rfl, (sourceRecord_spec input slices hslices).2.2.2.2.2,
    (sourceRecord_spec input slices hslices).2.1⟩

/-- Source-to-canonical opening transport holds for any complete stateful hash interpretation. -/
theorem sourceOpening_interpretation {PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl CtxRO (StateT PrimitiveState (OracleComp base)))
    (c : Pqxdh.Crypto) (input : RawCtxWholeOwner.OpenInput)
    (slices : RawCtxFrameDecoding.Slices)
    (hslices : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices)
    (had : input.context.associatedData.length = 153) (primitive : PrimitiveState) :
    (simulateQ impl (simulateQ (romAdapter c) (openInput input))).run primitive =
      (simulateQ impl (do
        let target := selectedTarget input slices hslices had
        let digest ← CtxRO.query ((), outerInput (sourceKey input) target.nonce target.context target.record.tag)
        pure (targetOpen c (sourceKey input) target digest))).run primitive := by
  rw [openInput_typed c input slices hslices had]
  rfl

/-- Forgetting only canonical opening instrumentation returns the exact source result and full shared cache. -/
theorem sourceOpening_cache_projection (c : Pqxdh.Crypto) (input : RawCtxWholeOwner.OpenInput)
    (target : CtxUnclaimedAcceptance.Target) (state : CanonicalState) :
    (fun result => (result.1, result.2.ctx.cache)) <$> sourceOpening c input target state =
      (simulateQ ctxRandomOracle (simulateQ (romAdapter c) (openInput input))).run state.ctx.cache := by
  simp [sourceOpening, afterOpening]

/-- A valid selected source opening inherits the actual shared-cache randomness cap. -/
theorem sourceOpening_uniform (c : Pqxdh.Crypto) (input : RawCtxWholeOwner.OpenInput)
    (slices : RawCtxFrameDecoding.Slices)
    (hslices : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices)
    (had : input.context.associatedData.length = 153) (state : CanonicalState) :
    (sourceOpening c input (selectedTarget input slices hslices had) state).IsTotalQueryBound 64 := by
  rw [sourceOpening_canonical c input slices hslices had
    (fun _ => some (selectedTarget input slices hslices had)) state rfl]
  exact canonicalRaw_uniform _ _ _ _ _

end BeaconcryptCore.Computational.RawCtxCanonicalOpening

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalOpening.typedOpen_target' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalOpening.typedOpen_target

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalOpening.sourceOpening_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalOpening.sourceOpening_canonical

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalOpening.selectedDecoder_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalOpening.selectedDecoder_source

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalOpening.sourceOpening_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalOpening.sourceOpening_selected

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalOpening.sourceOpening_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalOpening.sourceOpening_continuation

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalOpening.canonicalRaw_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalOpening.canonicalRaw_uniform

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalOpening.selectedTarget_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalOpening.selectedTarget_fields

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalOpening.sourceOpening_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalOpening.sourceOpening_interpretation

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalOpening.sourceOpening_cache_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalOpening.sourceOpening_cache_projection

/--
info: 'BeaconcryptCore.Computational.RawCtxCanonicalOpening.sourceOpening_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCanonicalOpening.sourceOpening_uniform
