import BeaconcryptCore.Computational.RawCtxSharedSourceOpening
import BeaconcryptCore.Computational.RawCtxInterpretedArguments
import BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds

/-!
An actual prepared receive capability can retain unavailable record keys as finite labels while obtaining its optional plaintext from the existing shared CTX challenger. The compiler calls that challenger at the selected label with the original raw bytes, wraps only its returned plaintext, and invokes the extracted cached/future finish. Missing material and RustM failure/divergence do not invent a plaintext or silently become ordinary rejection. Optional failure retains the original kernel; success performs the original publication.

The compiler contains no material interpretation or secret key. Interpretation of the resulting private kernel belongs to the challenger-side correspondence theorem. Every reached opening is counted, including AEAD/commitment failure; earlier raw rejection and KDF calls retain their distinct source ledgers. The module does not establish independent evolving keys or sealing nonce freshness and therefore makes no end-to-end security claim.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer
open CtxRomAuth AdaptiveCtxSharedKeySelection RawCtxInterpretedOpening

/-- API metadata is obtained from the actual source request; plaintext is only challenger supplied. -/
def apiReply (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (reply : Option Pqxdh.Bytes) : core.option.Option RawCtxWholeOwner.Decrypted :=
  match reply with
  | none => .None
  | some plaintext => .Some ⟨plaintext, context.frame.sender, sequence⟩

/-- A key-free opening callback forwards the original bytes at the selected private label. -/
noncomputable def call {count : Nat} (index : Fin (count + 1)) (sequence : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) : OracleComp (SourceSpec count)
      (core.option.Option RawCtxWholeOwner.Decrypted) := do
  let reply ← (SourceSpec count).query ⟨index, .inr context.raw⟩
  pure (apiReply sequence context reply)

/-- The source getter and finish choreography, parameterized only by unavailable-key labels. -/
noncomputable def opening {count : Nat}
    (pending : Opening RatchetChain RatchetChain (Fin (count + 1)) RawCtxWholeOwner.OpenContext) :=
  run call pending

/-- Failure from the actual primitive remains rejection, without substituted plaintext. -/
theorem api_none (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    apiReply sequence context none = .None := rfl

/-- The actual successful reply retains exactly the prepared sequence, decoded sender and challenger plaintext. -/
theorem api_some (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) (plaintext : Pqxdh.Bytes) :
    apiReply sequence context (some plaintext) = .Some ⟨plaintext, context.frame.sender, sequence⟩ := rfl

/-- The compiler spends exactly its one raw-call allowance, without public hash, seal or uniform requests. -/
theorem call_bound {count : Nat} (index : Fin (count + 1)) (sequence : Std.U64)
    (context : RawCtxWholeOwner.OpenContext)
    (classify : (SourceSpec count).Domain → Prop) [DecidablePred classify] :
    (call index sequence context).IsQueryBoundP classify
      (if classify ⟨index, .inr context.raw⟩ then 1 else 0) := by
  simpa only [call, bind_pure_comp, isQueryBoundP_map_iff] using
    (isQueryBoundP_query_iff classify ⟨index, .inr context.raw⟩ _).2
      (by intro hit; simp [hit])

/-- Every represented prepared capability makes at most one component call, including missing/mistagged slots. -/
theorem opening_bound {count : Nat}
    (pending : Opening RatchetChain RatchetChain (Fin (count + 1)) RawCtxWholeOwner.OpenContext)
    (classify : (SourceSpec count).Domain → Prop) [DecidablePred classify] (bound : Nat)
    (allowed : ∀ (index : Fin (count + 1)) (context : RawCtxWholeOwner.OpenContext), (if classify ⟨index, .inr context.raw⟩ then 1 else 0) ≤ bound) :
    (opening pending).IsQueryBoundP classify bound := by
  unfold opening run
  cases found : material pending with
  | fail error => trivial
  | div => trivial
  | ok selected =>
    cases selected with
    | none => trivial
    | some index =>
      cases prepared : RawCtxInterpretedOpening.sequence pending with
      | fail error => trivial
      | div => trivial
      | ok sequence =>
        simpa only [bindResult, bind_pure_comp, isQueryBoundP_map_iff] using
          (call_bound index sequence pending.context classify).mono (allowed index pending.context)

/-- No primitive result is requested when the extracted slot lookup has no material. -/
theorem opening_missing {count : Nat}
    (pending : Opening RatchetChain RatchetChain (Fin (count + 1)) RawCtxWholeOwner.OpenContext)
    (missing : material pending = ok .None) :
    opening pending = pure (finish pending (core.option.Option.None : core.option.Option RawCtxWholeOwner.Decrypted)) := by
  simp only [opening, run, missing, bindResult]

/-- Actual present material forwards its unchanged raw request and finishes with the returned option. -/
theorem opening_present {count : Nat}
    (pending : Opening RatchetChain RatchetChain (Fin (count + 1)) RawCtxWholeOwner.OpenContext)
    (index : Fin (count + 1)) (sequence : Std.U64)
    (selected : material pending = ok (.Some index))
    (prepared : RawCtxInterpretedOpening.sequence pending = ok sequence) :
    opening pending = (do
      let reply ← (SourceSpec count).query ⟨index, .inr pending.context.raw⟩
      pure (finish pending (apiReply sequence pending.context reply))) := by
  simp only [opening, run, selected, prepared, bindResult, call, bind_assoc, pure_bind]

/-- The concrete compiler has one raw allowance and no public-hash, sealing or explicit-coin calls. -/
theorem opening_bills {count : Nat}
    (pending : Opening RatchetChain RatchetChain (Fin (count + 1)) RawCtxWholeOwner.OpenContext) :
    (opening pending).IsQueryBoundP
      (AdaptiveCtxSharedMultiKeyBounds.SourceClass AdaptiveCtxReceive.IsRawQuery) 1 ∧
    (opening pending).IsQueryBoundP
      (AdaptiveCtxSharedMultiKeyBounds.SourceClass AdaptiveCtxQueryBounds.SourceHash) 0 ∧
    (opening pending).IsQueryBoundP
      (AdaptiveCtxSharedMultiKeyBounds.SourceClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
    (opening pending).IsQueryBoundP
      (AdaptiveCtxSharedMultiKeyBounds.SourceClass AdaptiveCtxQueryBounds.SourceUniform) 0 := by
  refine ⟨opening_bound pending _ 1 ?_, opening_bound pending _ 0 ?_,
    opening_bound pending _ 0 ?_, opening_bound pending _ 0 ?_⟩
  all_goals intros; simp [AdaptiveCtxSharedMultiKeyBounds.SourceClass, AdaptiveCtxReceive.IsRawQuery,
    AdaptiveCtxQueryBounds.SourceHash, AdaptiveCtxQueryBounds.SourceSeal, AdaptiveCtxQueryBounds.SourceUniform]

/-- Kernel interpretation occurs only in the challenger-side comparison after the key-free source finish. -/
def interpretResult {count : Nat} (interpret : Fin (count + 1) → RatchetMaterial)
    (result : RustM (ratchet.refined.RefinedRatchet RatchetChain RatchetChain (Fin (count + 1)) ×
      core.option.Option RawCtxWholeOwner.Decrypted)) : RustM (ConcreteRatchetKernel ×
        core.option.Option RawCtxWholeOwner.Decrypted) :=
  (fun published => (ConcreteRatchetKernel.mk (RawCtxMaterialInterpretation.mapRefined interpret published.1), published.2)) <$> result

/-- All optional replies use the actual native cached/future finish with complete kernel interpretation. -/
theorem finish_source {count : Nat} (interpret : Fin (count + 1) → RatchetMaterial)
    (pending : Opening RatchetChain RatchetChain (Fin (count + 1)) RawCtxWholeOwner.OpenContext)
    (sequence : Std.U64) (reply : Option Pqxdh.Bytes) :
    ReceiveOpen.finish (toNative (mapOpening interpret pending)) (apiReply sequence pending.context reply) =
      interpretResult interpret (finish pending (apiReply sequence pending.context reply)) := by
  rw [native_finish, finish_map]
  simp only [interpretResult, Functor.map_map]

set_option backward.isDefEq.respectTransparency false in
/-- The key-free compiler consumes a reached source capability and reconstructs the actual optional publication, retaining the entire shared family state. The assumptions are exact source getter/context facts, not security or simulation premises. -/
theorem present_source {count : Nat} (interpret : Fin (count + 1) → RatchetMaterial)
    (pending : Opening RatchetChain RatchetChain (Fin (count + 1)) RawCtxWholeOwner.OpenContext)
    (index : Fin (count + 1)) (sequence : Std.U64)
    (selected : material pending = ok (.Some index))
    (prepared : RawCtxInterpretedOpening.sequence pending = ok sequence)
    (nonce : Fin (count + 1) → CtxNonce) (expected : Fin (count + 1) → Std.U64)
    (ad : Fin (count + 1) → Pqxdh.Bytes) (read : RawCtxReceive.FrameDecoder)
    (c : Pqxdh.Crypto) (keys : Fin (count + 1) → CtxKey) (state : SourceState count)
    (keySelected : keys index = RawCtxSourceOpen.sourceKey ⟨interpret index, sequence, pending.context⟩)
    (nonceSelected : nonce index = RawCtxSourceOpen.sourceNonce ⟨interpret index, sequence, pending.context⟩)
    (adSelected : ad index = pending.context.associatedData)
    (nonempty : pending.context.raw.isEmpty = false)
    (decoded : read pending.context.raw = some pending.context.frame)
    (valid : RawCtxReceive.ValidFrame (expected index) pending.context.associatedData pending.context.frame)
    (sequenceSelected : sequence = pending.context.frame.sequence)
    (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload pending.context.frame.payload = some slices) :
    (fun result => (interpretResult interpret result.1, result.2)) <$>
      (simulateQ (sourceImpl (fun _ => true)
        (fun i => RawCtxKeyFreeDecoder.decoder (nonce i) (expected i) (ad i) read) c keys)
        (opening pending)).run state = (do
      let result ← RawCtxCanonicalOpening.sourceOpening c ⟨interpret index, sequence, pending.context⟩
        (RawCtxCanonicalOpening.selectedTarget ⟨interpret index, sequence, pending.context⟩ slices parsed valid.2.2)
        (AdaptiveCtxSharedModes.canonicalProjection (state.1 index, state.2))
      pure (ReceiveOpen.finish (toNative (mapOpening interpret pending)) (apiReply sequence pending.context result.1),
        RawCtxSharedSourceOpening.retainFamily index state result.2)) := by
  rw [opening_present pending index sequence selected prepared]
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [RawCtxSharedSourceOpening.reached_source index nonce expected ad read c keys
    ⟨interpret index, sequence, pending.context⟩ state keySelected nonceSelected adSelected
    nonempty decoded valid sequenceSelected slices parsed]
  simp only [map_bind, map_pure, bind_map_left, finish_source]

set_option backward.isDefEq.respectTransparency false in
/-- The real family challenger pays for every digest miss; key erasure does not make its sampling free. -/
theorem family_raw_uniform {count : Nat} (index : Fin (count + 1))
    (decode : Fin (count + 1) → AdaptiveCtxReceive.RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin (count + 1) → CtxKey) (raw : Pqxdh.Bytes) (state : SourceState count) :
    ((sourceImpl (fun _ => true) decode c keys ⟨index, .inr raw⟩).run state).IsTotalQueryBound 64 := by
  rw [RawCtxSharedSourceOpening.family_complete]
  simpa only [IsTotalQueryBound, isQueryBound_map_iff, AdaptiveCtxCanonical.canonicalImpl, StateT.run] using
    RawCtxCanonicalOpening.canonicalRaw_uniform (decode index) c (keys index) raw
      (AdaptiveCtxSharedModes.canonicalProjection (state.1 index, state.2))

end BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer.api_none' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer.api_none

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer.api_some' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer.api_some

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer.call_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer.call_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer.opening_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer.opening_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer.opening_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer.opening_missing

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer.opening_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer.opening_present

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer.opening_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer.opening_bills

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer.finish_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer.present_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer.present_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer.family_raw_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer.family_raw_uniform
