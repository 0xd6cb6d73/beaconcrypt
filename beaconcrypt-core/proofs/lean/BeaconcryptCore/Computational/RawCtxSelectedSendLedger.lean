import BeaconcryptCore.Computational.RawCtxSelectedSendTrace
import BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer

/-!
All actual nonsealing component calls preserve the selected nonce ledger. This includes adaptive raw validation, malformed decoding, public hashes, uniform requests and known-key operations whose bytes may alias the selected key. These laws carry the checked original-send occurrence history through the rest of the common component program.
-/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedSendLedger
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxSharedHash AdaptiveCtxSharedModes
open AdaptiveCtxDynamicKnownKeys RawCtxSelectedSendTrace

/-- The literal real raw/public callback never changes the selected seal ledger, including every decoder rejection and optional opening result. -/
theorem local_nonseal (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (notSeal : ¬ AdaptiveCtxQueryBounds.SourceSeal query)
    (entry : AdaptiveCtxSharedHash.Local) (cache : CtxRO.QueryCache)
    (result : (ReceiveSpec.Range query × AdaptiveCtxSharedHash.Local) × CtxRO.QueryCache)
    (supported : result ∈ support ((simulateQ hashImpl
      ((AdaptiveCtxSharedHash.localImpl decode c key query).run entry)).run cache)) :
    result.1.2.usedNonces = entry.usedNonces := by
  rcases query with (coin | (hash | input)) | raw
  · simp only [AdaptiveCtxSharedHash.localImpl, StateT.run, bind_pure_comp, simulateQ_map,
      simulateQ_spec_query] at supported
    change result ∈ support ((fun answer => ((answer.1, entry), answer.2)) <$>
      (hashImpl (.inl coin)).run cache) at supported
    simp only [support_map] at supported
    obtain ⟨answer, _, rfl⟩ := supported
    rfl
  · change result ∈ support ((simulateQ hashImpl (do
      let answer ← HashSpec.query (.inr hash)
      pure (answer, {entry with publicInputs := hash.2 :: entry.publicInputs}))).run cache) at supported
    simp only [bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
    obtain ⟨answer, _, rfl⟩ := supported
    rfl
  · exact False.elim (notSeal trivial)
  · change result ∈ support ((simulateQ hashImpl (AdaptiveCtxSharedHash.localRaw decode c key raw entry)).run cache) at supported
    cases parsed : decode raw with
    | none =>
        simp only [AdaptiveCtxSharedHash.localRaw, parsed, simulateQ_pure, StateT.run_pure] at supported
        subst result
        rfl
    | some target =>
        simp only [AdaptiveCtxSharedHash.localRaw, parsed, bind_pure_comp, simulateQ_map,
          simulateQ_spec_query, StateT.run_map, support_map] at supported
        obtain ⟨answer, _, rfl⟩ := supported
        rfl

/-- Every actual dynamic call outside the selected seal interface preserves the selected nonce ledger, including arbitrary known-key aliases. -/
theorem source_nonseal (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : Spec.Domain)
    (notSeal : ¬ AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal query)
    (before : SourceState) (result : Spec.Range query × SourceState)
    (supported : result ∈ support ((sourceImpl true decode c key query).run before)) :
    result.2.selected.1.usedNonces = before.selected.1.usedNonces := by
  cases query with
  | inr known =>
      simp only [sourceImpl, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨answer, _, rfl⟩ := supported
      rfl
  | inl query =>
      simp only [sourceImpl, AdaptiveCtxSharedModes.localImpl, ite_true, StateT.run,
        bind_pure_comp, simulateQ_map] at supported
      change result ∈ support ((fun answer => (answer.1.1,
          ({before with selected := answer.1.2, cache := answer.2} : SourceState))) <$>
        (((fun answer => (answer.1, (answer.2, before.selected.2))) <$>
          simulateQ hashImpl (AdaptiveCtxSharedHash.localImpl decode c key query before.selected.1))
            before.cache)) at supported
      rw [support_map] at supported
      obtain ⟨mapped, mappedSupported, rfl⟩ := supported
      have baseSupported : mapped ∈ support ((fun answer =>
          ((fun value => (value.1, (value.2, before.selected.2))) answer.1, answer.2)) <$>
        (simulateQ hashImpl (AdaptiveCtxSharedHash.localImpl decode c key query before.selected.1)).run
          before.cache) := by
        exact Eq.mp (congrArg (fun distribution => mapped ∈ support distribution)
          (StateT.run_map (fun value => (value.1, (value.2, before.selected.2)))
            (simulateQ hashImpl (AdaptiveCtxSharedHash.localImpl decode c key query before.selected.1))
            before.cache)) mappedSupported
      rw [support_map] at baseSupported
      obtain ⟨answer, reached, rfl⟩ := baseSupported
      exact local_nonseal decode c key query notSeal before.selected.1 before.cache answer reached

set_option backward.isDefEq.respectTransparency false in
/-- An arbitrary complete adaptive program with zero selected sealing queries preserves the actual selected nonce ledger. Its raw, hash, known-key and randomness work still executes. -/
theorem program_nonseal {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (client : OracleComp Spec Result)
    (bounded : client.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0)
    (before : SourceState) (result : Result × SourceState)
    (supported : result ∈ support ((simulateQ (sourceImpl true decode c key) client).run before)) :
    result.2.selected.1.usedNonces = before.selected.1.usedNonces := by
  induction client using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have quiet : ¬ AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal query := by
        simpa using bounded.1
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, reached, tail⟩ := supported
      exact (ih reply.1 (by simpa using bounded.2 reply.1) reply.2 result tail).trans
        (source_nonseal decode c key query quiet before reply reached)

/-- Actual nonsealing source work transports the earlier original-send evidence without a caller-supplied nonce-history equality. -/
theorem tracked_nonseal {Owner Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (client : OracleComp Spec Result)
    (bounded : client.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0)
    (before : SourceState) (result : Result × SourceState) (history : List (Occurrence Owner))
    (tracked : Tracked before history)
    (supported : result ∈ support ((simulateQ (sourceImpl true decode c key) client).run before)) :
    Tracked result.2 history := by
  intro value used
  exact tracked value (by simpa only [program_nonseal decode c key client bounded before result supported] using used)

/-- The actual scalar raw-opening service preserves the selected-send ledger for every optional plaintext, without extra parse, context or successful-opening premises. -/
theorem opening_nonseal (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Aeneas.Std.U64)
    (pending : RawCtxInterpretedOpening.Opening beaconcrypt_core.ratchet.RatchetChain
      beaconcrypt_core.ratchet.RatchetChain RawCtxSelectedMessageKey.Slot RawCtxWholeOwner.OpenContext)
    (before : SourceState)
    (result : CoreModels.core.option.Option RawCtxWholeOwner.Decrypted × SourceState)
    (supported : result ∈ support ((simulateQ (sourceImpl true decode c key)
      (RawCtxSelectedOpenConsumer.service slot read expected pending)).run before)) :
    result.2.selected.1.usedNonces = before.selected.1.usedNonces :=
  program_nonseal decode c key (RawCtxSelectedOpenConsumer.service slot read expected pending)
    (RawCtxSelectedOpenConsumer.service_other slot read expected pending).1 before result supported

end BeaconcryptCore.Computational.RawCtxSelectedSendLedger

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendLedger.local_nonseal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendLedger.local_nonseal

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendLedger.source_nonseal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendLedger.source_nonseal

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendLedger.program_nonseal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendLedger.program_nonseal

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendLedger.tracked_nonseal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendLedger.tracked_nonseal

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendLedger.opening_nonseal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendLedger.opening_nonseal
