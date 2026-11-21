-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceOwner
import BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation
/-! Typed source AEAD and hash replies preserve the full original primitive and platform poststates under narrow primitive output-width and length guarantees. The actual source plaintext is a bounded slice; no parser, wrapper, authentication or security conclusion is a premise. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceRepresentation
open BeaconcryptCore.Refinement
open BeaconcryptCore.Refinement.ProtocolComposition (concreteByte)
open PqxdhRefinement
variable {S Platform Value : Type}
abbrev M (S Platform : Type) := StateT S (StateT Platform ProbComp)

def sealed (reply : Option (Pqxdh.Bytes × Pqxdh.Bytes)) : RegistrationNativePlatformOrdinarySourceNative.Sealed :=
  RegistrationRecordPrimitives.sealedBytes reply

/-- Successful primitive ciphertext and tag survive their actual source Vec and tag16 representations. -/
theorem sealed_bytes (reply : Option (Pqxdh.Bytes × Pqxdh.Bytes))
    (width : ∀ body tag, reply = some (body, tag) → tag.length = 16)
    (fits : ∀ body tag, reply = some (body, tag) → body.length ≤ Usize.max) :
    Option.map (fun pair => (TranscriptAuthParts.absSlice pair.1, absBytes pair.2)) (sealed reply) = reply := by
  cases reply with
  | none => rfl
  | some pair =>
      rcases pair with ⟨body, tag⟩
      simp only [sealed, RegistrationRecordPrimitives.sealedBytes, dite_eq_left (width body tag rfl),
        RegistrationAuthenticationShared.openedBytes, dite_eq_left (fits body tag rfl)]
      change some ((body.map concreteByte).map absByte, (tag.map concreteByte).map absByte) = some (body, tag)
      simp [List.map_map, Function.comp_def]

structure Functional (implementation : QueryImpl RawCtxSourceSeal.SealSpec (M S Platform)) : Prop where
  hashWidth : ∀ input before after previous next bytes,
    ((some bytes, after), next) ∈ support (((implementation (.inr (.inl input))).run before).run previous) → bytes.length = 64
  sealWidth : ∀ input before after previous next body tag,
    ((some (body, tag), after), next) ∈ support (((implementation (.inl input)).run before).run previous) → tag.length = 16
  sealLength : ∀ input before after previous next body tag,
    ((some (body, tag), after), next) ∈ support (((implementation (.inl input)).run before).run previous) → body.length ≤ input.plaintext.length

def typed (implementation : QueryImpl RawCtxSourceSeal.SealSpec (M S Platform)) :
    QueryImpl RecordEffectsSendBridge.PrimitiveSpec (M S Platform)
  | .inl input => sealed <$> implementation (.inl input)
  | .inr (.inl bytes) => AdapterRecordNativeRepresentation.digest <$> implementation (.inr (.inl bytes))
  | .inr (.inr frame) => implementation (.inr (.inr frame))

def Fits : RawCtxSourceSeal.SealSpec.Domain → Prop
  | .inl input => input.plaintext.length ≤ Usize.max
  | .inr _ => True

/-- Representation retains the entire original operation and both shared state coordinates, even when a primitive returns None. -/
theorem query_native (implementation : QueryImpl RawCtxSourceSeal.SealSpec (M S Platform))
    (functional : Functional implementation) (query : RawCtxSourceSeal.SealSpec.Domain) (fits : Fits query) :
    (typed implementation ∘ₛ RecordEffectsSendBridge.modelAdapter) query = implementation query := by
  funext before previous
  change (((typed implementation ∘ₛ RecordEffectsSendBridge.modelAdapter) query).run before).run previous =
    ((implementation query).run before).run previous
  rcases query with input | (bytes | frame)
  · simp only [QueryImpl.apply_compose, RecordEffectsSendBridge.modelAdapter, simulateQ_map,
      simulateQ_spec_query, bind_pure_comp, typed, StateT.run_map, Functor.map_map]
    apply AdapterRecordNativeRepresentation.map_self_of_support
    rintro ⟨⟨reply, after⟩, next⟩ supported
    apply congrArg (fun value => ((value, after), next))
    apply sealed_bytes
    · intro body tag same
      change reply = some (body, tag) at same
      subst reply
      exact functional.sealWidth input before after previous next body tag supported
    · intro body tag same
      change reply = some (body, tag) at same
      subst reply
      exact (functional.sealLength input before after previous next body tag supported).trans fits
  · simp only [QueryImpl.apply_compose, RecordEffectsSendBridge.modelAdapter, simulateQ_map,
      simulateQ_spec_query, bind_pure_comp, typed, StateT.run_map, Functor.map_map]
    apply AdapterRecordNativeRepresentation.map_self_of_support
    rintro ⟨⟨reply, after⟩, next⟩ supported
    apply congrArg (fun value => ((value, after), next))
    apply AdapterRecordNativeRepresentation.digest_bytes
    intro digest same
    change reply = some digest at same
    subst reply
    exact functional.hashWidth bytes before after previous next digest supported
  · simp only [QueryImpl.apply_compose, RecordEffectsSendBridge.modelAdapter, simulateQ_spec_query, typed]

/-- Arbitrary adaptive continuation preserves the complete source/native joint distribution on represented requests. -/
theorem program_native (implementation : QueryImpl RawCtxSourceSeal.SealSpec (M S Platform))
    (functional : Functional implementation) (work : OracleComp RawCtxSourceSeal.SealSpec Value)
    (fits : work.AllQueriesSatisfy Fits) :
    simulateQ (typed implementation ∘ₛ RecordEffectsSendBridge.modelAdapter) work = simulateQ implementation work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at fits
      simp only [simulateQ_bind, simulateQ_spec_query]
      rw [query_native implementation functional query fits.1]
      exact bind_congr fun reply => ih reply (fits.2 reply)

private theorem seal_fits (input : RawCtxSourceSend.SealInput) (fits : input.context.plaintext.length ≤ Usize.max) :
    (RawCtxSourceSeal.sealInput input).AllQueriesSatisfy Fits := by
  rw [RawCtxSourceSeal.sealInput, allQueriesSatisfy_query_bind_iff]
  refine ⟨fits, fun reply => ?_⟩
  cases reply with
  | none => trivial
  | some pair =>
      rcases pair with ⟨body, tag⟩
      dsimp only
      split_ifs
      · rw [allQueriesSatisfy_query_bind_iff]
        refine ⟨trivial, fun digest => ?_⟩
        cases digest with
        | none => trivial
        | some commitment => exact (allQueriesSatisfy_query_iff _ _).mpr trivial
      · trivial
      · trivial

/-- The complete source sealing sequence uses only represented AEAD plaintexts; this derives its typed/untyped native equality without a parser-size premise. -/
theorem sealing_native (implementation : QueryImpl RawCtxSourceSeal.SealSpec (M S Platform))
    (functional : Functional implementation) (input : RawCtxSourceSend.SealInput)
    (fits : input.context.plaintext.length ≤ Usize.max) :
    simulateQ (typed implementation) (simulateQ RecordEffectsSendBridge.modelAdapter (RawCtxSourceSeal.sealInput input)) =
      simulateQ implementation (RawCtxSourceSeal.sealInput input) := by
  rw [← QueryImpl.simulateQ_compose]
  exact program_native implementation functional _ (seal_fits input fits)

def SendFits : RawCtxSourceSend.PrimitiveSpec.Domain → Prop
  | .inl _ => True
  | .inr input => input.context.plaintext.length ≤ Usize.max

private theorem send_fits (kernel : ratchet.concrete.ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext)
    (fits : context.plaintext.length ≤ Usize.max) :
    (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel context)).AllQueriesSatisfy SendFits := by
  by_cases exhausted : kernel.refined.control.send_sequence = core.num.U64.MAX
  · rw [RawCtxSourceSend.send_exhausted kernel context exhausted, simulateQ_pure]
    trivial
  · obtain ⟨pending, started, _entry, sameContext, _⟩ := RawCtxSourceSend.beginSend_fields kernel context exhausted
    rw [RawCtxSourceSend.send, started, RawCtxSourceSend.program, simulateQ_bind, simulateQ_spec_query]
    simp only [RawCtxSourceSend.adapter, simulateQ_bind, simulateQ_pure]
    apply allQueriesSatisfy_bind
    · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
    · intro response
      obtain ⟨stepped, _step, fields⟩ := RawCtxSourceSend.resumeSend_fields pending response
      apply allQueriesSatisfy_bind
      · apply allQueriesSatisfy_bind
        · apply (allQueriesSatisfy_query_iff _ _).mpr
          simpa only [SendFits, RawCtxSourceSend.arguments, fields, sameContext] using fits
        · intro reply
          trivial
      · intro reply
        trivial

private theorem owner_fits {Metadata : Type} (sender : U64) (plaintext : Pqxdh.Bytes)
    (fits : plaintext.length ≤ Usize.max) (owner : RawCtxWholeOwner.OwnerState Metadata) :
    ((RawCtxSourceSend.sendOwner sender plaintext).run owner).AllQueriesSatisfy SendFits := by
  unfold RawCtxSourceSend.sendOwner StateT.run
  split
  · trivial
  · apply allQueriesSatisfy_bind
    · exact send_fits _ _ fits
    · intro result
      trivial

def typedModel (kdf : beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest → M S Platform beaconcrypt_core.ratchet.RatchetKdfResponse)
    (implementation : QueryImpl RawCtxSourceSeal.SealSpec (M S Platform)) : QueryImpl RawCtxSourceSend.PrimitiveSpec (M S Platform)
  | .inl request => kdf request
  | .inr input => simulateQ (typed implementation) (simulateQ RecordEffectsSendBridge.modelAdapter (RawCtxSourceSeal.sealInput input))

def model (kdf : beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest → M S Platform beaconcrypt_core.ratchet.RatchetKdfResponse)
    (implementation : QueryImpl RawCtxSourceSeal.SealSpec (M S Platform)) : QueryImpl RawCtxSourceSend.PrimitiveSpec (M S Platform)
  | .inl request => kdf request
  | .inr input => simulateQ implementation (RawCtxSourceSeal.sealInput input)

private theorem send_program_native
    (kdf : beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest → M S Platform beaconcrypt_core.ratchet.RatchetKdfResponse)
    (implementation : QueryImpl RawCtxSourceSeal.SealSpec (M S Platform)) (functional : Functional implementation)
    (work : OracleComp RawCtxSourceSend.PrimitiveSpec Value) (fits : work.AllQueriesSatisfy SendFits) :
    simulateQ (typedModel kdf implementation) work = simulateQ (model kdf implementation) work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at fits
      simp only [simulateQ_bind, simulateQ_spec_query]
      have called : typedModel kdf implementation query = model kdf implementation query := by
        cases query with
        | inl request => rfl
        | inr input => exact sealing_native implementation functional input fits.1
      rw [called]
      exact bind_congr fun reply => ih reply (fits.2 reply)

/-- Every actual whole-owner source send has a represented plaintext, so typed primitive adaptation preserves its complete joint execution without a codec-size premise. -/
theorem owner_native
    (kdf : beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest → M S Platform beaconcrypt_core.ratchet.RatchetKdfResponse)
    (implementation : QueryImpl RawCtxSourceSeal.SealSpec (M S Platform)) (functional : Functional implementation)
    {Metadata : Type} (owner : RawCtxWholeOwner.OwnerState Metadata) (sender : U64) (plaintext : Slice U8) :
    simulateQ (typedModel kdf implementation) ((RawCtxSourceSend.sendOwner sender (TranscriptAuthParts.absSlice plaintext)).run owner) =
      simulateQ (model kdf implementation) ((RawCtxSourceSend.sendOwner sender (TranscriptAuthParts.absSlice plaintext)).run owner) := by
  apply send_program_native kdf implementation functional
  apply owner_fits
  simpa only [TranscriptAuthParts.absSlice, List.length_map] using plaintext.property

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceRepresentation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceRepresentation.sealed_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceRepresentation.sealed_bytes

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceRepresentation.query_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceRepresentation.query_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceRepresentation.program_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceRepresentation.program_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceRepresentation.sealing_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceRepresentation.sealing_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceRepresentation.owner_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceRepresentation.owner_native
