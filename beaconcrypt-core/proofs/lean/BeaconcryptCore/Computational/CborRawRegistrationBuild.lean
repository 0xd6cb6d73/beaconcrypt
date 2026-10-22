-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRegistrationCodec
import BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl
import BeaconcryptCore.Computational.RawCtxSourcePublication

/-! Current registration sealing appends C, tag16 and commitment64 directly, without invoking the optional ordinary-frame encoder. The raw callback below preserves the actual optional AEAD/hash effects and their complete state. Its registration-only codec sends that protected payload to the unchanged optional outer response writer. The fixed-codec source14 compiler and its physical build correspondence require a separate join. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRegistrationBuild
open PqxdhServerAuthExperiment (Setup Codec Checks)
variable {ι KemSK Reader Response PrimitiveState Result : Type} {baseSpec : OracleSpec ι}

/-- The actual raw registration branch has no frame-writing capability. -/
abbrev RawSealSpec :=
  (RawCtxSourceSeal.AeadInput →ₒ Option (Pqxdh.Bytes × Pqxdh.Bytes)) +
    (Pqxdh.Bytes →ₒ Option Pqxdh.Bytes)

/-- Source order retains every optional primitive result, then returns the assembled protected bytes. -/
def rawSeal (input : RawCtxSourceSend.SealInput) : OracleComp RawSealSpec (Option Pqxdh.Bytes) := do
  let sealed ← RawSealSpec.query (.inl (RawCtxSourceSeal.aeadInput input))
  match sealed with
  | none => pure none
  | some (body, tag) =>
      if input.context.associatedData.length = 153 then
        if tag.length = 16 then do
          let digest ← RawSealSpec.query (.inr (RawCtxSourceSeal.hashInput input tag))
          match digest with
          | none => pure none
          | some commitment => pure (some (body ++ tag ++ commitment))
        else pure none
      else pure none

/-- Payload projection is pure; the recoverable ordinary-frame allocator is absent. -/
def rawWriter : RawCtxMixedShared.Writer := fun frame => some frame.payload

def eraseWriter : QueryImpl RawCtxSourceSeal.SealSpec (OracleComp RawSealSpec)
  | .inl input => RawSealSpec.query (.inl input)
  | .inr (.inl bytes) => RawSealSpec.query (.inr bytes)
  | .inr (.inr frame) => pure (rawWriter frame)

/-- Eliminating frame writing preserves the complete optional raw-seal program, before any primitive interpretation. -/
theorem raw_seal_exact (input : RawCtxSourceSend.SealInput) :
    simulateQ eraseWriter (RawCtxSourceSeal.sealInput input) = rawSeal input := by
  simp only [RawCtxSourceSeal.sealInput, rawSeal, simulateQ_bind, simulateQ_spec_query,
    eraseWriter, RawCtxSourceSeal.frame]
  apply bind_congr
  rintro (_ | ⟨body, tag⟩)
  all_goals simp only [simulateQ_pure]
  split_ifs
  all_goals simp only [simulateQ_pure, simulateQ_bind, simulateQ_spec_query, eraseWriter]
  apply bind_congr
  rintro (_ | commitment) <;>
    simp only [simulateQ_pure, simulateQ_spec_query, eraseWriter, rawWriter]

/-- Arbitrary stateful optional AEAD/hash effects survive removal of the unused frame-writing capability. -/
theorem raw_seal_run {κ : Type} {target : OracleSpec κ}
    (implementation : QueryImpl RawSealSpec (StateT PrimitiveState (OracleComp target)))
    (input : RawCtxSourceSend.SealInput) (state : PrimitiveState) :
    (simulateQ (implementation ∘ₛ eraseWriter) (RawCtxSourceSeal.sealInput input)).run state =
      (simulateQ implementation (rawSeal input)).run state := by
  rw [QueryImpl.simulateQ_compose, raw_seal_exact]

/-- Render the source-selected metadata with the raw protected payload as proof data. -/
def renderPayload (input : RawCtxSourceSend.SealInput) (payload : Pqxdh.Bytes) : Pqxdh.Bytes :=
  CborTransport.render ⟨input.sequence, input.context.senderId, payload⟩

def renderAdapter : QueryImpl RawCtxSourceSeal.SealSpec (OracleComp RawSealSpec)
  | .inl input => RawSealSpec.query (.inl input)
  | .inr (.inl bytes) => RawSealSpec.query (.inr bytes)
  | .inr (.inr frame) => pure (some (CborTransport.render frame))

/-- Pure virtual framing changes only returned representation, with identical optional primitive effects. -/
theorem raw_seal_render (input : RawCtxSourceSend.SealInput) :
    simulateQ renderAdapter (RawCtxSourceSeal.sealInput input) =
      Option.map (renderPayload input) <$> rawSeal input := by
  simp only [RawCtxSourceSeal.sealInput, rawSeal, simulateQ_bind, simulateQ_spec_query,
    renderAdapter, map_bind]
  apply bind_congr
  rintro (_ | ⟨body, tag⟩)
  all_goals simp only [simulateQ_pure, map_pure, Option.map_none]
  split_ifs
  all_goals simp only [simulateQ_pure, map_pure, Option.map_none, simulateQ_bind,
    simulateQ_spec_query, renderAdapter, map_bind]
  apply bind_congr
  rintro (_ | commitment) <;>
    simp only [simulateQ_pure, simulateQ_spec_query, renderAdapter, map_pure,
      Option.map_none, Option.map_some, renderPayload, RawCtxSourceSeal.frame]

/-- Arbitrary interpretation preserves the pure virtual representation bridge and the full reached primitive state. -/
theorem raw_render_run {κ : Type} {target : OracleSpec κ}
    (implementation : QueryImpl RawSealSpec (StateT PrimitiveState (OracleComp target)))
    (input : RawCtxSourceSend.SealInput) (state : PrimitiveState) :
    (simulateQ (implementation ∘ₛ renderAdapter) (RawCtxSourceSeal.sealInput input)).run state =
      (fun result => (Option.map (renderPayload input) result.1, result.2)) <$>
        (simulateQ implementation (rawSeal input)).run state := by
  rw [QueryImpl.simulateQ_compose, raw_seal_render, simulateQ_map, StateT.run_map]

/-- The raw callback uses the existing functional CTX seal and the same entire shared cache, with no frame allocator. -/
theorem shared_raw_seal {Auxiliary : Type} (crypto : Pqxdh.Crypto)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (input : RawCtxSourceSend.SealInput) (valid : input.context.associatedData.length = 153)
    (auxiliary : Auxiliary) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (simulateQ (RawCtxCanonicalSeal.sharedImpl crypto rawWriter kdf)
      (RawCtxSourceSeal.sealInput input)).run (auxiliary, cache) = (do
      let result ← (simulateQ CtxRomAuth.ctxRandomOracle
        (CtxRomAuth.ctxSeal crypto (RawCtxCanonicalSeal.sourceKey input)
          (RawCtxCanonicalSeal.sourceInput input valid))).run cache
      pure (some result.1.encode, (auxiliary, result.2))) := by
  rw [RawCtxCanonicalSeal.shared_seal]
  rfl

/-- Sequence-one raw sealing has the same pure virtual representation used by registration opening. -/
theorem render_registration (input : RawCtxSourceSend.SealInput) (first : input.sequence = 1#u64)
    (payload : Pqxdh.Bytes) :
    renderPayload input payload = CborRegistrationCodec.wrap input.context.senderId payload := by
  simp only [renderPayload, CborRegistrationCodec.wrap, CborTransport.registrationFrame, first]

/-- Complete native response admission also admits the pure virtual representation of its raw protected payload. -/
theorem render_admitted (input : RawCtxSourceSend.SealInput) (first : input.sequence = 1#u64)
    (payload : Pqxdh.Bytes) (assigned : Nat)
    (admitted : CborSizing.responseLen payload.length assigned ≤ CborSizing.maxMessageSize) :
    (renderPayload input payload).length ≤ CborSizing.maxMessageSize := by
  rw [render_registration input first payload]
  exact CborTransport.registration_render_fits input.context.senderId payload assigned admitted

/-- Registration changes no outer allocation, identity-check, erasure or response-writing callback. -/
theorem auxiliary_unchanged (setup : Setup baseSpec KemSK) (wire : Codec Reader Response) (checks : Checks)
    (query : PqxdhServerRegistrationPublication.AuxSpec.Domain) :
    PqxdhServerAuthExperiment.tailImpl setup (CborRegistrationCodec.raw wire) checks (.inr query) =
      PqxdhServerAuthExperiment.tailImpl setup wire checks (.inr query) := by
  cases query <;> rfl

/-- The complete supplied-root builder after transport admission uses raw inner protection and the native optional outer writer. -/
noncomputable def build (setup : Setup baseSpec KemSK) (wire : Codec Reader Response) (checks : Checks)
    (pending : pqxdh.PendingServerRegistration) (root : PqxdhSecretInputKdf.RootOutput)
    (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (primitive : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    ProbComp ((Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) ×
      RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :=
  (fun result => (PqxdhServerAuthExperiment.settle server result.1, result.2)) <$>
    (simulateQ (PqxdhServerAuthExperiment.tailImpl setup (CborRegistrationCodec.raw wire) checks)
      (PqxdhServerRegistrationPublication.build setup.source pending root payload () server)).run primitive

/-- Changing the ordinary frame encoder cannot change a raw registration build or any reached state. -/
theorem build_writer_irrelevant (setup : Setup baseSpec KemSK) (wire : Codec Reader Response) (checks : Checks)
    (writer : RawCtxMixedShared.Writer) (pending : pqxdh.PendingServerRegistration)
    (root : PqxdhSecretInputKdf.RootOutput) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (primitive : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    build setup { wire with frameWrite := writer } checks pending root payload server primitive =
      build setup wire checks pending root payload server primitive := rfl

/-- A rejected outer response retains all reached sealing/cache/log effects and publishes no peer or control update. -/
theorem outer_none (setup : Setup baseSpec KemSK) (wire : Codec Reader Response) (checks : Checks)
    (failed : ∀ fields, wire.write2 fields = none)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (primitive : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (simulateQ (PqxdhServerAuthExperiment.tailImpl setup (CborRegistrationCodec.raw wire) checks)
      (PqxdhServerRegistrationPublication.afterInitialization candidate authenticated kernel () server)).run primitive = (do
      let sent ← (simulateQ (PqxdhServerAuthExperiment.tailImpl setup (CborRegistrationCodec.raw wire) checks)
        (simulateQ PqxdhServerRegistrationPublication.sendLift (simulateQ RawCtxSourceSend.adapter
          (RawCtxSourceSend.send kernel (PqxdhServerRegistrationPublication.firstContext candidate authenticated))))).run primitive
      pure ((none, server), sent.2)) := by
  simp only [PqxdhServerRegistrationPublication.afterInitialization, simulateQ_bind, StateT.run_bind]
  apply bind_congr
  intro sent
  simp only [simulateQ_spec_query, PqxdhServerAuthNegativeControl.tailImpl_aux,
    PqxdhServerAuthExperiment.tailAux, StateT.run_pure, pure_bind]
  cases sent.1.2 <;> simp only [simulateQ_pure, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    StateT.run_pure, PqxdhServerAuthNegativeControl.tailImpl_aux, PqxdhServerAuthExperiment.tailAux,
    CborRegistrationCodec.raw, failed, pure_bind]

end BeaconcryptCore.Computational.CborRawRegistrationBuild

/-- info: 'BeaconcryptCore.Computational.CborRawRegistrationBuild.raw_seal_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRegistrationBuild.raw_seal_exact
/-- info: 'BeaconcryptCore.Computational.CborRawRegistrationBuild.raw_seal_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRegistrationBuild.raw_seal_run
/-- info: 'BeaconcryptCore.Computational.CborRawRegistrationBuild.raw_seal_render' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRegistrationBuild.raw_seal_render
/-- info: 'BeaconcryptCore.Computational.CborRawRegistrationBuild.raw_render_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRegistrationBuild.raw_render_run
/-- info: 'BeaconcryptCore.Computational.CborRawRegistrationBuild.shared_raw_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRegistrationBuild.shared_raw_seal
/-- info: 'BeaconcryptCore.Computational.CborRawRegistrationBuild.render_registration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRegistrationBuild.render_registration
/-- info: 'BeaconcryptCore.Computational.CborRawRegistrationBuild.render_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRegistrationBuild.render_admitted
/-- info: 'BeaconcryptCore.Computational.CborRawRegistrationBuild.auxiliary_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRegistrationBuild.auxiliary_unchanged
/-- info: 'BeaconcryptCore.Computational.CborRawRegistrationBuild.build_writer_irrelevant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRegistrationBuild.build_writer_irrelevant
/-- info: 'BeaconcryptCore.Computational.CborRawRegistrationBuild.outer_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRegistrationBuild.outer_none
