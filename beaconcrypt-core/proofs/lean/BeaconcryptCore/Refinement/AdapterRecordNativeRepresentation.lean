-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterRecordStatefulReceive
import BeaconcryptCore.Computational.RegistrationAuthenticationShared
import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-! Typed source hash/AEAD replies preserve the original primitive state. Fixed hash width and successful AEAD plaintext length are primitive functional contracts. The actual extracted AEAD request owns a bounded slice, so its plaintext fits a source Vec whenever the primitive does not enlarge it. No parser law, security conclusion, independent cache or whole-program correspondence is postulated. -/

open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation
open BeaconcryptCore.Computational
open PqxdhRefinement
open BeaconcryptCore.Refinement.ProtocolComposition (concreteByte)

abbrev SourceSpec := AdapterRecordStatefulReceive.NativeSpec

def digest (reply : Option Pqxdh.Bytes) : Option (Array Std.U8 64#usize) :=
  reply.bind fun bytes => if width : bytes.length = 64 then
    some ⟨bytes.map concreteByte, by simpa only [List.length_map, Std.UScalar.ofNatCore_val_eq] using width⟩
  else none

def plaintext (reply : Option Pqxdh.Bytes) : Option (alloc.vec.Vec Std.U8) :=
  reply.bind fun bytes => if fits : bytes.length ≤ Std.Usize.max then
    some ⟨bytes.map concreteByte, by simpa only [List.length_map] using fits⟩
  else none

/-- Fixed-width successful hash bytes survive their actual source-array representation. -/
theorem digest_bytes (reply : Option Pqxdh.Bytes)
    (width : ∀ bytes, reply = some bytes → bytes.length = 64) :
    Option.map absBytes (digest reply) = reply := by
  cases reply with
  | none => rfl
  | some bytes =>
      simp only [digest, Option.bind_some, dite_eq_left (width bytes rfl)]
      change some ((bytes.map concreteByte).map absByte) = some bytes
      simp [List.map_map, Function.comp_def]

/-- Every representable optional plaintext survives conversion into the source Vec. -/
theorem plaintext_bytes (reply : Option Pqxdh.Bytes)
    (fits : ∀ bytes, reply = some bytes → bytes.length ≤ Std.Usize.max) :
    Option.map (fun value => value.val.map absByte) (plaintext reply) = reply := by
  cases reply with
  | none => rfl
  | some bytes =>
      simp only [plaintext, Option.bind_some, dite_eq_left (fits bytes rfl)]
      change some ((bytes.map concreteByte).map absByte) = some bytes
      simp [List.map_map, Function.comp_def]

/-- Functional primitive output contracts; no authentication or secrecy event appears here. -/
structure Functional {PrimitiveState : Type}
    (impl : QueryImpl RawCtxSourceOpen.NativeSpec (StateT PrimitiveState ProbComp)) : Prop where
  hashWidth : ∀ input before after bytes,
    (some bytes, after) ∈ support ((impl (.inr (.inl input))).run before) → bytes.length = 64
  aeadLength : ∀ input before after bytes,
    (some bytes, after) ∈ support ((impl (.inr (.inr input))).run before) →
      bytes.length ≤ input.ciphertext.length

/-- Query replies are converted after the complete original primitive operation, keeping its exact poststate even on optional failure. -/
def typed {PrimitiveState : Type}
    (impl : QueryImpl RawCtxSourceOpen.NativeSpec (StateT PrimitiveState ProbComp)) :
    QueryImpl SourceSpec (StateT PrimitiveState ProbComp)
  | .inl request => impl (.inl request)
  | .inr (.inl input) => digest <$> impl (.inr (.inl input))
  | .inr (.inr input) => plaintext <$> impl (.inr (.inr input))

def Fits : RawCtxSourceOpen.NativeSpec.Domain → Prop
  | .inl _ | .inr (.inl _) => True
  | .inr (.inr input) => input.ciphertext.length ≤ Std.Usize.max

/-- The actual source AEAD argument is an already represented slice, so this bound needs no decoder premise. -/
theorem request_fits (request : record.AeadRequest) :
    (RecordEffectsReceiveProgram.aeadQuery request).ciphertext.length ≤ Std.Usize.max := by
  simpa only [RecordEffectsReceiveProgram.aeadQuery, RawCtxNativeFramePrelude.sliceBytes,
    List.length_map] using request.ciphertext.property

theorem map_self_of_support {Value : Type} (work : ProbComp Value) (change : Value → Value)
    (same : ∀ value, value ∈ support work → change value = value) : change <$> work = work := by
  rw [map_eq_bind_pure_comp]
  conv_rhs => rw [← bind_pure work]
  exact OracleComp.bind_congr_of_forall_mem_support work (fun value reached => congrArg pure (same value reached))

/-- Typed reply adaptation preserves the entire original primitive operation on every representable request. -/
theorem query_native {PrimitiveState : Type}
    (impl : QueryImpl RawCtxSourceOpen.NativeSpec (StateT PrimitiveState ProbComp))
    (functional : Functional impl) (query : RawCtxSourceOpen.NativeSpec.Domain)
    (fits : Fits query) (before : PrimitiveState) :
    ((typed impl ∘ₛ AdapterRecordStatefulReceive.abstractNative) query).run before =
      (impl query).run before := by
  rcases query with request | (input | input)
  · simp only [QueryImpl.apply_compose, AdapterRecordStatefulReceive.abstractNative,
      simulateQ_spec_query, typed]
  · simp only [QueryImpl.apply_compose, AdapterRecordStatefulReceive.abstractNative,
      simulateQ_map, simulateQ_spec_query, typed, StateT.run_map, Functor.map_map]
    apply map_self_of_support
    rintro ⟨reply, after⟩ reached
    apply congrArg (fun value => (value, after))
    apply digest_bytes
    intro bytes same
    change reply = some bytes at same
    subst reply
    exact functional.hashWidth input before after bytes reached
  · simp only [QueryImpl.apply_compose, AdapterRecordStatefulReceive.abstractNative,
      simulateQ_map, simulateQ_spec_query, typed, StateT.run_map, Functor.map_map]
    apply map_self_of_support
    rintro ⟨reply, after⟩ reached
    apply congrArg (fun value => (value, after))
    apply plaintext_bytes
    intro bytes same
    change reply = some bytes at same
    subst reply
    exact (functional.aeadLength input before after bytes reached).trans fits

def OpenFits : RawCtxSourceOpen.OpenSpec.Domain → Prop
  | .inl _ => True
  | .inr input => input.ciphertext.length ≤ Std.Usize.max

/-- Pure extracted core continuations cannot introduce an unrepresented primitive request. -/
theorem bindResult_queries {ι Input Output : Type} {spec : OracleSpec ι}
    (result : RustM Input) (next : Input → OracleComp spec (RustM Output)) (allowed : spec.Domain → Prop)
    (safe : ∀ value, (next value).AllQueriesSatisfy allowed) :
    (RawCtxInterpretedOpening.bindResult result next).AllQueriesSatisfy allowed := by
  cases result with
  | ok value => exact safe value
  | fail error => trivial
  | div => trivial

/-- The concrete AEAD getter supplies a bounded ciphertext slice for every primitive reply history. -/
theorem aead_queries (pending : record_effects.RecordReceiveAead) :
    (RecordEffectsReceiveProgram.executeAead pending).AllQueriesSatisfy OpenFits := by
  unfold RecordEffectsReceiveProgram.executeAead
  apply bindResult_queries
  intro request
  cases request with
  | none =>
      simp only [pure_bind]
      apply bindResult_queries
      intro result
      trivial
  | some request =>
      rw [allQueriesSatisfy_query_bind_iff]
      refine ⟨request_fits request, fun plaintext => ?_⟩
      apply bindResult_queries
      intro result
      trivial

/-- The commitment phase preserves the same bound through optional hash failure, exact comparison and the retained continuation. -/
theorem commitment_queries (erased : Array Std.U8 357#usize)
    (pending : record_effects.RecordReceiveCommitment) :
    (RecordEffectsReceiveProgram.executeCommitment erased pending).AllQueriesSatisfy OpenFits := by
  unfold RecordEffectsReceiveProgram.executeCommitment
  apply bindResult_queries
  intro transcript
  apply bindResult_queries
  intro bytes
  apply allQueriesSatisfy_bind
  · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
  · intro digest
    apply bindResult_queries
    intro borrowed
    apply bindResult_queries
    intro bytesBorrowed
    apply bindResult_queries
    intro matched
    apply bindResult_queries
    intro next
    cases next with
    | Rejected _ | KdfRequested _ | CommitmentRequested _ => trivial
    | AeadRequested pending => exact aead_queries pending

/-- Embedding the opening requests retains their proven source representability. -/
theorem openLift_queries {Value : Type} (work : OracleComp RawCtxSourceOpen.OpenSpec Value)
    (safe : work.AllQueriesSatisfy OpenFits) :
    (simulateQ RawCtxSourceOpen.openLift work).AllQueriesSatisfy Fits := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at safe
      rw [simulateQ_bind, simulateQ_spec_query]
      apply allQueriesSatisfy_bind
      · cases query with
        | inl input => simp [RawCtxSourceOpen.openLift, Fits]
        | inr input => simpa [RawCtxSourceOpen.openLift, Fits, OpenFits] using safe.1
      · intro reply
        exact ih reply (safe.2 reply)

/-- All possible queries of the complete extracted effect program fit source representations, including repeated KDF continuations and optional failures. -/
theorem execute_queries (erased : Array Std.U8 357#usize)
    (effect : record_effects.RecordReceiveEffect) :
    (RecordEffectsReceiveProgram.execute erased effect).AllQueriesSatisfy Fits := by
  generalize depthEq : RecordEffectsReceiveRank.rank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
      cases effect with
      | Rejected kernel => simp only [RecordEffectsReceiveProgram.execute, allQueriesSatisfy_pure]
      | AeadRequested pending =>
          simpa only [RecordEffectsReceiveProgram.execute] using openLift_queries _ (aead_queries pending)
      | CommitmentRequested pending =>
          simpa only [RecordEffectsReceiveProgram.execute] using openLift_queries _ (commitment_queries erased pending)
      | KdfRequested pending =>
          rw [RecordEffectsReceiveProgram.execute_kdf, allQueriesSatisfy_query_bind_iff]
          refine ⟨trivial, fun response => ?_⟩
          obtain ⟨next, resumed⟩ :=
            BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveKdf_resume_total pending response
          simp only [resumed, RawCtxInterpretedOpening.bindResult]
          exact ih _ (by simpa only [depthEq] using
            RecordEffectsReceiveRank.resume_decreasing pending response next resumed) next rfl

/-- Every native operation and its complete state are equal after typed source adaptation on an admitted program. -/
theorem program_native {PrimitiveState Value : Type}
    (impl : QueryImpl RawCtxSourceOpen.NativeSpec (StateT PrimitiveState ProbComp))
    (functional : Functional impl) (work : OracleComp RawCtxSourceOpen.NativeSpec Value)
    (safe : work.AllQueriesSatisfy Fits) (before : PrimitiveState) :
    (simulateQ (typed impl ∘ₛ AdapterRecordStatefulReceive.abstractNative) work).run before =
      (simulateQ impl work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at safe
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [query_native impl functional query safe.1 before]
      exact bind_congr fun result => ih result.1 (safe.2 result.1) result.2

/-- The actual lifted receive loop runs on the original complete shared primitive state under only fixed hash width and AEAD output-length functional contracts. -/
theorem controller_native {PrimitiveState : Type}
    (impl : QueryImpl RawCtxSourceOpen.NativeSpec (StateT PrimitiveState ProbComp))
    (functional : Functional impl) (erased : Array Std.U8 357#usize)
    (effect : record_effects.RecordReceiveEffect) (before : PrimitiveState) :
    (simulateQ (typed impl) ((fun result => AdapterRecordReceive.decodeResult <$> result) <$>
      AdapterRecordStatefulReceive.interpret erased
        (AdapterRecordStatefulReceive.drive (RecordEffectsReceiveRank.rank effect + 2) effect))).run before =
      (simulateQ impl (RecordEffectsReceiveProgram.execute erased effect)).run before := by
  calc
    _ = (simulateQ (typed impl) (simulateQ AdapterRecordStatefulReceive.abstractNative
        (RecordEffectsReceiveProgram.execute erased effect))).run before :=
      (AdapterRecordStatefulReceive.source_stateful (typed impl) erased effect before).2
    _ = _ := by
      rw [← QueryImpl.simulateQ_compose]
      exact program_native impl functional _ (execute_queries erased effect) before

/-- The source-selected actual controller and core admission interpreted on the original primitive state. -/
def receive {PrimitiveState : Type}
    (impl : QueryImpl RawCtxSourceOpen.NativeSpec (StateT PrimitiveState ProbComp))
    (erased : Array Std.U8 357#usize) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (sequence : Std.U64) (payload : Slice Std.U8) (ad : Array Std.U8 281#usize) (sender : Std.U64) :=
  simulateQ (typed impl) ((fun result => AdapterRecordReceive.decodeResult <$> result) <$>
    AdapterRecordStatefulReceive.interpret erased
      (AdapterRecordStatefulReceive.receive kernel sequence payload ad sender))

/-- The entire actual receive entrypoint preserves the full original kernel/result and primitive state, including malformed admission and every optional primitive failure. -/
theorem receive_native {PrimitiveState : Type}
    (impl : QueryImpl RawCtxSourceOpen.NativeSpec (StateT PrimitiveState ProbComp))
    (functional : Functional impl) (erased : Array Std.U8 357#usize)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (sequence : Std.U64)
    (payload : Slice Std.U8) (ad : Array Std.U8 281#usize) (sender : Std.U64)
    (before : PrimitiveState) :
    (receive impl erased kernel sequence payload ad sender).run before =
      (simulateQ impl
        (RecordEffectsReceiveProgram.receive erased kernel sequence payload ad sender)).run before := by
  obtain ⟨effect, admitted⟩ := BeaconcryptCore.PanicFreedom.RecordEffects.begin_record_receive_total
    kernel sequence payload ad sender
  simp only [receive, AdapterRecordStatefulReceive.receive, AdapterRecordStatefulReceive.interpret_bind,
    AdapterRecordStatefulReceive.interpret_lift, admitted, pure_bind,
    RecordEffectsReceiveProgram.receive, RawCtxInterpretedOpening.bindResult]
  exact controller_native impl functional erased effect before

/-- Later native callbacks execute from the identical joint result and full primitive poststate. -/
theorem receive_continuation {PrimitiveState Output : Type}
    (impl : QueryImpl RawCtxSourceOpen.NativeSpec (StateT PrimitiveState ProbComp))
    (functional : Functional impl) (erased : Array Std.U8 357#usize)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (sequence : Std.U64)
    (payload : Slice Std.U8) (ad : Array Std.U8 281#usize) (sender : Std.U64)
    (later : RustM RecordEffectsReceiveProgram.Result → StateT PrimitiveState ProbComp Output)
    (before : PrimitiveState) :
    (do
      let result ← receive impl erased kernel sequence payload ad sender
      later result).run before =
    (do
      let result ← simulateQ impl (RecordEffectsReceiveProgram.receive erased kernel sequence payload ad sender)
      later result).run before := by
  simp only [StateT.run_bind]
  rw [receive_native impl functional]

end BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.digest_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.digest_bytes

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.plaintext_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.plaintext_bytes

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.request_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.request_fits

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.map_self_of_support' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.map_self_of_support

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.query_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.query_native

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.bindResult_queries' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.bindResult_queries

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.aead_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.aead_queries

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.commitment_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.commitment_queries

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.openLift_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.openLift_queries

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.execute_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.execute_queries

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.program_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.program_native

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.controller_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.controller_native

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.receive_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.receive_native

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.receive_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.receive_continuation
