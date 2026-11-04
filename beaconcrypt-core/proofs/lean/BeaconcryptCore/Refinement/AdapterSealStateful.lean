-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterSealRequestExtraction
import BeaconcryptCore.Refinement.AdapterSealSourceJoin

/-! Kernel-checked specialization of the complete original detached-seal dispatcher and arbitrary shared-state interpretation of its exact request program. The allocator receives only its current pre-extension vector and capacity. Native AEAD receives its own plaintext, AD, nonce and key. Optional rejection, Rust failure and divergence retain the reached interpreter poststate and are not collapsed into one another. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.AdapterSealStateful
open AdapterSealRequestMonad
variable [primitives : AdapterSealPrimitive.Operations]

abbrev Output := core.option.Option (alloc.vec.Vec U8 × Array U8 16#usize)

@[instance_reducible] def rustOperations [allocator : AdapterWirePrimitive.Operations] :
    Operations allocator.ReserveError RustM where
  reserve := alloc.vec.Vec.try_reserve_exact
  aead := beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.encrypt_detached

theorem rust_specializes [allocator : AdapterWirePrimitive.Operations]
    (other : AdapterSealJoinCallbacks.Operations) (request : beaconcrypt_core.record_effects.AeadSealRequest) :
    @AdapterSealRequestExtraction.execute primitives allocator.ReserveError RustM _ _ rustOperations request =
      @beaconcrypt_seal.ratchet.execute_seal_request primitives (AdapterSealSourceJoin.sourceCallbacks other) request := by
  rfl

def interpret {E A ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (OracleComp base)) (work : Program E A) :
    OracleComp base (RustM A) := simulateQ implementation work.run

@[simp] theorem interpret_pure {E A ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (OracleComp base)) (value : A) :
    interpret implementation (pure value) = pure (.ok value) := rfl

@[simp] theorem interpret_lift {E A ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (OracleComp base)) (value : RustM A) :
    interpret implementation (AdapterRecordRequestMonad.liftRust value) = pure value := rfl

theorem interpret_bind {E A B ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (OracleComp base))
    (work : Program E A) (next : A → Program E B) :
    interpret implementation (work >>= next) = (do
      let result ← interpret implementation work
      match result with
      | .ok value => interpret implementation (next value)
      | .fail error => pure (.fail error)
      | .div => pure .div) := by
  change simulateQ implementation (do
    let result ← work.run
    match result with
    | .ok value => (next value).run
    | .fail error => pure (.fail error)
    | .div => pure .div) = _
  rw [simulateQ_bind]
  refine bind_congr fun result => ?_
  cases result <;> rfl

@[simp] theorem interpret_query {E ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (OracleComp base)) (request : Request) :
    interpret implementation (Program.query request) = implementation request :=
  simulateQ_spec_query implementation request

def execute {E σ ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (request : beaconcrypt_core.record_effects.AeadSealRequest) :
    StateT σ (OracleComp base) (RustM Output) :=
  simulateQ implementation (AdapterSealRequestExtraction.execute
    (E := E) (m := Program E) request).run

theorem execute_joint {E σ ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (request : beaconcrypt_core.record_effects.AeadSealRequest) (before : σ) :
    (execute implementation request).run before =
      (simulateQ implementation (AdapterSealRequestExtraction.execute
        (E := E) (m := Program E) request).run).run before := rfl

theorem execute_continuation {E σ ι Value : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (request : beaconcrypt_core.record_effects.AeadSealRequest)
    (next : RustM Output → StateT σ (OracleComp base) Value) (before : σ) :
    ((do let result ← execute implementation request; next result).run before) = (do
      let result ← (execute implementation request).run before
      (next result.1).run result.2) := by
  rw [StateT.run_bind]

theorem source [allocator : AdapterWirePrimitive.Operations]
    {σ ι : Type} {base : OracleSpec ι}
    (other : AdapterSealJoinCallbacks.Operations)
    (implementation : QueryImpl (Spec allocator.ReserveError) (StateT σ (OracleComp base)))
    (request : beaconcrypt_core.record_effects.AeadSealRequest) (before : σ) :
    (@AdapterSealRequestExtraction.execute primitives allocator.ReserveError RustM _ _ rustOperations request =
      @beaconcrypt_seal.ratchet.execute_seal_request primitives
        (AdapterSealSourceJoin.sourceCallbacks other) request) ∧
    ((execute implementation request).run before =
      (simulateQ implementation (AdapterSealRequestExtraction.execute
        (E := allocator.ReserveError) (m := Program allocator.ReserveError) request).run).run before) :=
  ⟨rust_specializes other request, execute_joint implementation request before⟩

end BeaconcryptCore.Refinement.AdapterSealStateful

/-- info: 'BeaconcryptCore.Refinement.AdapterSealStateful.rust_specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealStateful.rust_specializes

/-- info: 'BeaconcryptCore.Refinement.AdapterSealStateful.interpret_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealStateful.interpret_pure

/-- info: 'BeaconcryptCore.Refinement.AdapterSealStateful.interpret_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealStateful.interpret_lift

/-- info: 'BeaconcryptCore.Refinement.AdapterSealStateful.interpret_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealStateful.interpret_bind

/-- info: 'BeaconcryptCore.Refinement.AdapterSealStateful.interpret_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealStateful.interpret_query

/-- info: 'BeaconcryptCore.Refinement.AdapterSealStateful.execute_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealStateful.execute_joint

/-- info: 'BeaconcryptCore.Refinement.AdapterSealStateful.execute_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealStateful.execute_continuation

/-- info: 'BeaconcryptCore.Refinement.AdapterSealStateful.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealStateful.source
