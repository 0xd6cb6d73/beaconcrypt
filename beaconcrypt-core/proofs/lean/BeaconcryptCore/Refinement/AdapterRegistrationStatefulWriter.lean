-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterRegistrationWriterRequestExtraction
import BeaconcryptCore.Refinement.AdapterWireStatefulWriter

/-! The two actual runtime registration writers use their original length checks and the original allocation helper. The source request program records the complete schema value, both serializers' returned mutable slice and each reservation outcome. Arbitrary platform state and later callbacks are threaded through one interpretation. -/

open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter
open AdapterRegistrationWriterRequestMonad
open AdapterRecordRequestMonad (LiftRust liftRust)

@[instance_reducible] def rustOperations [codec : RegistrationWriterPrimitive.Operations]
    [allocator : AdapterWirePrimitive.Operations] : Operations allocator.ReserveError RustM where
  reserve := alloc.vec.Vec.try_reserve_exact
  encodeInit := beaconcrypt_parse.encode_init
  encodeResponse := beaconcrypt_parse.encode_response

theorem init_specializes [RegistrationWriterPrimitive.Operations]
    [allocator : AdapterWirePrimitive.Operations] (packet : beaconcrypt_parse.transport.initkex) :
    @AdapterRegistrationWriterRequestExtraction.encodeInit allocator.ReserveError RustM _ _
      rustOperations packet = beaconcrypt_registration_writer.wire.encode_init packet := by
  rfl

theorem response_specializes [RegistrationWriterPrimitive.Operations]
    [allocator : AdapterWirePrimitive.Operations] (packet : beaconcrypt_parse.transport.kexresponse) :
    @AdapterRegistrationWriterRequestExtraction.encodeResponse allocator.ReserveError RustM _ _
      rustOperations packet = beaconcrypt_registration_writer.wire.encode_response packet := by
  rfl

def interpret {E A ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl (Spec E) (OracleComp base)) (work : Program E A) :
    OracleComp base (RustM A) := simulateQ impl work.run

@[simp] theorem interpret_pure {E A ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl (Spec E) (OracleComp base)) (value : A) :
    interpret impl (pure value) = pure (.ok value) := rfl

@[simp] theorem interpret_lift {E A ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl (Spec E) (OracleComp base)) (value : RustM A) :
    interpret impl (liftRust value) = pure value := rfl

theorem interpret_bind {E A B ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl (Spec E) (OracleComp base))
    (work : Program E A) (next : A → Program E B) :
    interpret impl (work >>= next) = (do
      let result ← interpret impl work
      match result with
      | .ok value => interpret impl (next value)
      | .fail error => pure (.fail error)
      | .div => pure .div) := by
  change simulateQ impl (do
    let result ← work.run
    match result with
    | .ok value => (next value).run
    | .fail error => pure (.fail error)
    | .div => pure .div) = _
  rw [simulateQ_bind]
  refine bind_congr fun result => ?_
  cases result <;> rfl

@[simp] theorem interpret_query {E ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl (Spec E) (OracleComp base)) (request : Request) :
    interpret impl (Program.query request) = impl request :=
  simulateQ_spec_query impl request

def init {E σ ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (packet : beaconcrypt_parse.transport.initkex) :
    StateT σ (OracleComp base) (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  simulateQ impl (AdapterRegistrationWriterRequestExtraction.encodeInit (E := E) (m := Program E) packet).run

def response {E σ ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (packet : beaconcrypt_parse.transport.kexresponse) :
    StateT σ (OracleComp base) (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  simulateQ impl (AdapterRegistrationWriterRequestExtraction.encodeResponse (E := E) (m := Program E) packet).run

theorem init_joint {E σ ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (packet : beaconcrypt_parse.transport.initkex) (before : σ) :
    (init impl packet).run before =
      (simulateQ impl (AdapterRegistrationWriterRequestExtraction.encodeInit (E := E) (m := Program E) packet).run).run before := rfl

theorem response_joint {E σ ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (packet : beaconcrypt_parse.transport.kexresponse) (before : σ) :
    (response impl packet).run before =
      (simulateQ impl (AdapterRegistrationWriterRequestExtraction.encodeResponse (E := E) (m := Program E) packet).run).run before := rfl

theorem init_continuation {E σ ι Output : Type} {base : OracleSpec ι}
    (impl : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (packet : beaconcrypt_parse.transport.initkex)
    (next : RustM (core.option.Option (alloc.vec.Vec U8)) → StateT σ (OracleComp base) Output) (before : σ) :
    ((do let output ← init impl packet; next output).run before) = (do
      let output ← (init impl packet).run before
      (next output.1).run output.2) := by
  rw [StateT.run_bind]

theorem response_continuation {E σ ι Output : Type} {base : OracleSpec ι}
    (impl : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (packet : beaconcrypt_parse.transport.kexresponse)
    (next : RustM (core.option.Option (alloc.vec.Vec U8)) → StateT σ (OracleComp base) Output) (before : σ) :
    ((do let output ← response impl packet; next output).run before) = (do
      let output ← (response impl packet).run before
      (next output.1).run output.2) := by
  rw [StateT.run_bind]

theorem init_source [RegistrationWriterPrimitive.Operations]
    [allocator : AdapterWirePrimitive.Operations] {σ ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl (Spec allocator.ReserveError) (StateT σ (OracleComp base)))
    (packet : beaconcrypt_parse.transport.initkex) (before : σ) :
    (@AdapterRegistrationWriterRequestExtraction.encodeInit allocator.ReserveError RustM _ _
      rustOperations packet = beaconcrypt_registration_writer.wire.encode_init packet) ∧
    ((init impl packet).run before =
      (simulateQ impl (AdapterRegistrationWriterRequestExtraction.encodeInit
        (E := allocator.ReserveError) (m := Program allocator.ReserveError) packet).run).run before) :=
  ⟨init_specializes packet, init_joint impl packet before⟩

theorem response_source [RegistrationWriterPrimitive.Operations]
    [allocator : AdapterWirePrimitive.Operations] {σ ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl (Spec allocator.ReserveError) (StateT σ (OracleComp base)))
    (packet : beaconcrypt_parse.transport.kexresponse) (before : σ) :
    (@AdapterRegistrationWriterRequestExtraction.encodeResponse allocator.ReserveError RustM _ _
      rustOperations packet = beaconcrypt_registration_writer.wire.encode_response packet) ∧
    ((response impl packet).run before =
      (simulateQ impl (AdapterRegistrationWriterRequestExtraction.encodeResponse
        (E := allocator.ReserveError) (m := Program allocator.ReserveError) packet).run).run before) :=
  ⟨response_specializes packet, response_joint impl packet before⟩

end BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter

/-- info: 'BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.init_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.init_source
/-- info: 'BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.response_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.response_source

/-- info: 'BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.init_specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.init_specializes

/-- info: 'BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.response_specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.response_specializes

/-- info: 'BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.interpret_pure' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.interpret_pure

/-- info: 'BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.interpret_lift' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.interpret_lift

/-- info: 'BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.interpret_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.interpret_bind

/-- info: 'BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.interpret_query' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.interpret_query

/-- info: 'BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.init_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.init_joint

/-- info: 'BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.response_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.response_joint

/-- info: 'BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.init_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.init_continuation

/-- info: 'BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.response_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRegistrationStatefulWriter.response_continuation
