-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryGate

/-! The lower ordinary-record client keeps native primitives private and exposes only capacity requests to the external allocator. The selected private writer executes once before its public reservation gate; its returned failure reaches the original controller before any ledger continuation. All native poststates and public allocator poststates remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryGateCompiler
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (Primitive)
variable {E Platform Value ι KemSK Reader Response : Type} {base : OracleSpec ι}

abbrev Spec (E : Type) := RawCtxMixedOwner.NativeSpec + (Nat →ₒ core.result.Result Unit E)

def compile (E : Type) : QueryImpl RawCtxMixedOwner.NativeSpec (OracleComp (Spec E))
  | .inr (.inr (.inr (.inr frame))) => do
      let output ← (Spec E).query (.inl (.inr (.inr (.inr (.inr frame)))))
      match output with
      | none => pure none
      | some bytes => do
          let result ← (Spec E).query (.inr bytes.length)
          match result with
          | .Err _ => pure none
          | .Ok _ => pure (some bytes)
  | query => (Spec E).query (.inl query)

noncomputable def implementation (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) :
    QueryImpl (Spec E) (StateT Primitive (StateT Platform ProbComp))
  | .inl query => fun before => StateT.lift ((PqxdhRecordLiftWorld.primitives setup (CborRawCanonicalBuild.canonical codec) query).run before)
  | .inr size => StateT.lift (reserve size)

private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m] (value : X) (before : S) :
    (pure value : StateT S m X) before = pure (value, before) := rfl
private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (StateT.lift work : StateT S m X) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := bind_pure_comp _ _

private theorem original_writer (setup : Setup base KemSK) (codec : Codec Reader Response)
    (frame : RawCtxReceive.DecodedFrame) (before : Primitive) :
    (PqxdhRecordLiftWorld.primitives setup (CborRawCanonicalBuild.canonical codec) (.inr (.inr (.inr (.inr frame))))).run before =
      pure (CborRawCanonicalBuild.canonicalWriter frame, RegistrationNativePlatformOrdinaryWorld.chargeWriter before) := by
  rfl

/-- Each actual dynamic primitive callback equals one private native callback plus its public capacity-only allocator macro. -/
theorem query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (request : RawCtxMixedOwner.NativeSpec.Domain) :
    simulateQ (implementation setup codec reserve) (compile E request) =
      RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve request := by
  rcases request with request | (sealed | (opened | (bytes | frame)))
  all_goals try (simp only [compile, simulateQ_spec_query, implementation]; rfl)
  funext before previous
  simp only [compile, simulateQ_bind, simulateQ_spec_query, implementation, bind_apply,
    lift_apply, original_writer, map_pure, pure_bind, pure_apply, RegistrationNativePlatformOrdinaryWorld.primitives]
  rw [RegistrationNativePlatformOrdinaryGate.writer_late reserve frame]
  cases current : CborRawCanonicalBuild.canonicalWriter frame with
  | none => simp only [simulateQ_pure, RegistrationNativePlatformOrdinaryGate.gate, pure_apply, pure_bind]
  | some output =>
      simp only [simulateQ_bind, simulateQ_spec_query, implementation,
        RegistrationNativePlatformOrdinaryGate.gate, bind_apply, lift_apply, map_apply, bind_map_left,
        bind_assoc, Prod.map, id_eq]
      apply bind_congr
      rintro ⟨result, next⟩
      cases result <;> simp only [simulateQ_pure, pure_apply, pure_bind]

/-- The complete actual private ordinary primitive execution is this capacity-only public-gate client, jointly retaining all native and external state. -/
theorem program (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : OracleComp RawCtxMixedOwner.NativeSpec Value) :
    simulateQ (implementation setup codec reserve) (simulateQ (compile E) work) =
      simulateQ (RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve) work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext request
  exact query setup codec reserve request

/-- Only a reached writer can request public allocation, at most once and after its private native callback. -/
theorem allocation_bound (request : RawCtxMixedOwner.NativeSpec.Domain) :
    (compile E request).IsQueryBoundP (fun query => query.isRight = true)
      (if RawCtxMixedOwner.callKind request = .writer then 1 else 0) := by
  rcases request with request | (sealed | (opened | (bytes | frame)))
  all_goals try (solve | simp [compile, RawCtxMixedOwner.callKind])
  rw [compile, isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (by simp), fun output => ?_⟩
  cases output with
  | none => simp
  | some bytes =>
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inr (by simp [RawCtxMixedOwner.callKind]), fun result => ?_⟩
      cases result <;> simp

/-- An adaptive private record programme makes no more public allocator calls than its reached source writer allowance. -/
theorem program_allocation_bound (work : OracleComp RawCtxMixedOwner.NativeSpec Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun request => RawCtxMixedOwner.callKind request = .writer) cap) :
    (simulateQ (compile E) work).IsQueryBoundP (fun query => query.isRight = true) cap := by
  apply bounded.simulateQ_of_step
  · intro request writer
    simpa only [writer, ite_true] using allocation_bound (E := E) request
  · intro request other
    simpa only [other, ite_false] using allocation_bound (E := E) request

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryGateCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryGateCompiler.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryGateCompiler.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryGateCompiler.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryGateCompiler.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryGateCompiler.allocation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryGateCompiler.allocation_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryGateCompiler.program_allocation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryGateCompiler.program_allocation_bound
