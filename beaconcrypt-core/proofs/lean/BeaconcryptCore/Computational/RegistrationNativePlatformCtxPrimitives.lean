-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxNativeFrame
/-! Native record CTX leaves use the same explicit shared-cache backend as EnvEffects. Both commitment directions expose their literal byte inputs, preserving optional outputs and full native call/draw accounting. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxPrimitives
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (Primitive)
open RegistrationNativePlatformCtxBackend (Spec coin hash)
variable {I KemSK Reader Response A : Type} {base : OracleSpec I}

noncomputable def program (setup : Setup base KemSK) (codec : Codec Reader Response) :
    QueryImpl RawCtxMixedOwner.NativeSpec (StateT Primitive (OracleComp Spec))
  | .inr (.inr (.inr (.inl bytes))) => fun before => do
      let reply ← hash bytes
      pure (some reply.1.toList, ({before.1 with uniform := before.1.uniform + reply.2, native := Function.update before.1.native .hash (before.1.native .hash + 1)}, before.2))
  | query => fun before => simulateQ coin ((PqxdhRecordLiftWorld.primitives setup codec query).run before)

abbrev Full := Primitive × RegistrationNativePlatformCtxBackend.State

def realize (before : Full) : Primitive := (before.1.1, before.2.1)

noncomputable def implementation (setup : Setup base KemSK) (codec : Codec Reader Response) :
    QueryImpl RawCtxMixedOwner.NativeSpec (StateT Full ProbComp) := fun query before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ RegistrationNativePlatformCtxBackend.implementation ((program setup codec query).run before.1)).run before.2

theorem nonhash (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (allowed : RegistrationNativePlatformCtxNativeFrame.NonHash query)
    (before : Full) :
    Prod.map id realize <$> (implementation setup codec query).run before =
      (PqxdhRecordLiftWorld.primitives setup codec query).run (realize before) := by
  have branch : (program setup codec query).run before.1 = simulateQ coin ((PqxdhRecordLiftWorld.primitives setup codec query).run before.1) := by
    rcases query with request | input | opening | bytes | frame
    all_goals first | rfl | exact False.elim allowed
  unfold implementation
  change Prod.map id realize <$> ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ RegistrationNativePlatformCtxBackend.implementation ((program setup codec query).run before.1)).run before.2) = _
  rw [branch, RegistrationNativePlatformCtxBackend.coins]
  simp only [StateT.run_lift, bind_pure_comp, Functor.map_map]
  exact RegistrationNativePlatformCtxNativeFrame.primitives setup codec query allowed before.1 before.2.1

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

theorem hashing (setup : Setup base KemSK) (codec : Codec Reader Response) (bytes : Pqxdh.Bytes) (before : Full) :
    Prod.map id realize <$> (implementation setup codec (.inr (.inr (.inr (.inl bytes))))).run before =
      (PqxdhRecordLiftWorld.primitives setup codec (.inr (.inr (.inr (.inl bytes))))).run (realize before) := by
  have shift := RegistrationNativePlatformCtxBackend.count_shift
    ((CtxRomAuth.ctxRandomOracle ((), bytes)).run before.2.1) before.1.1.uniform 0
  simp only [Nat.add_zero] at shift
  unfold implementation program RegistrationNativePlatformCtxBackend.hash PqxdhRecordLiftWorld.primitives PqxdhDeploymentNative.primitives
  simp only [realize, StateT.run, bind_pure_comp, Functor.map_map] at shift ⊢
  have original := RawCtxMixedShared.shared_hash setup.source.crypto codec.frameWrite
    (RawCtxSourceHkdf.kdfImpl setup.source) bytes ((), before.2.1)
  simp only [StateT.run] at original
  rw [original]
  simp only [bind_pure_comp, simulateQ_map, simulateQ_spec_query, RegistrationNativePlatformCtxBackend.implementation]
  simp only [state_map_apply, RegistrationNativePlatformCtxBackend.physical, StateT.run, bind_pure_comp, Functor.map_map]
  rw [← shift, Functor.map_map]
  rfl

theorem query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (request : RawCtxMixedOwner.NativeSpec.Domain) (before : Full) :
    Prod.map id realize <$> (implementation setup codec request).run before =
      (PqxdhRecordLiftWorld.primitives setup codec request).run (realize before) := by
  rcases request with request | input | opening | bytes | frame
  all_goals first | exact hashing setup codec _ before | apply nonhash; trivial

/-- Every native record primitive trace uses the same substitutable CTX backend and retains its full original reply/counter/cache distribution. -/
theorem complete (setup : Setup base KemSK) (codec : Codec Reader Response)
    (work : OracleComp RawCtxMixedOwner.NativeSpec A) (before : Full) :
    Prod.map id realize <$> (simulateQ (implementation setup codec) work).run before =
      (simulateQ (PqxdhRecordLiftWorld.primitives setup codec) work).run (realize before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ realize (query setup codec) work before
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxPrimitives

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxPrimitives.nonhash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxPrimitives.nonhash

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxPrimitives.hashing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxPrimitives.hashing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxPrimitives.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxPrimitives.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxPrimitives.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxPrimitives.complete
