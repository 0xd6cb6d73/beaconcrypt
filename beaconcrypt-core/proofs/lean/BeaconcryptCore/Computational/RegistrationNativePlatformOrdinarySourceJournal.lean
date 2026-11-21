-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceWorld
/-! A reached writer records its exact frame beside the ordinary primitive state, including failed public allocation. Functional native representation is unchanged by the retained frame journal. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceJournal
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (Primitive)
open RegistrationNativePlatformOrdinarySourceRepresentation (M Functional typed)
open RegistrationNativePlatformOrdinaryLogged (logged framesAfter)
variable {Platform E I KemSK Reader Response : Type} {base : OracleSpec I}
abbrev State := Primitive × PqxdhRecordLiftLoggedAdapters.Frames
noncomputable def native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) :=
  logged (RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve)
noncomputable def implementation (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) :
    QueryImpl RawCtxSourceSeal.SealSpec (M State Platform) :=
  native setup codec reserve ∘ₛ RegistrationNativePlatformOrdinaryWorldSeal.inject
private theorem logged_run (backend : QueryImpl RawCtxMixedOwner.NativeSpec
    (StateT Primitive (StateT Platform ProbComp)))
    (query : RawCtxMixedOwner.NativeSpec.Domain) (before : State) :
    (RegistrationNativePlatformOrdinaryLogged.logged backend query).run before =
      (fun result => (result.1,(result.2,framesAfter query before.2))) <$>
        (backend query).run before.1 := rfl
private def nativeQuery : RawCtxSourceSeal.SealSpec.Domain → RawCtxMixedOwner.NativeSpec.Domain
  | .inl input => .inr (.inl input)
  | .inr (.inl bytes) => .inr (.inr (.inr (.inl bytes)))
  | .inr (.inr frame) => .inr (.inr (.inr (.inr frame)))
private theorem query_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (query : RawCtxSourceSeal.SealSpec.Domain) (before : State) (previous : Platform) :
    (((implementation setup codec reserve query).run before).run previous) =
      (fun result => ((result.1.1,(result.1.2,
        framesAfter (nativeQuery query) before.2)),result.2)) <$>
        (((RegistrationNativePlatformOrdinarySourceWorld.implementation setup codec reserve query).run before.1).run previous) := by
  rcases query with input | (bytes | frame)
  all_goals simp only [implementation, RegistrationNativePlatformOrdinarySourceWorld.implementation,
    QueryImpl.apply_compose, RegistrationNativePlatformOrdinaryWorldSeal.inject,
    simulateQ_spec_query, native]
  all_goals rw [logged_run, StateT.run_map]
  all_goals simp only [nativeQuery]
  all_goals rfl
private theorem original_support (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (query : RawCtxSourceSeal.SealSpec.Domain) (before after : State) (previous next : Platform)
    (reply : RawCtxSourceSeal.SealSpec.Range query)
    (supported : ((reply,after),next) ∈ support (((implementation setup codec reserve query).run before).run previous)) :
    ((reply,after.1),next) ∈ support
      (((RegistrationNativePlatformOrdinarySourceWorld.implementation setup codec reserve query).run before.1).run previous) := by
  rw [query_source, support_map] at supported
  obtain ⟨result,supported,same⟩ := supported
  have fields := congrArg (fun value => ((value.1.1,value.1.2.1),value.2)) same
  dsimp only at fields
  rw [← fields]
  simpa only [Prod.mk.eta] using supported
/-- Actual primitive widths and ciphertext bounds survive retention of every failed writer frame. -/
theorem functional (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto) :
    Functional (implementation setup codec reserve) := by
  have original := RegistrationNativePlatformOrdinarySourceWorld.functional setup codec reserve length
  constructor
  · intro input before after previous next digest supported
    exact original.hashWidth input before.1 after.1 previous next digest
      (original_support setup codec reserve _ before after previous next _ supported)
  · intro input before after previous next body tag supported
    exact original.sealWidth input before.1 after.1 previous next body tag
      (original_support setup codec reserve _ before after previous next _ supported)
  · intro input before after previous next body tag supported
    exact original.sealLength input before.1 after.1 previous next body tag
      (original_support setup codec reserve _ before after previous next _ supported)
noncomputable def kdf (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (request : ratchet.SymmetricRatchetKdfRequest) : M State Platform ratchet.RatchetKdfResponse :=
  native setup codec reserve (.inl request)

noncomputable def aead (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (input : RawCtxSourceSeal.AeadInput) :
    M State Platform RegistrationNativePlatformOrdinarySourceNative.Sealed :=
  RegistrationNativePlatformOrdinarySourceRepresentation.sealed <$> implementation setup codec reserve (.inl input)

noncomputable def hash (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (bytes : Pqxdh.Bytes) :
    M State Platform (Option (Std.Array U8 64#usize)) :=
  AdapterRecordNativeRepresentation.digest <$> implementation setup codec reserve (.inr (.inl bytes))

def receipt (frame : RawCtxReceive.DecodedFrame) : M State Platform Unit := fun before =>
  pure ((), (RegistrationNativePlatformOrdinaryWorld.chargeWriter before.1,before.2++[frame]))

def reserveNative (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (size : Nat) : M State Platform (core.result.Result Unit E) := StateT.lift (reserve size)

private theorem bind_apply {m : Type → Type} [Monad m] {S A B : Type}
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem pure_apply {m : Type → Type} [Monad m] {S A : Type} (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value,before) := rfl
private theorem map_apply {m : Type → Type} [Monad m] [LawfulMonad m] {S A B : Type}
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = (fun result => (f result.1,result.2)) <$> work before := by
  exact StateT.run_map f work before
private theorem lift_apply {m : Type → Type} [Monad m] {S A : Type} (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (do let value ← work; pure (value,before)) := rfl
private theorem writer_lift (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (frame : RawCtxReceive.DecodedFrame) :
    RegistrationNativePlatformOrdinaryWriter.write (reserveNative reserve) frame =
      (StateT.lift (RegistrationNativePlatformOrdinaryWriter.write reserve frame) : M State Platform _) := by
  unfold RegistrationNativePlatformOrdinaryWriter.write
  cases RegistrationNativePlatformOrdinaryWriter.capacity frame with
  | none =>
      funext before
      simp only [pure_apply, lift_apply, pure_bind]
  | some size =>
      funext before
      change ((do
        let reserved ← reserveNative reserve size
        match reserved with
        | .Err _ => pure none
        | .Ok _ => pure (some (CborTransport.render frame)) : M State Platform _).run before) = _
      simp only [StateT.run_bind, reserveNative, StateT.run_lift, lift_apply, bind_assoc, pure_bind]
      apply bind_congr
      intro reserved
      cases reserved <;> simp only [StateT.run_pure, pure_bind]

theorem writer_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (frame : RawCtxReceive.DecodedFrame) :
    RegistrationNativePlatformOrdinarySourceNative.afterAttempt (receipt frame)
      (RegistrationNativePlatformOrdinaryWriter.write (reserveNative reserve) frame) =
        implementation setup codec reserve (.inr (.inr frame)) := by
  rw [writer_lift]
  funext before previous
  simp only [RegistrationNativePlatformOrdinarySourceNative.afterAttempt, implementation, QueryImpl.apply_compose,
    RegistrationNativePlatformOrdinaryWorldSeal.inject, simulateQ_spec_query,
    RegistrationNativePlatformOrdinaryWorld.primitives, bind_apply, lift_apply, pure_apply,
    receipt, native, RegistrationNativePlatformOrdinaryLogged.logged, framesAfter, bind_assoc, pure_bind]
  simp only [StateT.run, map_apply, bind_pure_comp, Functor.map_map]


end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceJournal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceJournal.functional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceJournal.functional

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceJournal.writer_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceJournal.writer_source
