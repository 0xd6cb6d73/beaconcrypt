-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySealGate
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryGateCompiler

/-! Actual ordinary World sealing expands the source-selected private AEAD, shared CTX hash and source writer. Its public capacity gate may follow that whole private seal, retaining the exact source primitive state on every optional result. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldSeal
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (Primitive)
open RegistrationNativePlatformOrdinarySendGate (liftState)
open RegistrationNativePlatformOrdinaryGate (gate)
variable {Platform E ι KemSK Reader Response : Type} {base : OracleSpec ι}

def inject : QueryImpl RawCtxSourceSeal.SealSpec (OracleComp RawCtxMixedOwner.NativeSpec)
  | .inl input => RawCtxMixedOwner.NativeSpec.query (.inr (.inl input))
  | .inr (.inl bytes) => RawCtxMixedOwner.NativeSpec.query (.inr (.inr (.inr (.inl bytes))))
  | .inr (.inr frame) => RawCtxMixedOwner.NativeSpec.query (.inr (.inr (.inr (.inr frame))))

noncomputable def original (setup : Setup base KemSK) (codec : Codec Reader Response) :
    QueryImpl RawCtxSourceSeal.SealSpec (StateT Primitive ProbComp) :=
  PqxdhRecordLiftWorld.primitives setup (CborRawCanonicalBuild.canonical codec) ∘ₛ inject

private theorem run_liftState {A : Type} (work : StateT Primitive ProbComp A) (before : Primitive) :
    (liftState (Platform := Platform) work).run before = StateT.lift (work.run before) := rfl

private theorem original_writer (setup : Setup base KemSK) (codec : Codec Reader Response)
    (frame : RawCtxReceive.DecodedFrame) (before : Primitive) :
    (PqxdhRecordLiftWorld.primitives setup (CborRawCanonicalBuild.canonical codec) (.inr (.inr (.inr (.inr frame))))).run before =
      pure (CborRawCanonicalBuild.canonicalWriter frame, RegistrationNativePlatformOrdinaryWorld.chargeWriter before) := rfl

/-- The actual source World leaves are the ordinary private seal interpreter with only its terminal public capacity gate added. -/
theorem queries (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (request : RawCtxSourceSeal.SealSpec.Domain) :
    simulateQ (RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve) (inject request) =
      RegistrationNativePlatformOrdinarySealGate.implementation (original setup codec) reserve request := by
  rcases request with input | (bytes | frame)
  all_goals try (simp only [inject, simulateQ_spec_query, RegistrationNativePlatformOrdinarySealGate.implementation,
    original, QueryImpl.compose, simulateQ_spec_query]; rfl)
  ext before previous
  simp only [inject, simulateQ_spec_query, RegistrationNativePlatformOrdinarySealGate.implementation,
    original, QueryImpl.compose, simulateQ_spec_query, run_liftState, StateT.run_bind,
    StateT.run_lift, StateT.run_pure,
    RegistrationNativePlatformOrdinaryWorld.primitives]
  rw [RegistrationNativePlatformOrdinaryGate.writer_late reserve frame]
  rfl

/-- Expanding the complete private seal leaves only the terminal public reservation after its exact private poststate. -/
theorem sealing (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (input : RawCtxSourceSend.SealInput) :
    simulateQ (RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve)
        (simulateQ inject (RawCtxSourceSeal.sealInput input)) = (do
      let output ← liftState (simulateQ (original setup codec) (RawCtxSourceSeal.sealInput input))
      StateT.lift (gate reserve List.length output) : StateT Primitive (StateT Platform ProbComp) _) := by
  rw [← QueryImpl.simulateQ_compose]
  have exactQueries : RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve ∘ₛ inject =
      RegistrationNativePlatformOrdinarySealGate.implementation (original setup codec) reserve := by
    funext request
    exact queries setup codec reserve request
  rw [exactQueries]
  exact RegistrationNativePlatformOrdinarySealGate.program (original setup codec) reserve input

/-- The source send adapter expands the same three private sealing leaves before its public capacity gate. -/
theorem send_queries (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) :
    RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve ∘ₛ RawCtxMixedOwner.sendAdapter =
      RegistrationNativePlatformOrdinarySendGate.implementation
        (PqxdhRecordLiftWorld.primitives setup (CborRawCanonicalBuild.canonical codec) ∘ₛ RawCtxMixedOwner.sendAdapter)
        reserve := by
  funext request
  rcases request with request | input
  · simp only [QueryImpl.compose, RawCtxMixedOwner.sendAdapter, RawCtxSourceSeal.nativeAdapter,
      RawCtxMixedOwner.sendLift, simulateQ_spec_query,
      RegistrationNativePlatformOrdinarySendGate.implementation]
    rfl
  · simp only [QueryImpl.compose, RawCtxMixedOwner.sendAdapter, RawCtxSourceSeal.nativeAdapter,
      RegistrationNativePlatformOrdinarySendGate.implementation]
    have inclusion : RawCtxMixedOwner.sendLift ∘ₛ RawCtxSourceSeal.sealLift = inject := by
      funext request
      rcases request with request | (bytes | frame)
      all_goals simp only [QueryImpl.compose, RawCtxSourceSeal.sealLift, simulateQ_spec_query,
        RawCtxMixedOwner.sendLift, inject]
    rw [← QueryImpl.simulateQ_compose RawCtxMixedOwner.sendLift RawCtxSourceSeal.sealLift, inclusion]
    convert sealing setup codec reserve input using 1 <;>
      first | rfl | (simp only [original, QueryImpl.simulateQ_compose]; rfl)

/-- Complete actual owner execution advances the same kernel and private World before the terminal public reservation decides publication. -/
theorem sendOwner {Metadata : Type} (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (senderId : U64) (plaintext : Pqxdh.Bytes) (owner : RawCtxWholeOwner.OwnerState Metadata) :
    simulateQ (RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve)
        (simulateQ RawCtxMixedOwner.sendAdapter ((RawCtxSourceSend.sendOwner senderId plaintext).run owner)) = (do
      let result ← liftState (simulateQ (PqxdhRecordLiftWorld.primitives setup (CborRawCanonicalBuild.canonical codec))
        (simulateQ RawCtxMixedOwner.sendAdapter ((RawCtxSourceSend.sendOwner senderId plaintext).run owner)))
      let output ← StateT.lift (gate reserve (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) result.1)
      pure (output, result.2) : StateT Primitive (StateT Platform ProbComp) _) := by
  rw [← QueryImpl.simulateQ_compose, send_queries]
  simpa only [QueryImpl.simulateQ_compose] using
    RegistrationNativePlatformOrdinarySendGate.sendOwner
      (PqxdhRecordLiftWorld.primitives setup (CborRawCanonicalBuild.canonical codec) ∘ₛ RawCtxMixedOwner.sendAdapter)
      reserve senderId plaintext owner

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldSeal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldSeal.queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldSeal.queries

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldSeal.sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldSeal.sealing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldSeal.send_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldSeal.send_queries

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldSeal.sendOwner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldSeal.sendOwner
