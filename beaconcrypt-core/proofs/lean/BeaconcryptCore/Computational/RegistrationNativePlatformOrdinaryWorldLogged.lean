-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLogged
/-! The concrete actual source writer is connected to its original private World and per-command source journal before routing updates. Public reservation can reject publication after the exact consumed send kernel, hash cache, native counters and reached-writer frame are retained. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldLogged
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (Primitive)
open RegistrationNativePlatformOrdinarySendGate (liftState)
open RegistrationNativePlatformOrdinaryGate (gate)
open RegistrationNativePlatformOrdinaryLogged (logged gated)
variable {Platform E ι KemSK Reader Response : Type} {base : OracleSpec ι}

/-- The concrete dynamic source World is precisely its private canonical interpreter with only a public terminal writer gate. -/
theorem world (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) :
    RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve =
      gated (PqxdhRecordLiftWorld.primitives setup (CborRawCanonicalBuild.canonical codec)) reserve := by
  funext query
  rcases query with request | (input | (input | (bytes | frame)))
  all_goals try (solve | rfl)
  convert RegistrationNativePlatformOrdinaryWorldSeal.queries setup codec reserve (.inr (.inr frame)) using 1 <;>
    first | rfl | simp only [RegistrationNativePlatformOrdinaryWorldSeal.inject, simulateQ_spec_query]

/-- Failed source publication retains the complete advanced owner, native primitive state and reached-writer journal. -/
theorem owner {Metadata : Type} (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (senderId : U64) (plaintext : Pqxdh.Bytes) (before : RawCtxWholeOwner.OwnerState Metadata) :
    simulateQ (logged (RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve))
        (simulateQ RawCtxMixedOwner.sendAdapter ((RawCtxSourceSend.sendOwner senderId plaintext).run before)) = (do
      let result ← liftState (simulateQ
        (logged (PqxdhRecordLiftWorld.primitives setup (CborRawCanonicalBuild.canonical codec)))
        (simulateQ RawCtxMixedOwner.sendAdapter ((RawCtxSourceSend.sendOwner senderId plaintext).run before)))
      let output ← StateT.lift (gate reserve (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) result.1)
      pure (output, result.2) : StateT (Primitive × PqxdhRecordLiftLoggedAdapters.Frames) (StateT Platform ProbComp) _) := by
  rw [world, RegistrationNativePlatformOrdinaryLogged.logged_gated]
  exact RegistrationNativePlatformOrdinaryLogged.sendOwner
    (logged (PqxdhRecordLiftWorld.primitives setup (CborRawCanonicalBuild.canonical codec))) reserve senderId plaintext before

private theorem run_liftState {S A : Type} (work : StateT S ProbComp A) (before : S) :
    (liftState (Platform := Platform) work).run before = StateT.lift (work.run before) := rfl

/-- The complete source command has the original private execution and exact reached-writer log, followed only by public publication refusal. -/
theorem source_owner {Metadata : Type} (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (senderId : U64) (plaintext : Pqxdh.Bytes) (before : RawCtxWholeOwner.OwnerState Metadata)
    (primitive : Primitive) :
    let work := simulateQ RawCtxMixedOwner.sendAdapter ((RawCtxSourceSend.sendOwner senderId plaintext).run before)
    PqxdhRecordLiftLoggedAdapters.swapResult <$>
      (simulateQ (RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve)
        (PqxdhDeploymentNative.logged work)).run primitive = (do
      let result ← StateT.lift ((simulateQ
        (PqxdhRecordLiftWorld.primitives setup (CborRawCanonicalBuild.canonical codec))
        (PqxdhDeploymentNative.logged work)).run primitive)
      let output ← gate reserve (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) result.1.1.1
      pure ((output, result.1.1.2), (result.2, result.1.2)) : StateT Platform ProbComp _) := by
  dsimp only
  change PqxdhRecordLiftLoggedAdapters.swapResult <$>
    (simulateQ (RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve)
      ((simulateQ PqxdhDeploymentNative.frameLog _).run [])).run primitive = _
  rw [← RegistrationNativePlatformOrdinaryLogged.program_source, owner]
  simp only [StateT.run_bind, run_liftState, StateT.run_lift, StateT.run_pure,
    bind_assoc, pure_bind]
  rw [RegistrationNativePlatformOrdinaryLogged.program_source]
  ext previous
  simp only [StateT.run_bind, StateT.run_lift, bind_map_left, PqxdhRecordLiftLoggedAdapters.swapResult]
  simp only [StateT.run_pure, bind_assoc, pure_bind]
  all_goals rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldLogged

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldLogged.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldLogged.world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldLogged.owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldLogged.owner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldLogged.source_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldLogged.source_owner
