-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldRouting
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldGuarded
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformOrdinaryWorldRouting (after after_run)
open RegistrationNativePlatformOrdinaryGate (gate)
variable {n : Nat} {I KemSK Reader Response Platform E : Type} {base : OracleSpec I}

theorem refusal_beacon (shell : CborRecordWorldClient.Shell) (owner : Nat) (plaintext : Pqxdh.Bytes)
    (reply : Option RawCtxSourceSend.Encrypted)
    (refused : CborRecordWorldClient.refusal (n := n) (Sum.inr (Sum.inr (Sum.inr (owner, Sum.inl plaintext)))) shell = some reply) : reply = none := by
  simp only [CborRecordWorldClient.refusal] at refused
  split at refused
  · cases refused
  · split at refused
    · cases refused
    · exact (Option.some.inj refused).symm

theorem refusal_server (shell : CborRecordWorldClient.Shell) (keyId : U64) (plaintext : Pqxdh.Bytes)
    (reply : Option RawCtxSourceSend.Encrypted)
    (refused : CborRecordWorldClient.refusal (n := n) (Sum.inr (Sum.inr (Sum.inl (Sum.inl (plaintext, keyId))))) shell = some reply) : reply = none := by
  simp only [CborRecordWorldClient.refusal] at refused
  split at refused
  · cases refused
  · split at refused
    · cases refused
    · split at refused
      · cases refused
      · exact (Option.some.inj refused).symm

private theorem lift_pure {A : Type} (value : A) :
    (StateT.lift (pure value : ProbComp A) : StateT Platform ProbComp A) = pure value := by
  funext previous
  change (pure value >>= fun result => pure (result, previous) : ProbComp _) = pure (value, previous)
  exact pure_bind _ _

theorem beacon (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (owner : Nat) (plaintext : Pqxdh.Bytes) :
    RegistrationNativePlatformOrdinaryWorld.guarded (n := n) setup codec reserve route (Sum.inr (Sum.inr (Sum.inr (owner, Sum.inl plaintext)))) =
      after reserve (CborRecordWorldSimulation.guarded setup (CborRawCanonicalBuild.canonical codec) route (Sum.inr (Sum.inr (Sum.inr (owner, Sum.inl plaintext))))) := by
  let original : StateT (PqxdhRecordLiftWorld.State n) ProbComp (Option RawCtxSourceSend.Encrypted) :=
    CborRecordWorldSimulation.guarded setup (CborRawCanonicalBuild.canonical codec) route (Sum.inr (Sum.inr (Sum.inr (owner, Sum.inl plaintext))))
  funext before
  change (RegistrationNativePlatformOrdinaryWorld.guarded (n := n) setup codec reserve route (Sum.inr (Sum.inr (Sum.inr (owner, Sum.inl plaintext))))).run before = (after reserve original).run before
  rw [after_run]
  cases refused : CborRecordWorldClient.refusal (n := n) (Sum.inr (Sum.inr (Sum.inr (owner, Sum.inl plaintext)))) (CborRecordWorldCursor.worldShell before) with
  | none =>
      have moved := congrFun (RegistrationNativePlatformOrdinaryWorldRouting.beaconStep (n := n) setup codec reserve owner plaintext) before
      let originalStep : StateT (PqxdhRecordLiftWorld.State n) ProbComp (Option RawCtxSourceSend.Encrypted) := PqxdhRecordLiftWorld.beaconStep setup (CborRawCanonicalBuild.canonical codec) owner (Sum.inl plaintext)
      change (RegistrationNativePlatformOrdinaryWorld.beaconStep setup codec reserve owner (Sum.inl plaintext)).run before = (after reserve originalStep).run before at moved
      rw [after_run] at moved
      simp only [StateT.run, RegistrationNativePlatformOrdinaryWorld.guarded, CborRecordWorldSimulation.guarded, original, originalStep,
        refused, RegistrationNativePlatformOrdinaryWorld.handler, PqxdhRecordLiftWorld.handler] at moved ⊢
      convert moved using 1
  | some reply =>
      have empty := refusal_beacon (CborRecordWorldCursor.worldShell before) owner plaintext reply refused
      cases empty
      simp only [StateT.run, RegistrationNativePlatformOrdinaryWorld.guarded, CborRecordWorldSimulation.guarded, original,
        refused, lift_pure, gate, pure_bind]

theorem server (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (keyId : U64) (plaintext : Pqxdh.Bytes) :
    RegistrationNativePlatformOrdinaryWorld.guarded (n := n) setup codec reserve route (Sum.inr (Sum.inr (Sum.inl (Sum.inl (plaintext, keyId))))) =
      after reserve (CborRecordWorldSimulation.guarded setup (CborRawCanonicalBuild.canonical codec) route (Sum.inr (Sum.inr (Sum.inl (Sum.inl (plaintext, keyId)))))) := by
  let original : StateT (PqxdhRecordLiftWorld.State n) ProbComp (Option RawCtxSourceSend.Encrypted) :=
    CborRecordWorldSimulation.guarded setup (CborRawCanonicalBuild.canonical codec) route (Sum.inr (Sum.inr (Sum.inl (Sum.inl (plaintext, keyId)))))
  funext before
  change (RegistrationNativePlatformOrdinaryWorld.guarded (n := n) setup codec reserve route (Sum.inr (Sum.inr (Sum.inl (Sum.inl (plaintext, keyId)))))).run before = (after reserve original).run before
  rw [after_run]
  cases refused : CborRecordWorldClient.refusal (n := n) (Sum.inr (Sum.inr (Sum.inl (Sum.inl (plaintext, keyId))))) (CborRecordWorldCursor.worldShell before) with
  | none =>
      have moved := congrFun (RegistrationNativePlatformOrdinaryWorldRouting.serverStep (n := n) setup codec reserve route keyId plaintext) before
      let originalStep : StateT (PqxdhRecordLiftWorld.State n) ProbComp (Option RawCtxSourceSend.Encrypted) := PqxdhRecordLiftWorld.serverStep setup (CborRawCanonicalBuild.canonical codec) route (Sum.inl (plaintext, keyId))
      change (RegistrationNativePlatformOrdinaryWorld.serverStep setup codec reserve route (Sum.inl (plaintext, keyId))).run before = (after reserve originalStep).run before at moved
      rw [after_run] at moved
      simp only [StateT.run, RegistrationNativePlatformOrdinaryWorld.guarded, CborRecordWorldSimulation.guarded, original, originalStep,
        refused, RegistrationNativePlatformOrdinaryWorld.handler, PqxdhRecordLiftWorld.handler] at moved ⊢
      convert moved using 1
  | some reply =>
      have empty := refusal_server (CborRecordWorldCursor.worldShell before) keyId plaintext reply refused
      cases empty
      simp only [StateT.run, RegistrationNativePlatformOrdinaryWorld.guarded, CborRecordWorldSimulation.guarded, original,
        refused, lift_pure, gate, pure_bind]
end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldGuarded
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldGuarded.refusal_beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldGuarded.refusal_beacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldGuarded.refusal_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldGuarded.refusal_server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldGuarded.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldGuarded.beacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldGuarded.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldGuarded.server
