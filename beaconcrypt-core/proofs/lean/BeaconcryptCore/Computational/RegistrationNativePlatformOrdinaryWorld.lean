-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWriter
import BeaconcryptCore.Computational.CborRecordWorldSimulation

/-! Ongoing record execution uses the actual dynamic source Frame3 writer. Its only external argument is a public capacity, and the common platform state survives all source refusals and allocation failures. Real ratchet, AEAD, opening and CTX requests retain their original private World counters and shared cache. No equality to a static writer profile is asserted. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorld
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhRecordLiftWorld (State Primitive produce)
variable {n : Nat} {ι KemSK Reader Response Platform E Value : Type} {base : OracleSpec ι}
abbrev M (n : Nat) (Platform : Type) := StateT (State n) (StateT Platform ProbComp)

def liftWorld (work : StateT (State n) ProbComp Value) : M n Platform Value :=
  fun before => StateT.lift (work.run before)

def chargeWriter (before : Primitive) : Primitive :=
  ({ before.1 with native := Function.update before.1.native .writer (before.1.native .writer + 1) }, before.2)

noncomputable def primitives (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) :
    QueryImpl RawCtxMixedOwner.NativeSpec (StateT Primitive (StateT Platform ProbComp))
  | .inr (.inr (.inr (.inr frame))) => fun before => do
      let output ← RegistrationNativePlatformOrdinaryWriter.write reserve frame
      pure (output, chargeWriter before)
  | query => fun before => StateT.lift ((PqxdhRecordLiftWorld.primitives setup codec query).run before)

noncomputable def serverStep (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain) :
    M n Platform (RawCtxServerMixed.SourceSpec.Range query) := fun before =>
  match before.server with
  | none => match query with
      | .inl _ => pure (none, before)
      | .inr _ => pure (.None, before)
  | some server => do
      let result ← (simulateQ (primitives setup codec reserve) (PqxdhDeploymentNative.logged
        ((MldsaServerRouting.handler PqxdhRefinement.absBytes
          (fun _ => server.sender) route codec.frameRead query).run server.records))).run before.primitive
      pure (result.1.1.1, produce (PqxdhDeploymentNative.serverTag query) result.1.2
        { before with server := some { server with records := result.1.1.2 }, primitive := result.2 })

noncomputable def beaconStep (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain) : M n Platform (RawCtxMixedOwner.SourceSpec.Range query) := fun before =>
  match before.owners[owner]? with
  | none => pure (PqxdhDeploymentNative.absent query, before)
  | some phase => do
      let result ← (simulateQ (primitives setup codec reserve) (PqxdhDeploymentNative.logged
        ((PqxdhRecordLiftBeacon.handler codec.frameRead query).run ⟨phase, before.ownerRaw owner⟩))).run before.primitive
      pure (result.1.1.1, produce (PqxdhDeploymentNative.beaconTag owner) result.1.2
        { before with owners := before.owners.set owner result.1.1.2.phase
                      ownerRaw := Function.update before.ownerRaw owner result.1.1.2.rawAttempts
                      primitive := result.2 })

noncomputable def handler (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) : QueryImpl (WorldSpec n) (M n Platform)
  | .inl created => liftWorld (PqxdhRecordLiftWorld.initializeServer created)
  | .inr (.inl query) => liftWorld (PqxdhRecordLiftWorld.effects query)
  | .inr (.inr (.inl (.inl pair))) => serverStep (n := n) setup codec reserve route (.inl pair)
  | .inr (.inr (.inl (.inr raw))) => serverStep (n := n) setup codec reserve route (.inr raw)
  | .inr (.inr (.inr (owner, .inl plaintext))) => beaconStep (n := n) setup codec reserve owner (.inl plaintext)
  | .inr (.inr (.inr (owner, .inr raw))) => beaconStep (n := n) setup codec reserve owner (.inr raw)

noncomputable def guarded (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) : QueryImpl (WorldSpec n) (M n Platform) :=
  fun query before => match CborRecordWorldClient.refusal query (CborRecordWorldCursor.worldShell before) with
  | some reply => pure (reply, before)
  | none => (handler setup codec reserve route query).run before

/-- Dynamic source writing charges the reached writer once and preserves its exact shared external poststate. -/
theorem writer_joint (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (frame : RawCtxReceive.DecodedFrame) (before : Primitive) (previous : Platform) :
    ((primitives setup codec reserve (.inr (.inr (.inr (.inr frame))))).run before).run previous =
      (fun result => ((result.1, chargeWriter before), result.2)) <$>
        (RegistrationNativePlatformOrdinaryWriter.write reserve frame).run previous := by
  change ((do
    let output ← RegistrationNativePlatformOrdinaryWriter.write reserve frame
    pure (output, chargeWriter before) : StateT Platform ProbComp _).run previous) = _
  rw [StateT.run_bind]
  simp only [StateT.run_pure]
  exact bind_pure_comp _ _

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorld

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorld.writer_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorld.writer_joint
