-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldLogged
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldRouting
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (Primitive)
open RegistrationNativePlatformOrdinaryGate (gate)
variable {n : Nat} {I KemSK Reader Response Platform E Metadata S : Type} {base : OracleSpec I}

theorem mapped_owner (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (sender : U64) (plaintext : Pqxdh.Bytes) (owner : RawCtxWholeOwner.OwnerState Metadata)
    (primitive : Primitive)
    (render : RawCtxWholeOwner.OwnerState Metadata → Primitive → PqxdhRecordLiftLoggedAdapters.Frames → S) :
    let work := simulateQ RawCtxMixedOwner.sendAdapter ((RawCtxSourceSend.sendOwner sender plaintext).run owner)
    (fun result => (result.1.1.1, render result.1.1.2 result.2 result.1.2)) <$>
      (simulateQ (RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve) (PqxdhDeploymentNative.logged work)).run primitive = (do
      let result ← StateT.lift ((simulateQ (PqxdhRecordLiftWorld.primitives setup (CborRawCanonicalBuild.canonical codec))
        (PqxdhDeploymentNative.logged work)).run primitive)
      let output ← gate reserve (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) result.1.1.1
      pure (output, render result.1.1.2 result.2 result.1.2) : StateT Platform ProbComp _) := by
  have mapped := congrArg (fun distribution => (fun result :
      (Option RawCtxSourceSend.Encrypted × RawCtxWholeOwner.OwnerState Metadata) × (Primitive × PqxdhRecordLiftLoggedAdapters.Frames) =>
        (result.1.1, render result.1.2 result.2.1 result.2.2)) <$> distribution)
    (RegistrationNativePlatformOrdinaryWorldLogged.source_owner setup codec reserve sender plaintext owner primitive)
  simpa only [Functor.map_map, map_bind, map_pure, PqxdhRecordLiftLoggedAdapters.swapResult] using mapped

def after (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp (Option RawCtxSourceSend.Encrypted)) :
    RegistrationNativePlatformOrdinaryWorld.M n Platform (Option RawCtxSourceSend.Encrypted) := do
  let result ← RegistrationNativePlatformOrdinaryWorld.liftWorld work
  StateT.lift (gate reserve (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) result)

theorem after_run (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp (Option RawCtxSourceSend.Encrypted))
    (before : PqxdhRecordLiftWorld.State n) :
    (after reserve work).run before = (do
      let result ← StateT.lift (work.run before)
      let output ← gate reserve (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) result.1
      pure (output, result.2) : StateT Platform ProbComp _) := rfl

private theorem lift_pure {A : Type} (value : A) :
    (StateT.lift (pure value : ProbComp A) : StateT Platform ProbComp A) = pure value := by
  funext previous
  change (pure value >>= fun result => pure (result, previous) : ProbComp _) = pure (value, previous)
  exact pure_bind _ _

private theorem pure_apply {T V : Type} {m : Type → Type} [Monad m] (value : V) (before : T) :
    (pure value : StateT T m V) before = pure (value, before) := rfl

private theorem lift_map {A B : Type} (f : A → B) (work : ProbComp A) :
    (StateT.lift (f <$> work) : StateT Platform ProbComp B) = f <$> StateT.lift work := by
  funext previous
  change (StateT.lift (f <$> work) : StateT Platform ProbComp B).run previous =
    (f <$> (StateT.lift work : StateT Platform ProbComp A)).run previous
  simp only [StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map]

private theorem map_apply {T A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT T m A) (before : T) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem logged_pure {A : Type} (value : A) :
    PqxdhDeploymentNative.logged (pure value) = pure (value, []) := by
  simp only [PqxdhDeploymentNative.logged, simulateQ_pure, StateT.run_pure]

theorem beaconStep (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (owner : Nat) (plaintext : Pqxdh.Bytes) :
    RegistrationNativePlatformOrdinaryWorld.beaconStep (n := n) setup codec reserve owner (.inl plaintext) = (do
      let result ← RegistrationNativePlatformOrdinaryWorld.liftWorld
        (PqxdhRecordLiftWorld.beaconStep setup (CborRawCanonicalBuild.canonical codec) owner (.inl plaintext))
      StateT.lift (gate reserve (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) result)) := by
  funext before
  change (RegistrationNativePlatformOrdinaryWorld.beaconStep setup codec reserve owner (.inl plaintext) : RegistrationNativePlatformOrdinaryWorld.M n Platform (Option RawCtxSourceSend.Encrypted)).run before =
    (after reserve (PqxdhRecordLiftWorld.beaconStep setup (CborRawCanonicalBuild.canonical codec) owner (.inl plaintext))).run before
  rw [after_run]
  cases found : before.owners[owner]? with
  | none =>
      simp only [StateT.run, RegistrationNativePlatformOrdinaryWorld.beaconStep, PqxdhRecordLiftWorld.beaconStep,
        found, PqxdhDeploymentNative.absent,
        lift_pure, gate, pure_bind]
  | some phase =>
      cases phase with
      | inactive inactive =>
          simp only [StateT.run, RegistrationNativePlatformOrdinaryWorld.beaconStep, PqxdhRecordLiftWorld.beaconStep,
            found, PqxdhRecordLiftBeacon.handler, PqxdhRecordLiftBeacon.rejected,
            logged_pure, simulateQ_pure, pure_apply,
            lift_pure, gate, pure_bind]
      | established shell kernel =>
          let original : RawCtxWholeOwner.OwnerState Unit :=
            ⟨⟨kernel, shell.control.server_binding.identity_key_id, PqxdhRefinement.absBytes shell.associatedData, ()⟩, before.ownerRaw owner⟩
          let render := fun (after : RawCtxWholeOwner.OwnerState Unit) (primitive : Primitive) (frames : PqxdhRecordLiftLoggedAdapters.Frames) =>
            PqxdhRecordLiftWorld.produce (PqxdhDeploymentNative.beaconTag owner) frames
              {before with owners := before.owners.set owner (.established shell after.owner.kernel)
                           ownerRaw := Function.update before.ownerRaw owner after.rawAttempts
                           primitive := primitive}
          have moved := mapped_owner setup codec reserve shell.identityKeyId plaintext original before.primitive render
          simp only [StateT.run, RegistrationNativePlatformOrdinaryWorld.beaconStep, PqxdhRecordLiftWorld.beaconStep,
            found, PqxdhRecordLiftBeacon.handler, RawCtxMixedOwner.ownerImpl,
            bind_pure_comp, PqxdhDeploymentNative.logged_map, simulateQ_map,
            map_apply, Functor.map_map, Prod.map, id_eq, lift_map, bind_map_left, original, render] at moved ⊢
          convert moved using 1 <;> rfl

theorem serverStep (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (keyId : U64) (plaintext : Pqxdh.Bytes) :
    RegistrationNativePlatformOrdinaryWorld.serverStep (n := n) setup codec reserve route (.inl (plaintext, keyId)) = (do
      let result ← RegistrationNativePlatformOrdinaryWorld.liftWorld
        (PqxdhRecordLiftWorld.serverStep setup (CborRawCanonicalBuild.canonical codec) route (.inl (plaintext, keyId)))
      StateT.lift (gate reserve (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) result)) := by
  funext before
  change (RegistrationNativePlatformOrdinaryWorld.serverStep setup codec reserve route (.inl (plaintext, keyId)) : RegistrationNativePlatformOrdinaryWorld.M n Platform (Option RawCtxSourceSend.Encrypted)).run before =
    (after reserve (PqxdhRecordLiftWorld.serverStep setup (CborRawCanonicalBuild.canonical codec) route (.inl (plaintext, keyId)))).run before
  rw [after_run]
  cases found : before.server with
  | none =>
      simp only [StateT.run, RegistrationNativePlatformOrdinaryWorld.serverStep, PqxdhRecordLiftWorld.serverStep,
        found, lift_pure, gate, pure_bind]
  | some server =>
      cases present : server.records.server.peers keyId with
      | none =>
          simp only [StateT.run, RegistrationNativePlatformOrdinaryWorld.serverStep, PqxdhRecordLiftWorld.serverStep,
            found, MldsaServerRouting.handler, MldsaServerRouting.send, present,
            logged_pure, simulateQ_pure, pure_apply, lift_pure, gate, pure_bind]
      | some peer =>
          let original : RawCtxWholeOwner.OwnerState Unit :=
            ⟨MldsaServerRouting.selected PqxdhRefinement.absBytes keyId peer, server.records.rawAttempts⟩
          let render := fun (after : RawCtxWholeOwner.OwnerState Unit) (primitive : Primitive) (frames : PqxdhRecordLiftLoggedAdapters.Frames) =>
            PqxdhRecordLiftWorld.produce (PqxdhDeploymentNative.serverTag (.inl (plaintext, keyId))) frames
              {before with server := some {server with records := ⟨RawCtxServerRouting.putPeer server.records.server keyId peer after.owner.kernel, after.rawAttempts⟩}
                           primitive := primitive}
          have moved := mapped_owner setup codec reserve server.sender plaintext original before.primitive render
          simp only [StateT.run, RegistrationNativePlatformOrdinaryWorld.serverStep, PqxdhRecordLiftWorld.serverStep,
            found, MldsaServerRouting.handler, MldsaServerRouting.send, present, RawCtxMixedOwner.ownerImpl,
            bind_pure_comp, PqxdhDeploymentNative.logged_map, simulateQ_map,
            map_apply, Functor.map_map, Prod.map, id_eq, lift_map, bind_map_left, original, render] at moved ⊢
          convert moved using 1 <;> rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldRouting
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldRouting.mapped_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldRouting.mapped_owner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldRouting.beaconStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldRouting.beaconStep

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldRouting.after_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldRouting.after_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldRouting.serverStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldRouting.serverStep
