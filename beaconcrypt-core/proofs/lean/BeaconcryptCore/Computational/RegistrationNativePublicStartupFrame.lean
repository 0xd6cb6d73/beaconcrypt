-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicStartup
import BeaconcryptCore.Computational.RegistrationNativePublicRootFrame

/-! Generated reference startup is exactly one computation of the existing World. Constructor and ML keygen draws remain at their original positions, and neither the retained-root memo nor any root callback is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicStartupFrame
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicInterpreter (State world)
variable {ι KemSK X Y : Type} {base : OracleSpec ι} {n : Nat}

private theorem world_bind (first : StateT (PqxdhRecordLiftWorld.State n) ProbComp X)
    (next : X → StateT (PqxdhRecordLiftWorld.State n) ProbComp Y) :
    world (KemSK := KemSK) (first >>= next) = (world first >>= fun value => world (next value)) := by
  apply StateT.ext
  intro before
  change (fun result => (result.1, { before with world := result.2 })) <$>
    simulateQ RegistrationNativePublicInterpreter.coins ((first >>= next).run before.world) =
      ((world first >>= fun value => world (next value)).run before)
  rw [StateT.run_bind, StateT.run_bind]
  simp only [world, StateT.run, simulateQ_bind, map_bind, bind_map_left]


private theorem world_pure (value : X) :
    world (n := n) (KemSK := KemSK) (pure value) = pure value := by
  apply StateT.ext
  intro before
  change (fun result => (result.1, { before with world := result.2 })) <$>
    simulateQ RegistrationNativePublicInterpreter.coins
      ((pure value : StateT (PqxdhRecordLiftWorld.State n) ProbComp X).run before.world) =
        (pure value : RegistrationNativePublicInterpreter.M n KemSK X).run before
  simp only [StateT.run_pure, simulateQ_pure, map_pure]


private abbrev PeerMetadata := Std.Array U8 151#usize

noncomputable def startup (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) :
    StateT (PqxdhRecordLiftWorld.State n) ProbComp (Option (RegistrationNativePublicStartup.Started source)) := do
  let constructed ← PqxdhRecordLiftWorld.sampled
    ((PqxdhLiveServerConstruction.construct (P := PeerMetadata) setup.joint ensureInit identityIndex serverKeyId none).run ())
  match constructed.1 with
  | none => pure none
  | some _ =>
      let generated ← PqxdhRecordLiftWorld.sampled (RegistrationNativeMldsa.generate source)
      match generated with
      | none => pure none
      | some credential =>
          let created := RegistrationServerStartup.publicCreated identity identityIndex serverKeyId
          let _ ← PqxdhRecordLiftWorld.initializeServer created
          let pin : session.ServerAuthenticationPin :=
            ⟨⟨PqxdhRootTableInitialization.rootArray identity.ed25519, serverKeyId⟩,
              credential.publicKey⟩
          let frontend : RegistrationNativePublicFrontend.State source :=
            ⟨RegistrationServerMaterialFrontend.initial created.control pin, [],
              ⟨RegistrationServerRoleBackend.empty, [], [], []⟩, 0⟩
          pure (some ⟨credential, frontend⟩)

/-- The concrete generated startup uses the same World operation, without a separate root-service initialization premise. -/
theorem start_world (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) :
    RegistrationNativePublicStartup.start (n := n) setup source ensureInit identityIndex serverKeyId identity =
      world (startup setup source ensureInit identityIndex serverKeyId identity) := by
  simp only [startup, RegistrationNativePublicStartup.start, world_bind]
  apply congrArg (fun continuation =>
    world (n := n) (KemSK := KemSK) (PqxdhRecordLiftWorld.sampled
      ((PqxdhLiveServerConstruction.construct (P := PeerMetadata) setup.joint ensureInit identityIndex serverKeyId none).run ())) >>= continuation)
  funext constructed
  cases constructed.1 with
  | none => exact (world_pure none).symm
  | some created =>
      rw [world_bind]
      apply congrArg (fun continuation =>
        world (n := n) (KemSK := KemSK) (PqxdhRecordLiftWorld.sampled (RegistrationNativeMldsa.generate source)) >>= continuation)
      funext generated
      cases generated <;> simp only [world_pure, world_bind]


/-- All startup branches make zero root, selected-signing or public-HMAC queries. -/
theorem start_free (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) (before : State n KemSK) :
    ((RegistrationNativePublicStartup.start setup source ensureInit identityIndex serverKeyId identity).run before).IsQueryBoundP
      RegistrationNativePublicRootFrame.IsRoot 0 := by
  rw [start_world]
  exact RegistrationNativePublicRootFrame.world_free _ before

/-- Every generated-startup branch preserves the separate root memo, together with every actual World counter and field. -/
theorem start_replace (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity)
    (memo : RegistrationNativeReferenceInterpreter.State) (before : State n KemSK) :
    Prod.map id (RegistrationNativePublicRootFrame.replace memo) <$>
      (RegistrationNativePublicStartup.start setup source ensureInit identityIndex serverKeyId identity).run before =
      (RegistrationNativePublicStartup.start setup source ensureInit identityIndex serverKeyId identity).run
        (RegistrationNativePublicRootFrame.replace memo before) := by
  rw [start_world]
  exact RegistrationNativePublicRootFrame.world_replace memo _ before

end BeaconcryptCore.Computational.RegistrationNativePublicStartupFrame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicStartupFrame.start_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicStartupFrame.start_world
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicStartupFrame.start_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicStartupFrame.start_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicStartupFrame.start_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicStartupFrame.start_replace
