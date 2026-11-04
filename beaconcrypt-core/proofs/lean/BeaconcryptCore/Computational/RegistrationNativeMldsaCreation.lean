-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaProgram
import BeaconcryptCore.Computational.RegistrationNativeScalarEffectBind
import BeaconcryptCore.Computational.RegistrationNativeScalarSource

/-! Native startup and Beacon creation expose only their actual ML generation leaf. Every original initialization, pin hash, identity/prekey draw and private KEM birth remains in its original order and current World. Actual capability evaluation restores the complete original source outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCreation
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaProgram (Spec lift liftState evalState evaluate call)
open RegistrationNativeBeaconFrontend (Prepared)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def world (work : StateT (PqxdhRecordLiftWorld.State n) (OracleComp (Spec source)) Value) :
    StateT (RegistrationNativeExperiment.State n KemSK source) (OracleComp (Spec source)) Value := fun before =>
  (fun result => (result.1, { before with server := { before.server with world := { before.server.world with
    world := (result.2, before.server.world.world.2) } } })) <$> work.run before.server.world.world.1

/-- Reified leaves use the original World lens, preserving the complete native envelope. -/
theorem eval_world (work : StateT (PqxdhRecordLiftWorld.State n) (OracleComp (Spec source)) Value) :
    evalState (world (KemSK := KemSK) work) = RegistrationNativeExperiment.world (evalState work) := by
  funext before
  simp only [world, evalState, RegistrationNativeExperiment.world, RegistrationNativeExperiment.server,
    evaluate, simulateQ_map, StateT.run, Functor.map_map]

noncomputable def afterGenerated (edPin : Std.Array Std.U8 32#usize) (mlPin : Std.Array Std.U8 1952#usize)
    (keyId : Std.U64) (generated : Option (RegistrationNativeMldsa.Credential source)) :
    RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State
      (RustM (Option (Prepared source))) :=
  match generated with
  | none => pure (.ok none)
  | some credentials =>
    match registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
    | .fail error => pure (.fail error)
    | .div => pure .div
    | .ok pending => match pending.request with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok request => do
        let digest ← RegistrationNativeBeaconFrontend.hash request
        match pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
        | .fail error => pure (.fail error)
        | .div => pure .div
        | .ok .None => pure (.ok none)
        | .ok (.Some pin) => do
          let identity ← RegistrationNativeBeaconFrontend.sample PqxdhJointIdentity.sampleSeed
          let prekey ← RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar
          pure (.ok (some ⟨credentials, pin, identity, prekey⟩))

noncomputable def createSuffix (setup : Setup base KemSK) (edPin : Std.Array Std.U8 32#usize)
    (mlPin : Std.Array Std.U8 1952#usize) (keyId : Std.U64)
    (generated : Option (RegistrationNativeMldsa.Credential source)) :
    RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State (RustM (Option Nat)) := do
  match ← afterGenerated edPin mlPin keyId generated with
  | .ok (some prepared) =>
      RegistrationNativeBeaconFrontend.appendBorn setup source edPin keyId
        prepared.pin prepared.credentials prepared.identity prepared.prekey
  | .ok none => pure (.ok none)
  | .fail error => pure (.fail error)
  | .div => pure .div

/-- The only ML operation in source creation is its initial actual key-generation draw. -/
theorem create_split (setup : Setup base KemSK) (edPin : Std.Array Std.U8 32#usize)
    (mlPin : Std.Array Std.U8 1952#usize) (keyId : Std.U64) :
    RegistrationNativeBeaconFrontend.create (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
        setup source edPin mlPin keyId =
      (RegistrationNativeBeaconFrontend.sample (RegistrationNativeMldsa.generate source) >>= fun generated =>
        createSuffix setup edPin mlPin keyId generated) := by
  simp only [RegistrationNativeBeaconFrontend.create, RegistrationNativeBeaconFrontend.prepare,
    createSuffix, afterGenerated, bind_assoc]
  rfl

noncomputable def create (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (edPin : Std.Array Std.U8 32#usize)
    (mlPin : Std.Array Std.U8 1952#usize) (keyId : Std.U64) :
    StateT (RegistrationNativeExperiment.State n KemSK source) (OracleComp (Spec source)) (RustM (Option Nat)) := do
  let generated ← world (call .environment .generate)
  liftState (RegistrationNativeExperiment.beacon setup checks representation created
    (createSuffix setup edPin mlPin keyId generated))

/-- The additive creation program evaluates to the entire original native creation body, including all failed prefixes. -/
theorem eval_create (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (edPin : Std.Array Std.U8 32#usize)
    (mlPin : Std.Array Std.U8 1952#usize) (keyId : Std.U64) :
    evalState (create (n := n) (source := source) setup checks representation created edPin mlPin keyId) =
      RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId) := by
  rw [create, RegistrationNativeMldsaProgram.eval_bind, eval_world, RegistrationNativeMldsaProgram.eval_call]
  simp only [RegistrationNativeMldsaCapability.draw, RegistrationNativeMldsaProgram.eval_liftState]
  change (RegistrationNativeExperiment.world
      (simulateQ PqxdhRecordLiftWorld.effects
        (simulateQ RegistrationWorldCoinCompiler.envCoin (RegistrationNativeMldsa.generate source))) >>= fun generated =>
      RegistrationNativeExperiment.beacon setup checks representation created
        (createSuffix setup edPin mlPin keyId generated)) = _
  funext before
  rw [create_split, RegistrationNativeScalarSource.sample_effects,
    ← RegistrationNativeScalarEffectBind.effects_lift]
  have fact := RegistrationNativeScalarEffectBind.beacon_bind setup checks representation created
    (simulateQ RegistrationWorldCoinCompiler.envCoin (RegistrationNativeMldsa.generate source))
    (createSuffix (n := n) setup edPin mlPin keyId) before
  simp only [StateT.run] at fact
  rw [fact]
  change ((RegistrationNativeExperiment.world
      (simulateQ PqxdhRecordLiftWorld.effects
        (simulateQ RegistrationWorldCoinCompiler.envCoin (RegistrationNativeMldsa.generate source)))).run before >>= fun result =>
    (RegistrationNativeExperiment.beacon setup checks representation created
      (createSuffix setup edPin mlPin keyId result.1)).run result.2) = _
  simp only [RegistrationNativeExperiment.world, RegistrationNativeExperiment.server, StateT.run,
    bind_map_left, RegistrationBeaconReferenceNativeEffects.embed]

noncomputable def start (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Std.U64) :
    OracleComp (Spec source) (Option (RegistrationNativeExperiment.Initial n KemSK source)) := do
  let constructed ← lift ((PqxdhRecordLiftWorld.sampled
    ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ())).run
      (PqxdhRecordLiftWorld.initial : PqxdhRecordLiftWorld.State n))
  match constructed.1.1 with
  | none => pure none
  | some created =>
    let generated ← (call .native .generate).run constructed.2
    match generated.1 with
    | none => pure none
    | some credential =>
      let initialized ← lift ((RegistrationWorldServerFrontend.start created credential.publicKey
        RegistrationServerRoleBackend.empty).run generated.2)
      match initialized.1 with
      | .ok (.Some native) => pure (some ⟨created, credential,
          ⟨RegistrationServerFrontendCompiler.erase native, [], PqxdhLiveKemBirth.empty, 0⟩⟩)
      | _ => pure none

/-- Startup evaluates to the original generated Server credential, current pin cache and every constructor failure. -/
theorem eval_start (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Std.U64) :
    evaluate (start (n := n) (source := source) setup ensureInit identityIndex serverKeyId) =
      RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId := by
  unfold start RegistrationNativeExperiment.start
  simp only [evaluate, simulateQ_bind]
  rw [← evaluate, RegistrationNativeMldsaProgram.evaluate_lift]
  apply bind_congr
  intro constructed
  cases generated : constructed.1.1 with
  | none => simp only [simulateQ_pure]
  | some created =>
      dsimp only
      simp only [simulateQ_bind]
      have leaf := congrFun (RegistrationNativeMldsaProgram.eval_call (n := n) (source := source)
        .native .generate) constructed.2
      change evaluate ((call (n := n) (source := source) .native .generate).run constructed.2) =
        (PqxdhRecordLiftWorld.sampled (RegistrationNativeMldsa.generate source)).run constructed.2 at leaf
      simp only [evaluate] at leaf
      rw [leaf]
      apply bind_congr
      intro generated
      cases generated.1 with
      | none => simp only [simulateQ_pure]
      | some credential =>
          dsimp only
          simp only [simulateQ_bind]
          rw [← evaluate, RegistrationNativeMldsaProgram.evaluate_lift]
          apply bind_congr
          intro initialized
          cases outcome : initialized.1 with
          | fail error | div => rfl
          | ok option => cases option <;> rfl

end BeaconcryptCore.Computational.RegistrationNativeMldsaCreation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCreation.eval_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCreation.eval_world
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCreation.create_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCreation.create_split
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCreation.eval_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCreation.eval_create
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCreation.eval_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCreation.eval_start
