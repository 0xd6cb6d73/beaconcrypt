-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaProgram
import BeaconcryptCore.Computational.RegistrationNativeScalarEffectBind
import BeaconcryptCore.Computational.RegistrationNativeScalarSource

/-! Native startup exposes its actual Server ML generation leaf. Beacon creation performs no ML generation. Every original initialization, pure pin selection, identity/prekey draw and private KEM birth remains in its original order and current World. Actual capability evaluation restores the complete original source outcome. -/
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

/-- Beacon construction is ordinary native work and makes no ML capability request. -/
noncomputable def create (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (edPin : Std.Array Std.U8 32#usize)
    (mlPin : Std.Array Std.U8 1952#usize) (keyId : Std.U64) :
    StateT (RegistrationNativeExperiment.State n KemSK source) (OracleComp (Spec source)) (RustM (Option Nat)) :=
  liftState (RegistrationNativeExperiment.beacon setup checks representation created
    (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId))

/-- The additive creation program restores the entire current native construction, including failed prefixes. -/
theorem eval_create (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (edPin : Std.Array Std.U8 32#usize)
    (mlPin : Std.Array Std.U8 1952#usize) (keyId : Std.U64) :
    evalState (create (n := n) (source := source) setup checks representation created edPin mlPin keyId) =
      RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId) :=
  RegistrationNativeMldsaProgram.eval_liftState _

private abbrev PeerMetadata := Std.Array Std.U8 151#usize

noncomputable def start (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Std.U64) :
    OracleComp (Spec source) (Option (RegistrationNativeExperiment.Initial n KemSK source)) := do
  let constructed ← lift ((PqxdhRecordLiftWorld.sampled
    ((PqxdhLiveServerConstruction.construct (P := PeerMetadata) setup.joint ensureInit identityIndex serverKeyId none).run ())).run
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

/-- Startup evaluates to the original generated Server credential, pure exact pin and every constructor failure. -/
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
