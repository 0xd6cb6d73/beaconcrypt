-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerMaterialSourceLift

/-! Once actual source pin/occupancy/preflight/reservation admission has produced an initializer, the finite public material controller is the real native SDK record/publication/commit component. The private root supplies only the known108 service interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerMaterialAdmittedSource
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerMaterialSourceState (State close project restore nativeView service)
variable {n : Nat} {ι KemSK Reader Response : Type} {base : OracleSpec ι}

noncomputable def admitted (wire : RegistrationNativeWire.Wire) (control : pqxdh.ServerState)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (message : RegistrationNativeRelatedFamily.Message) :
    StateT RegistrationServerMaterialFrontend.State (OracleComp (RegistrationServerMaterialFrontend.Spec n))
      RegistrationServerMaterialFrontend.Result := do
  let published ← StateT.lift (RegistrationNativePairedServerService.publicAdmitted wire.encodeResponse control initial message)
  RegistrationServerMaterialFrontend.finish published

private theorem commit_view (published : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes))
    (before : RegistrationServerFrontendCompiler.State n) :
    Prod.map id nativeView <$> (RegistrationServerSdkSource.commit published).run before =
      (RegistrationServerSdkSource.commit published).run (nativeView before) := by
  cases published with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> rfl

private theorem sdk_run (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes) (control : pqxdh.ServerState)
    (initial : registration.ServerInitialKdf) (before : RegistrationServerFrontendCompiler.State n) :
    (RegistrationServerSdkSource.fromInitial setup codec sign encode control initial).run before = (do
      let result ← (RegistrationWorldServerCompletion.fromInitial setup codec sign encode control initial).run before.world
      (RegistrationServerSdkSource.commit result.1).run { before with world := result.2 }) := by
  rw [RegistrationServerSdkSource.fromInitial, StateT.run_bind]
  simp only [RegistrationServerSdkSource.world,
    StateT.run, bind_map_left]

/-- The admitted public frontend settles the complete actual source record/sign/encode/install result on its original current state. -/
theorem native (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots) (control : pqxdh.ServerState)
    (initial : registration.ServerInitialKdf) (message : RegistrationNativeRelatedFamily.Message)
    (role : initial.pending = PqxdhInitialRatchetComplementarity.serverPending
      (PqxdhRootTableInitialization.rootArray (roots message))) (before : State n) :
    Prod.map id (project roots) <$>
      (close setup.source wire.frameWrite sign roots
        (admitted wire control (RegistrationBoundKeySchedule.publicInitial initial) message)).run before =
      Prod.map id nativeView <$>
        (RegistrationServerSdkSource.fromInitial setup (RegistrationNativeWire.ledgerCodec wire)
          sign wire.encodeResponse control initial).run (restore roots before) := by
  have material := congrArg (fun distribution => distribution >>= fun result =>
    (RegistrationServerSdkSource.commit result.1).run
      (RegistrationServerReferenceRestore.restore roots before.1 result.2))
    (RegistrationServerMaterialServiceSource.native setup (RegistrationNativeWire.ledgerCodec wire)
      sign roots wire.encodeResponse control initial message role before.2)
  simp only [admitted, RegistrationServerMaterialSourceLift.bind_run,
    RegistrationServerMaterialSourceLift.lift_run, map_bind, bind_map_left]
  simp only [RegistrationServerMaterialSourceState.commit]
  rw [sdk_run]
  simp only [map_bind, commit_view, restore, nativeView,
    RegistrationServerReferenceRestore.restore, project] at material ⊢
  simp only [bind_map_left, Prod.map_def, id_eq, RegistrationNativeWire.ledgerCodec] at material ⊢
  exact material

end BeaconcryptCore.Computational.RegistrationServerMaterialAdmittedSource

/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialAdmittedSource.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialAdmittedSource.native
