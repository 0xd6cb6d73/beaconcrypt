-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconAgreementInputReceipt

/-! Actual native Beacon classical replies are the literal source conversion and ordered role-DH values. Their lowering changes the request ledger alone; private key rows and every complete native coordinate remain unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconDhReplies
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner M)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeResponseAuthentication (lower_bind lower_pure)
open RegistrationAgreementRoot (nativeOption)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

def reply (setup : Setup base KemSK) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (request : agreement.DhRequest) : core.option.Option (Std.Array U8 32#usize) :=
  match request.secret_role with
  | .LocalIdentity => nativeOption ((setup.joint.staticDh owner.identitySeed (PqxdhPhase2GapDhSource.peer request.public_key)).map PqxdhRootTableInitialization.rootArray)
  | .BeaconPrekey => nativeOption ((setup.dh.dh owner.prekeyScalar (PqxdhPhase2GapDhSource.peer request.public_key)).map PqxdhPhase2GapDhSource.word)
  | .BeaconOneTime => nativeOption ((setup.dh.dh oneTime (PqxdhPhase2GapDhSource.peer request.public_key)).map PqxdhRootTableInitialization.rootArray)
  | .ServerEphemeral => .None

/-- Every native role-DH getter computes the actual source value without a further request or state change. -/
theorem primitive_dh (setup : Setup base KemSK) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (request : agreement.DhRequest) :
    RegistrationNativeBeaconFrontend.primitive (n := n) (Auxiliary := Auxiliary) setup owner oneTime (.dh request) = pure (reply setup owner oneTime request) := by
  cases role : request.secret_role <;>
    simp only [RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon,
      RegistrationNativeKemInterface.other, simulateQ_spec_query, RegistrationNativeKemBackend.beaconOther,
      RegistrationNativeKemInterface.OtherRequest.primitive, RegistrationBeaconRoleBackend.native,
      RegistrationBeaconRoleBackend.localBackend, role, StateT.run, map_pure, StateT.monad_pure_def, StateT.pure,
      RegistrationNativeBeaconFrontend.sample, simulateQ_pure, Option.bind_some, reply]

/-- The native public converter uses the same complete source byte input and optional conversion result. -/
theorem primitive_public (setup : Setup base KemSK) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (key : Std.Array U8 32#usize) :
    RegistrationNativeBeaconFrontend.primitive (n := n) (Auxiliary := Auxiliary) setup owner oneTime (.convertPublic key) =
      pure (RegistrationPublicConversion.convert setup.source.crypto key) := by
  simp only [RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon,
    RegistrationNativeKemInterface.other, simulateQ_spec_query, RegistrationNativeKemBackend.beaconOther,
    RegistrationNativeKemInterface.OtherRequest.primitive, RegistrationBeaconRoleBackend.native,
    RegistrationBeaconRoleBackend.localBackend, StateT.run, map_pure, StateT.monad_pure_def, StateT.pure,
    RegistrationNativeBeaconFrontend.sample, simulateQ_pure]

/-- The original identity conversion is answered from this owner's actual source identity seed. -/
theorem primitive_identity (setup : Setup base KemSK) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    RegistrationNativeBeaconFrontend.primitive (n := n) (Auxiliary := Auxiliary) setup owner oneTime (.convertSecret .LocalIdentity) =
      pure (RegistrationServerRoleBackend.selectedConversion setup.source.crypto (setup.secretOfSeed owner.identitySeed)) := by
  simp only [RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon,
    RegistrationNativeKemInterface.other, simulateQ_spec_query, RegistrationNativeKemBackend.beaconOther,
    RegistrationNativeKemInterface.OtherRequest.primitive, RegistrationBeaconRoleBackend.native,
    RegistrationBeaconRoleBackend.localBackend, StateT.run, map_pure, StateT.monad_pure_def,
    RegistrationNativeBeaconFrontend.sample, simulateQ_pure]

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before
private theorem state_modify_apply {S : Type} {m : Type → Type} [Monad m]
    (change : S → S) (before : S) : (modify change : StateT S m Unit) before = pure ((), change before) := rfl
private theorem state_pure_apply {S A : Type} {m : Type → Type} [Monad m]
    (value : A) (before : S) : (pure value : StateT S m A) before = pure (value, before) := rfl

/-- A literal pure primitive reply changes only the actual source request ledger under native lowering. -/
theorem pure_step (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Request) (answer : RegistrationAgreementExecutor.Spec.Range query)
    (primitive : RegistrationNativeBeaconFrontend.agreementCore (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup owner oneTime query = pure answer)
    (before : Local n KemSK source) :
    ((lower setup checks representation created (RegistrationNativeBeaconFrontend.agreement setup owner oneTime query)).run before) =
      pure (answer, (before.1, ({before.2.1 with requests := before.2.1.requests ++ RegistrationWorldAgreement.recorded query}, before.2.2))) := by
  rw [RegistrationNativeBeaconFrontend.agreement, lower_bind, primitive, lower_pure, StateT.run_bind]
  simp only [RegistrationNativeMldsaShared.lower, RegistrationNativeBeaconFrontend.updateEnv,
    StateT.run, StateT.lift, state_map_apply, state_modify_apply, state_pure_apply,
    bind_pure_comp, simulateQ_pure, map_pure]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeBeaconDhReplies

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconDhReplies.primitive_dh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconDhReplies.primitive_dh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconDhReplies.primitive_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconDhReplies.primitive_public

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconDhReplies.primitive_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconDhReplies.primitive_identity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconDhReplies.pure_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconDhReplies.pure_step
