-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCommonSource
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeOwner

/-! The indexed identity frontend reuses the exact original first-record callbacks. Their existing owner-independence theorem justifies the empty-roster adapter; no owner metadata, record request, current Env or World effect is discarded by the source correspondence. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityRecordSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentitySourceSimulation
open RegistrationWorldAgreementCompiler (EnvState)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

private theorem liftOld_lift
    (work : StateT (EnvState Auxiliary) (OracleComp (RegistrationNativeIdentityFrontend.Ambient n KemSK)) Value) :
    RegistrationNativeIdentityFrontend.liftOld (source := source) (StateT.lift work) = liftAmbient work := by
  apply StateT.ext
  intro current
  apply StateT.ext
  intro env
  simp only [RegistrationNativeIdentityFrontend.liftOld, liftAmbient, StateT.run_lift,
    StateT.run_map, bind_pure_comp, Functor.map_map,
    id_map']

/-- Each actual first-record query uses the original source primitive and retains all request logs and reached World state. -/
theorem query_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (seeds : List PqxdhJointIdentity.IdentitySeed)
    (wire : RegistrationNativeWire.Wire) (query : RegistrationRecordPrimitives.Spec.Domain) :
    Related (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created seeds
      (RegistrationNativeIdentityFrontend.record setup wire query) (RegistrationNativeBeaconFrontend.record setup wire query) := by
  change Related setup checks representation created seeds
    (RegistrationNativeIdentityFrontend.liftOld (RegistrationNativeBeaconFrontend.record setup wire query)) _
  rw [RegistrationBeaconReferenceNativeOwner.record_owned (mlSource := source), liftOld_lift]
  exact related_lift setup checks representation created seeds _

theorem query_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (query : RegistrationRecordPrimitives.Spec.Domain) :
    Keeps (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created
      (RegistrationNativeIdentityFrontend.record setup wire query) := by
  change Keeps setup checks representation created
    (RegistrationNativeIdentityFrontend.liftOld (RegistrationNativeBeaconFrontend.record setup wire query))
  rw [RegistrationBeaconReferenceNativeOwner.record_owned (mlSource := source), liftOld_lift]
  exact keeps_lift setup checks representation created _

/-- The complete native sequence-one opening controller has the same optional results, consumed kernel, mutable Env and World. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (seeds : List PqxdhJointIdentity.IdentitySeed)
    (wire : RegistrationNativeWire.Wire) (work : OracleComp RegistrationRecordPrimitives.Spec Value) :
    Related (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created seeds
      (simulateQ (RegistrationNativeIdentityFrontend.record setup wire) work)
      (simulateQ (RegistrationNativeBeaconFrontend.record setup wire) work) :=
  related_program setup checks representation created seeds _ _
    (query_source setup checks representation created seeds wire)
    (query_keeps setup checks representation created wire) work

theorem program_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (work : OracleComp RegistrationRecordPrimitives.Spec Value) :
    Keeps (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created
      (simulateQ (RegistrationNativeIdentityFrontend.record setup wire) work) :=
  keeps_program setup checks representation created _ (query_keeps setup checks representation created wire) work

end BeaconcryptCore.Computational.RegistrationNativeIdentityRecordSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRecordSource.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRecordSource.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRecordSource.query_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRecordSource.query_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRecordSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRecordSource.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRecordSource.program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRecordSource.program_keeps
