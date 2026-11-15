-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCommonSource
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCallbacks

/-! Only the actual local-identity conversion and DH getter depend on the Beacon identity seed. All other ordinary agreement callbacks are the existing native programs with the fixed dummy identity, including the same request logging, indexed KEM work and optional errors. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementShape
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open RegistrationNativeIdentityFrontend (Owner)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

def Other : RegistrationAgreementExecutor.Request → Prop
  | .convertSecret role => role ≠ .LocalIdentity
  | .dh request => request.secret_role ≠ .LocalIdentity
  | _ => True

/-- Outside the two identity operations, the original agreement callback does not inspect the privately generated seed. -/
theorem original_other (setup : Setup base KemSK) (owner : Owner source) (first second : IdentitySeed)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Request) (ordinary : Other query) :
    RegistrationNativeBeaconFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup
      (RegistrationNativeIdentityFrontend.restore first owner) oneTime query =
      RegistrationNativeBeaconFrontend.agreement setup (RegistrationNativeIdentityFrontend.restore second owner) oneTime query := by
  cases query with
  | convertPublic key | generate role | encapsulate key | root request =>
      simp only [RegistrationNativeBeaconFrontend.agreement, RegistrationNativeBeaconFrontend.agreementCore,
        RegistrationNativeBeaconFrontend.primitive, RegistrationNativeIdentityFrontend.restore,
        RegistrationNativeKemInterface.beacon, RegistrationNativeKemInterface.other, simulateQ_spec_query,
        simulateQ_pure, RegistrationNativeKemBackend.beaconOther, RegistrationNativeKemInterface.OtherRequest.primitive,
        RegistrationBeaconRoleBackend.native, RegistrationBeaconRoleBackend.localBackend,
        RegistrationNativeBeaconFrontend.sample, StateT.run, map_pure, StateT.monad_pure_def, StateT.pure]
  | decapsulate ciphertext =>
      cases ciphertext <;>
        simp only [RegistrationNativeBeaconFrontend.agreement, RegistrationNativeBeaconFrontend.agreementCore,
          RegistrationNativeBeaconFrontend.primitive, RegistrationNativeIdentityFrontend.restore,
          RegistrationNativeKemInterface.beacon, simulateQ_pure, simulateQ_map,
          simulateQ_spec_query, RegistrationNativeBeaconFrontend.sample]
  | convertSecret role =>
      cases role
      all_goals first
        | exact False.elim (ordinary rfl)
        | simp only [RegistrationNativeBeaconFrontend.agreement, RegistrationNativeBeaconFrontend.agreementCore,
            RegistrationNativeBeaconFrontend.primitive, RegistrationNativeIdentityFrontend.restore,
            RegistrationNativeKemInterface.beacon, RegistrationNativeKemInterface.other, simulateQ_spec_query,
            simulateQ_pure, RegistrationNativeKemBackend.beaconOther, RegistrationNativeKemInterface.OtherRequest.primitive,
            RegistrationBeaconRoleBackend.native, RegistrationBeaconRoleBackend.localBackend,
            RegistrationNativeBeaconFrontend.sample, StateT.run, map_pure, StateT.monad_pure_def, StateT.pure]
  | dh request =>
      cases role : request.secret_role
      all_goals first
        | exact False.elim (ordinary role)
        | simp only [RegistrationNativeBeaconFrontend.agreement, RegistrationNativeBeaconFrontend.agreementCore,
            RegistrationNativeBeaconFrontend.primitive, RegistrationNativeIdentityFrontend.restore,
            RegistrationNativeKemInterface.beacon, RegistrationNativeKemInterface.other, simulateQ_spec_query,
            simulateQ_pure, RegistrationNativeKemBackend.beaconOther, RegistrationNativeKemInterface.OtherRequest.primitive,
            RegistrationBeaconRoleBackend.native, RegistrationBeaconRoleBackend.localBackend, role,
            RegistrationNativeBeaconFrontend.sample, StateT.run, map_pure, StateT.monad_pure_def, StateT.pure]

/-- The ordinary public callback is exactly the existing owner-independent native callback lifted through the public ambient interface. -/
theorem exposed_other (setup : Setup base KemSK) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Request) (ordinary : Other query) :
    RegistrationNativeIdentityFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup owner oneTime query =
      RegistrationNativeIdentityFrontend.liftOld
        (RegistrationNativeBeaconFrontend.agreement setup
          (RegistrationNativeIdentityFrontend.restore RegistrationNativeIdentityFrontend.dummyIdentity owner) oneTime query) := by
  apply StateT.ext
  intro current
  apply StateT.ext
  intro env
  cases query with
  | convertPublic key | generate role | encapsulate key | decapsulate ciphertext | root request =>
      simp only [RegistrationNativeIdentityFrontend.agreement, RegistrationNativeIdentityFrontend.agreementCore,
        RegistrationNativeIdentityFrontend.primitive, RegistrationNativeBeaconFrontend.agreement,
        RegistrationNativeBeaconFrontend.agreementCore, RegistrationNativeIdentityFrontend.restore,
        RegistrationNativeIdentityFrontend.updateEnv, RegistrationNativeBeaconFrontend.updateEnv,
        RegistrationNativeIdentityFrontend.liftOld, StateT.run_bind, StateT.run_lift, StateT.run_modify,
        StateT.run_map, bind_pure_comp, simulateQ_bind, simulateQ_map,
        simulateQ_pure, Functor.map_map]
      simp only [StateT.run, map_pure, pure_bind, Functor.map_map]
      all_goals rfl
  | convertSecret role =>
      cases role
      all_goals first
        | exact False.elim (ordinary rfl)
        | simp only [RegistrationNativeIdentityFrontend.agreement, RegistrationNativeIdentityFrontend.agreementCore,
            RegistrationNativeIdentityFrontend.primitive, RegistrationNativeBeaconFrontend.agreement,
            RegistrationNativeBeaconFrontend.agreementCore, RegistrationNativeIdentityFrontend.restore,
            RegistrationNativeIdentityFrontend.updateEnv, RegistrationNativeBeaconFrontend.updateEnv,
            RegistrationNativeIdentityFrontend.liftOld, StateT.run_bind, StateT.run_lift, StateT.run_modify,
            StateT.run_map, bind_pure_comp, simulateQ_bind, simulateQ_map,
            simulateQ_pure]
      all_goals simp only [StateT.run, map_pure, pure_bind, Functor.map_map]
      all_goals rfl
  | dh request =>
      cases role : request.secret_role
      all_goals first
        | exact False.elim (ordinary role)
        | simp only [RegistrationNativeIdentityFrontend.agreement, RegistrationNativeIdentityFrontend.agreementCore,
            RegistrationNativeIdentityFrontend.primitive, RegistrationNativeBeaconFrontend.agreement,
            RegistrationNativeBeaconFrontend.agreementCore, RegistrationNativeIdentityFrontend.restore, role,
            RegistrationNativeIdentityFrontend.updateEnv, RegistrationNativeBeaconFrontend.updateEnv,
            RegistrationNativeIdentityFrontend.liftOld, StateT.run_bind, StateT.run_lift, StateT.run_modify,
            StateT.run_map, bind_pure_comp, simulateQ_bind, simulateQ_map,
            simulateQ_pure]
      all_goals simp only [StateT.run, map_pure, pure_bind, Functor.map_map]
      all_goals rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementShape

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementShape.original_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementShape.original_other

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementShape.exposed_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementShape.exposed_other
