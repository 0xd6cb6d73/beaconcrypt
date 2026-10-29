-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerRoleBackend
import BeaconcryptCore.Computational.RegistrationWorldBeaconRoot

/-! The Beacon owns its ordinary local identity, one-time scalar and ML-KEM key. The selected prekey scalar occurs only in the private source/family interpretation. Public preparation stores an opaque prekey role and records both actual public DH operands; decapsulation and all other local operations execute the existing source primitives with their actual optional replies and coins. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconRoleBackend
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity
open PqxdhJointGapDh (ScalarBytes)
open RegistrationAgreementShared (PrimitiveSpec)
open RegistrationAgreementRoot (nativeOption)
variable {ι KemSK : Type} {base : OracleSpec ι}

/-- Locally owned material excludes the selected Beacon prekey scalar and selected Server identity seed. -/
structure State (KemSK : Type) where
  identity : IdentitySeed
  oneTime : Option ScalarBytes
  kem : Option KemSK

/-- The selected native scalar already has the exact converted-secret width. -/
def selectedConversion (scalar : ScalarBytes) : Bool :=
  decide ((PqxdhRootTableInitialization.rootArray scalar).val.length = 32)

theorem selected_conversion (scalar : ScalarBytes) : selectedConversion scalar = true := by
  simp only [selectedConversion, PqxdhRootTableInitialization.rootArray, List.length_map,
    List.Vector.toList_length, decide_true]

noncomputable def localBackend (setup : Setup base KemSK) : QueryImpl PrimitiveSpec (StateT (State KemSK) ProbComp)
  | .convertPublic key => pure (RegistrationPublicConversion.convert setup.source.crypto key)
  | .convertSecret .LocalIdentity => fun state =>
      pure (RegistrationServerRoleBackend.selectedConversion setup.source.crypto (setup.secretOfSeed state.identity), state)
  | .convertSecret .BeaconPrekey => pure true
  | .convertSecret .BeaconOneTime => fun state => pure (state.oneTime.isSome, state)
  | .convertSecret .ServerEphemeral => pure false
  | .generate _ => pure .None
  | .encapsulate _ => pure .None
  | .decapsulate .None => pure .None
  | .decapsulate (.Some ciphertext) => fun state =>
      match state.kem with
      | none => pure (.None, state)
      | some secret => (fun reply => (nativeOption (reply.map PqxdhRootTableInitialization.rootArray), state)) <$>
          simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
            (setup.kem.decaps secret (PqxdhPhase2InputBytes.ciphertext ciphertext))
  | .dh request => fun state =>
      match request.secret_role with
      | .LocalIdentity => pure (nativeOption ((setup.joint.staticDh state.identity
          (PqxdhPhase2GapDhSource.peer request.public_key)).map PqxdhRootTableInitialization.rootArray), state)
      | .BeaconOneTime => pure (nativeOption (state.oneTime.bind fun scalar =>
          (setup.dh.dh scalar (PqxdhPhase2GapDhSource.peer request.public_key)).map PqxdhRootTableInitialization.rootArray), state)
      | _ => pure (.None, state)

/-- Only this private interpretation receives the selected scalar; its public local state and callback ledger contain no scalar bytes. -/
noncomputable def native (setup : Setup base KemSK) (scalar : ScalarBytes) :
    QueryImpl PrimitiveSpec (StateT (State KemSK) ProbComp)
  | .convertSecret .BeaconPrekey => pure (selectedConversion scalar)
  | .dh request => match request.secret_role with
      | .BeaconPrekey => pure (nativeOption ((setup.dh.dh scalar
          (PqxdhPhase2GapDhSource.peer request.public_key)).map PqxdhPhase2GapDhSource.word))
      | _ => localBackend setup (.dh request)
  | query => localBackend setup query

/-- Concrete public conversion is already the source conversion, with the actual optional width parser. -/
theorem public_conversion (setup : Setup base KemSK) :
    RegistrationPublicConversion.primitive setup.source.crypto (localBackend setup) = localBackend setup := by
  funext query
  cases query <;> rfl

/-- Actual fixed-shape prekey conversion reveals only validity, derived from its native scalar representation. -/
theorem native_conversion (setup : Setup base KemSK) (scalar : ScalarBytes) :
    native setup scalar (.convertSecret .BeaconPrekey) = localBackend setup (.convertSecret .BeaconPrekey) := by
  simp only [native, selected_conversion, localBackend]

/-- The real source callback differs from the concrete public backend only at the selected private prekey DH operations. -/
theorem native_source (setup : Setup base KemSK) (scalar : ScalarBytes) :
    RegistrationAgreementShared.implementation setup.source (native setup scalar) =
      RegistrationBeaconRootInterpreter.sourceImpl setup.dh scalar
        (RegistrationAgreementShared.implementation setup.source (localBackend setup)) (fun _ => pure ()) := by
  funext query before
  cases query with
  | convertSecret role => cases role <;> simp only [RegistrationAgreementShared.implementation,
      RegistrationAgreementShared.auxiliary, RegistrationBeaconRootInterpreter.sourceImpl,
      native, selected_conversion, localBackend, StateT.run, map_pure]
  | dh request =>
      cases role : request.secret_role <;>
        simp only [RegistrationAgreementShared.implementation, RegistrationAgreementShared.auxiliary,
          RegistrationBeaconRootInterpreter.sourceImpl, native, role, pure_bind, StateT.run]
      rfl
  | convertPublic key => rfl
  | generate role => rfl
  | encapsulate key => rfl
  | decapsulate ciphertext => rfl
  | root request => rfl

/-- Every ordinary Beacon prefix callback is independent of selected scalar bytes; the selected prekey positions are supplied by the public reference compiler. -/
theorem aux_scalar_erasure (setup : Setup base KemSK) (scalar : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) :
    RegistrationBeaconRootInterpreter.auxImpl
        (RegistrationAgreementShared.implementation setup.source (native setup scalar)) authenticated =
      RegistrationBeaconRootInterpreter.auxImpl
        (RegistrationAgreementShared.implementation setup.source (localBackend setup)) authenticated := by
  funext query
  cases query <;> simp only [RegistrationBeaconRootInterpreter.auxImpl, RegistrationBeaconAgreementRoot.callbacks,
    simulateQ_pure, simulateQ_map, simulateQ_spec_query]
  all_goals rfl


/-- The full World records the actual selected DH operand in the same position and retains its existing cache and signing receipts. -/
theorem native_world {n : Nat} (setup : Setup base KemSK) (scalar : ScalarBytes) :
    RegistrationWorldAgreement.agreement (n := n) setup.source (native setup scalar) =
      RegistrationBeaconRootInterpreter.sourceImpl setup.dh scalar
        (RegistrationWorldAgreement.agreement setup.source (localBackend setup)) RegistrationWorldBeaconRoot.visit := by
  funext query before
  cases query with
  | convertSecret role =>
      cases role <;> simp only [RegistrationBeaconRootInterpreter.sourceImpl,
        RegistrationWorldAgreement.agreement, RegistrationAgreementShared.auxiliary,
        native, localBackend, selected_conversion]
  | dh request =>
      cases role : request.secret_role with
      | BeaconPrekey =>
        simp only [RegistrationBeaconRootInterpreter.sourceImpl, role,
          RegistrationWorldAgreement.agreement, RegistrationAgreementShared.auxiliary,
          native, PqxdhRecordLiftWorld.sampled, simulateQ_pure,
          bind_pure_comp, map_pure, RegistrationWorldAgreement.recorded,
          StateT.run, StateT.monad_pure_def, StateT.pure]
        cases request
        cases role
        rfl
      | LocalIdentity | ServerEphemeral | BeaconOneTime =>
        simp only [RegistrationBeaconRootInterpreter.sourceImpl, RegistrationWorldAgreement.agreement,
          RegistrationAgreementShared.auxiliary, native, role]
  | root request => rfl
  | convertPublic key => rfl
  | generate role => rfl
  | encapsulate key => rfl
  | decapsulate ciphertext => rfl

/-- Actual public prefix execution, including its World request instrumentation, contains no selected scalar or selected DH reply. -/
theorem world_aux_scalar_erasure {n : Nat} (setup : Setup base KemSK) (scalar : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) :
    RegistrationBeaconRootInterpreter.auxImpl
        (RegistrationWorldAgreement.agreement (n := n) setup.source (native setup scalar)) authenticated =
      RegistrationBeaconRootInterpreter.auxImpl
        (RegistrationWorldAgreement.agreement setup.source (localBackend setup)) authenticated := by
  funext query
  cases query <;> simp only [RegistrationBeaconRootInterpreter.auxImpl, RegistrationBeaconAgreementRoot.callbacks,
    simulateQ_pure, simulateQ_map, simulateQ_spec_query]
  all_goals rfl

end BeaconcryptCore.Computational.RegistrationBeaconRoleBackend

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRoleBackend.selected_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRoleBackend.selected_conversion

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRoleBackend.public_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRoleBackend.public_conversion

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRoleBackend.native_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRoleBackend.native_conversion

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRoleBackend.native_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRoleBackend.native_source

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRoleBackend.aux_scalar_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRoleBackend.aux_scalar_erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRoleBackend.native_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRoleBackend.native_world

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRoleBackend.world_aux_scalar_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRoleBackend.world_aux_scalar_erasure
