-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldServerFrontend
import BeaconcryptCore.Computational.RegistrationPublicConversion

/-! The concrete Server role backend stores only its locally generated ephemeral scalar. The selected static identity is an opaque role: its fixed-shape conversion can be answered without its bytes, and its DH value is evaluated only by the private source/family interpretation. Encapsulation and all nonselected primitives use the existing source algorithms and their actual coins. The public preparation compiler contains no selected seed or raw selected DH output. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerRoleBackend
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity
open RegistrationAgreementShared (PrimitiveRequest PrimitiveSpec)
open RegistrationAgreementRoot (nativeOption)
variable {ι KemSK : Type} {base : OracleSpec ι}

/-- A known local ephemeral is the only secret stored in the public compiler's Server primitive state. -/
structure State where
  ephemeral : Option PqxdhJointGapDh.ScalarBytes

def empty : State := ⟨none⟩

/-- The native converted-key object is fixed width and represents the functional SDK conversion exactly. This ordinary representation contract is explicit because Crypto.xsk currently has no output-width field. -/
structure ConvertedIdentity (setup : Setup base KemSK) where
  converted : IdentitySeed → Std.Array U8 32#usize
  bytes : ∀ seed, absBytes (converted seed) = setup.source.crypto.xsk (setup.secretOfSeed seed).toList

/-- Selected identity conversion exposes only validity of its generated 32-byte converted-secret shape. -/
def selectedConversion (crypto : Pqxdh.Crypto) (secret : List.Vector UInt8 64) : Bool :=
  decide ((crypto.xsk secret.toList).length = 32)

theorem selected_conversion (setup : Setup base KemSK) (representation : ConvertedIdentity setup)
    (seed : IdentitySeed) : selectedConversion setup.source.crypto (setup.secretOfSeed seed) = true := by
  simp only [selectedConversion, ← representation.bytes seed]
  have width : (absBytes (representation.converted seed)).length = 32 := by simp
  simp only [width, decide_true]

/-- No selected identity material occurs in this interpreter or its state. The unavailable DH branch is compiled to a reference by the existing public prefix. -/
noncomputable def localBackend (setup : Setup base KemSK) (checks : Checks) :
    QueryImpl PrimitiveSpec (StateT State ProbComp)
  | .convertPublic key => pure (RegistrationPublicConversion.convert setup.source.crypto key)
  | .convertSecret .LocalIdentity => pure true
  | .convertSecret .ServerEphemeral => fun state => pure (state.ephemeral.isSome, state)
  | .convertSecret .BeaconPrekey | .convertSecret .BeaconOneTime => pure false
  | .generate .ServerEphemeral => fun state =>
      (fun drawn => (nativeOption (drawn.map PqxdhServerRootPreparation.Ephemeral.publicKey),
        { state with ephemeral := drawn.map PqxdhServerRootPreparation.Ephemeral.secret })) <$>
        PqxdhServerAuthExperiment.generateEphemeral setup
  | .encapsulate .None => pure .None
  | .encapsulate (.Some key) =>
      if checks.kemKey (RegistrationRootInput.pqKey key) then
        StateT.lift (nativeOption <$> PqxdhServerAuthExperiment.encapsulate setup (RegistrationRootInput.pqKey key))
      else pure .None
  | .decapsulate _ => pure .None
  | .dh request => fun state =>
      match request.secret_role with
      | .ServerEphemeral => pure (nativeOption (state.ephemeral.bind fun scalar =>
          (PqxdhJointGapDh.sourceScalarDh setup.source.crypto scalar
            (PqxdhPhase2GapDhSource.peer request.public_key)).map PqxdhRootTableInitialization.rootArray), state)
      | _ => pure (.None, state)

/-- The actual selected seed exists only in this private source interpretation, never in Aux. -/
noncomputable def native (setup : Setup base KemSK) (checks : Checks) (_representation : ConvertedIdentity setup) (seed : IdentitySeed) :
    QueryImpl PrimitiveSpec (StateT State ProbComp)
  | .convertSecret .LocalIdentity => pure (selectedConversion setup.source.crypto (setup.secretOfSeed seed))
  | .dh request => match request.secret_role with
      | .LocalIdentity => pure (nativeOption ((setup.joint.staticDh seed (PqxdhPhase2GapDhSource.peer request.public_key)).map
          PqxdhRootTableInitialization.rootArray))
      | _ => localBackend setup checks (.dh request)
  | query => localBackend setup checks query

/-- Actual selected converter validity is derived from source-generated key shape, not supplied as a secure callback premise. -/
theorem native_conversion (setup : Setup base KemSK) (checks : Checks) (representation : ConvertedIdentity setup) (seed : IdentitySeed) :
    native setup checks representation seed (.convertSecret .LocalIdentity) = localBackend setup checks (.convertSecret .LocalIdentity) := by
  simp only [native, selected_conversion setup representation, localBackend]

/-- The actual private source controller is the existing selected-DH source interpreter of this concrete seed-free local backend. -/
theorem native_source (setup : Setup base KemSK) (checks : Checks)
    (representation : ConvertedIdentity setup) (seed : IdentitySeed) :
    RegistrationAgreementShared.implementation setup.source (native setup checks representation seed) =
      RegistrationAgreementInterpreter.sourceImpl setup.joint seed
        (RegistrationAgreementShared.implementation setup.source (localBackend setup checks)) (fun _ => pure ()) := by
  funext query before
  cases query with
  | convertSecret role => cases role <;> simp only [RegistrationAgreementShared.implementation,
      RegistrationAgreementShared.auxiliary, RegistrationAgreementInterpreter.sourceImpl, native,
      selected_conversion setup representation, localBackend, StateT.run, map_pure]
  | dh request =>
      cases role : request.secret_role <;>
        simp only [RegistrationAgreementShared.implementation, RegistrationAgreementShared.auxiliary,
          RegistrationAgreementInterpreter.sourceImpl, native, role, pure_bind, StateT.run]
      rfl
  | convertPublic key => rfl
  | generate role => rfl
  | encapsulate key => rfl
  | decapsulate ciphertext => rfl
  | root request => rfl

/-- Every actual public preparation callback is independent of selected seed bytes before family interpretation; DH remains an opaque public reference. -/
theorem prep_seed_erasure (setup : Setup base KemSK) (checks : Checks)
    (representation : ConvertedIdentity setup) (seed : IdentitySeed) :
    RegistrationAgreementInterpreter.prepImpl
        (RegistrationAgreementShared.implementation setup.source (native setup checks representation seed)) =
      RegistrationAgreementInterpreter.prepImpl
        (RegistrationAgreementShared.implementation setup.source (localBackend setup checks)) := by
  funext query
  cases query <;>
    simp only [RegistrationAgreementInterpreter.prepImpl, RegistrationAgreementRoot.callbacks,
      simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      simulateQ_pure, simulateQ_map]
  all_goals try rfl
  funext before
  simp only [RegistrationAgreementShared.implementation, RegistrationAgreementShared.auxiliary,
    native, localBackend, selected_conversion setup representation]

end BeaconcryptCore.Computational.RegistrationServerRoleBackend

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRoleBackend.selected_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRoleBackend.selected_conversion

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRoleBackend.native_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRoleBackend.native_conversion

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRoleBackend.native_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRoleBackend.native_source

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRoleBackend.prep_seed_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRoleBackend.prep_seed_erasure
