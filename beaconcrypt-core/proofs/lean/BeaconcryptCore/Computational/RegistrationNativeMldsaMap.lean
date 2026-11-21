-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicFrontend
import BeaconcryptCore.Computational.RegistrationNativeExperiment

/-! A source key map replaces only the private Server ML signing-key representation. Beacon owner and pending-view conversions retag the source context and contain no ML secret. Every public key, pin, phase, identity, scalar, KEM handle, World owner and chronological receipt remains literal. Primitive leaf laws transport generation and complete signing requests without assuming key injectivity, key provenance or a protocol security conclusion. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaMap
open RegistrationNativeMldsa (Source Credential)
variable {left right : Source}

structure Map (left right : Source) where
  key : left.SigningKey → right.SigningKey

def credential (mapping : Map left right) (current : Credential left) : Credential right :=
  ⟨current.publicKey, mapping.key current.secret⟩

def owner (_ : Map left right) (current : RegistrationNativeBeaconFrontend.Owner left) : RegistrationNativeBeaconFrontend.Owner right :=
  ⟨current.pin, current.identitySeed, current.prekeyScalar, current.prekeyPublic,
    current.kemHandle, current.kemPublic, current.worldOwner, current.phase, current.edHistory⟩

def owners (mapping : Map left right) (current : RegistrationNativeBeaconFrontend.State left) : RegistrationNativeBeaconFrontend.State right :=
  current.map (owner mapping)

def prepared (_ : Map left right) (current : RegistrationNativeBeaconFrontend.Prepared left) : RegistrationNativeBeaconFrontend.Prepared right :=
  ⟨current.pin, current.identity, current.prekey⟩

def selectedOwner (_ : Map left right) (current : RegistrationBeaconReferenceCompiler.SelectedOwner left) : RegistrationBeaconReferenceCompiler.SelectedOwner right :=
  ⟨current.pin, current.identitySeed, current.prekeyPublic,
    current.kemHandle, current.kemPublic, current.worldOwner, current.phase, current.edHistory⟩

def publicOwner (mapping : Map left right) (current : RegistrationNativePublicOwners.Owner left) : RegistrationNativePublicOwners.Owner right :=
  ⟨selectedOwner mapping current.view, current.scalar⟩

def publicState (mapping : Map left right) (current : RegistrationNativePublicFrontend.State left) : RegistrationNativePublicFrontend.State right :=
  ⟨current.server, current.beacons.map (publicOwner mapping), current.environment, current.parsedAccepts⟩

def nativeState {n : Nat} {KemSK : Type} (mapping : Map left right) (current : RegistrationNativeExperiment.State n KemSK left) : RegistrationNativeExperiment.State n KemSK right :=
  ⟨current.server, owners mapping current.beacons, current.pool, current.parsedAccepts⟩

def initial {n : Nat} {KemSK : Type} (mapping : Map left right) (current : RegistrationNativeExperiment.Initial n KemSK left) : RegistrationNativeExperiment.Initial n KemSK right :=
  ⟨current.created, credential mapping current.credential, nativeState mapping current.state⟩

@[simp] theorem credential_public (mapping : Map left right) (current : Credential left) :
    (credential mapping current).publicKey = current.publicKey := rfl

/-- All non-ML-secret owner fields are unchanged, including the complete signing history. -/
theorem owner_fields (mapping : Map left right) (current : RegistrationNativeBeaconFrontend.Owner left) :
    (owner mapping current).pin = current.pin ∧ (owner mapping current).identitySeed = current.identitySeed ∧
    (owner mapping current).prekeyScalar = current.prekeyScalar ∧ (owner mapping current).prekeyPublic = current.prekeyPublic ∧
    (owner mapping current).kemHandle = current.kemHandle ∧ (owner mapping current).kemPublic = current.kemPublic ∧
    (owner mapping current).worldOwner = current.worldOwner ∧ (owner mapping current).phase = current.phase ∧
    (owner mapping current).edHistory = current.edHistory := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

@[simp] theorem owners_lookup (mapping : Map left right) (current : RegistrationNativeBeaconFrontend.State left) (index : Nat) :
    (owners mapping current)[index]? = (current[index]?).map (owner mapping) := by
  simp only [owners, List.getElem?_map]

@[simp] theorem owners_set (mapping : Map left right) (current : RegistrationNativeBeaconFrontend.State left)
    (index : Nat) (updated : RegistrationNativeBeaconFrontend.Owner left) :
    owners mapping (current.set index updated) = (owners mapping current).set index (owner mapping updated) := by
  simp only [owners, List.map_set]

@[simp] theorem owners_append (mapping : Map left right) (first second : RegistrationNativeBeaconFrontend.State left) :
    owners mapping (first ++ second) = owners mapping first ++ owners mapping second := by
  simp only [owners, List.map_append]

@[simp] theorem owner_phase (mapping : Map left right) (current : RegistrationNativeBeaconFrontend.Owner left) (phase : RegistrationNativeBeaconFrontend.Phase) :
    owner mapping { current with phase } = { owner mapping current with phase } := rfl

@[simp] theorem owner_history (mapping : Map left right) (current : RegistrationNativeBeaconFrontend.Owner left) (history : PqxdhJointIdentity.History) :
    owner mapping { current with edHistory := history } = { owner mapping current with edHistory := history } := rfl

@[simp] theorem erase_owner (mapping : Map left right) (current : RegistrationNativeBeaconFrontend.Owner left) :
    RegistrationBeaconReferenceCompiler.eraseOwner (owner mapping current) =
      selectedOwner mapping (RegistrationBeaconReferenceCompiler.eraseOwner current) := rfl

@[simp] theorem restore_owner (mapping : Map left right) (scalar : PqxdhJointGapDh.ScalarBytes) (current : RegistrationBeaconReferenceCompiler.SelectedOwner left) :
    RegistrationBeaconReferenceCompiler.restoreOwner scalar (selectedOwner mapping current) =
      owner mapping (RegistrationBeaconReferenceCompiler.restoreOwner scalar current) := rfl

@[simp] theorem public_restore (mapping : Map left right) (current : RegistrationNativePublicOwners.Owner left) :
    RegistrationNativePublicOwners.restore (publicOwner mapping current) = owner mapping (RegistrationNativePublicOwners.restore current) := rfl

@[simp] theorem initial_public {n : Nat} {KemSK : Type} (mapping : Map left right) (current : RegistrationNativeExperiment.Initial n KemSK left) :
    (initial mapping current).public = current.public := rfl

/-- These are primitive functional equalities on the same complete public-key and signing operands. -/
structure Laws (mapping : Map left right) : Prop where
  verify : left.verify = right.verify
  generate : Option.map (Prod.map id mapping.key) <$> left.generate = right.generate
  sign : ∀ key request, left.sign key request = right.sign (mapping.key key) request

/-- Optional generation failure and each returned public/private pair are mapped literally. -/
theorem generate (mapping : Map left right) (laws : Laws mapping) :
    Option.map (credential mapping) <$> RegistrationNativeMldsa.generate left = RegistrationNativeMldsa.generate right := by
  unfold RegistrationNativeMldsa.generate
  rw [← laws.generate, Functor.map_map, Functor.map_map]
  congr 1
  funext value
  cases value with
  | none => rfl
  | some pair => rfl

/-- A pool-dependent implementation needs only the one reached credential's complete signing request equality. -/
theorem owned_request (mapping : Map left right) (current : Credential left)
    (request : beaconcrypt_core.registration.MldsaSigningRequest)
    (signed : left.sign current.secret request = right.sign (mapping.key current.secret) request) :
    RegistrationNativeMldsa.owned left current request = RegistrationNativeMldsa.owned right (credential mapping current) request := by
  classical
  by_cases matching : request.public_key = current.publicKey
  · rw [RegistrationNativeMldsa.owned_match left current request matching,
      RegistrationNativeMldsa.owned_match right (credential mapping current) request (show request.public_key = (credential mapping current).publicKey from matching)]
    exact signed
  · rw [RegistrationNativeMldsa.owned_mismatch left current request matching,
      RegistrationNativeMldsa.owned_mismatch right (credential mapping current) request (show request.public_key ≠ (credential mapping current).publicKey from matching)]

/-- An unowned request remains a literal failure; an owned request retains its complete source signing operands. -/
theorem owned (mapping : Map left right) (laws : Laws mapping) (current : Credential left)
    (request : beaconcrypt_core.registration.MldsaSigningRequest) :
    RegistrationNativeMldsa.owned left current request = RegistrationNativeMldsa.owned right (credential mapping current) request :=
  owned_request mapping current request (laws.sign current.secret request)

end BeaconcryptCore.Computational.RegistrationNativeMldsaMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMap.credential_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMap.credential_public

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMap.owner_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMap.owner_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMap.owners_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMap.owners_lookup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMap.owners_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMap.owners_set

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMap.owners_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMap.owners_append

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMap.owner_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMap.owner_phase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMap.owner_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMap.owner_history

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMap.erase_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMap.erase_owner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMap.restore_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMap.restore_owner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMap.public_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMap.public_restore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMap.initial_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMap.initial_public

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMap.generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMap.generate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMap.owned_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMap.owned_request

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMap.owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMap.owned
