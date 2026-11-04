-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOwnerRoster
import BeaconcryptCore.Computational.RegistrationNativeScalarRoster

/-! Every reached original native owner retains the exact public prekey computed from its actual generated private prekey scalar. Birth establishes this source relation, and immutable owner metadata preserves it through every lifecycle outcome. No public-key injectivity, partner completion or shared-root equality is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePrekeyCoherence
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeOwnerFields (metadata)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def Coherent (setup : Setup base KemSK) (owner : Owner source) : Prop :=
  owner.prekeyPublic = PqxdhRootTableInitialization.rootArray (setup.dh.publicKey owner.prekeyScalar)

def Holds (setup : Setup base KemSK) (owners : RegistrationNativeBeaconFrontend.State source) : Prop :=
  ∀ owner ∈ owners, Coherent setup owner

theorem metadata_transport (setup : Setup base KemSK)
    (before after : RegistrationNativeBeaconFrontend.State source)
    (same : after.map metadata = before.map metadata) (prior : Holds setup before) : Holds setup after := by
  intro owner member
  have mapped : metadata owner ∈ before.map metadata := by
    rw [← same]
    exact List.mem_map.mpr ⟨owner, member, rfl⟩
  obtain ⟨earlier, reached, equal⟩ := List.mem_map.mp mapped
  have coherent : Coherent setup (metadata earlier) := prior earlier reached
  rw [equal] at coherent
  exact coherent

/-- The actual constructor computes each new public prekey from the exact generated scalar stored beside it; all rejected prefixes preserve old owners. -/
theorem create (setup : Setup base KemSK)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeBeaconFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (prior : Holds setup owners)
    (result : (RustM (Option Nat) × RegistrationNativeBeaconFrontend.State source) ×
      RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (supported : result ∈ support
      (((RegistrationNativeBeaconFrontend.create (n := n) setup source edPin mlPin keyId).run owners).run env)) :
    Holds setup result.1.2 := by
  rw [RegistrationNativeBeaconBirth.create_program] at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨earlier, reached, continued⟩ := supported
  have retained := RegistrationNativeKemBirthOwners.prepare_owners edPin mlPin keyId owners env earlier reached
  cases actual : earlier.1.1 with
  | fail error | div =>
    simp only [actual, support_pure, Set.mem_singleton_iff] at continued
    cases continued
    rw [retained]
    exact prior
  | ok result => cases result with
    | none =>
      simp only [actual, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      rw [retained]
      exact prior
    | some prepared =>
      simp only [actual] at continued
      rw [RegistrationNativeBeaconBirth.append_program] at continued
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at continued
      obtain ⟨born, _born, worldOwner, _allocated, returned⟩ := continued
      cases returned
      rw [retained]
      intro owner member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · exact prior owner old
      · rfl

private theorem beacon (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (law : ∀ owners env result, Holds setup owners → result ∈ support ((work.run owners).run env) → Holds setup result.1.2)
    (before : RegistrationNativeExperiment.State n KemSK source) (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (prior : Holds setup before.beacons)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)) :
    Holds setup result.2.beacons := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  apply law before.beacons (RegistrationWorldAgreementCompiler.erase before.server.world) inner.1 prior
  apply OracleComp.support_simulateQ_run'_subset
    (RegistrationNativeExperiment.trusted setup checks representation created source) _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst possible

/-- All original typed callbacks preserve prekey/scalar coherence, including successful creation and every failed source continuation. -/
theorem handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : RegistrationNativeExperiment.State n KemSK source)
    (prior : Holds setup before.beacons)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential query).run before)) :
    Holds setup result.2.beacons := by
  by_cases born : ∃ edPin mlPin keyId, query = .inr (.create edPin mlPin keyId)
  · obtain ⟨edPin, mlPin, keyId, rfl⟩ := born
    exact beacon setup checks representation created _ (fun _ _ _ valid reached => create setup edPin mlPin keyId _ _ valid _ reached)
      before result prior supported
  · have quiet : ∀ edPin mlPin keyId, query ≠ .inr (.create edPin mlPin keyId) :=
      fun edPin mlPin keyId equal => born ⟨edPin, mlPin, keyId, equal⟩
    obtain ⟨tail, same⟩ := RegistrationNativeOwnerRoster.typed_prefix setup checks wire route representation created credential query before result supported
    have lengthEq := RegistrationNativeScalarRoster.noncreate_length setup checks wire route representation created credential query quiet before result supported
    have sizes := congrArg List.length same
    simp only [List.length_map, List.length_append, lengthEq] at sizes
    have empty : tail = [] := List.length_eq_zero_iff.mp (by omega)
    rw [empty, List.append_nil] at same
    exact metadata_transport setup before.beacons result.2.beacons same prior

theorem program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : RegistrationNativeExperiment.State n KemSK source)
    (prior : Holds setup before.beacons) (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((simulateQ
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) work).run before)) :
    Holds setup result.2.beacons := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query
    (RegistrationNativeExperiment.handler setup checks wire route representation created source credential)
    (fun current => Holds setup current.beacons)
    (fun query current valid next reached => handler setup checks wire route representation created credential query current valid next reached)
    work before prior result supported

theorem start (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (supported : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    Holds setup initial.state.beacons := by
  simp only [RegistrationNativeExperiment.start, mem_support_bind_iff] at supported
  obtain ⟨constructed, _constructed, continued⟩ := supported
  cases built : constructed.1.1 with
  | none => simp only [built, mem_support_pure_iff] at continued; cases continued
  | some created =>
    simp only [built, mem_support_bind_iff] at continued
    obtain ⟨generated, _generated, continued⟩ := continued
    cases chosen : generated.1 with
    | none => simp only [chosen, mem_support_pure_iff] at continued; cases continued
    | some credential =>
      simp only [chosen, mem_support_bind_iff] at continued
      obtain ⟨initialized, _reached, returned⟩ := continued
      cases native : initialized.1 with
      | fail error | div => simp only [native, mem_support_pure_iff] at returned; cases returned
      | ok reply => cases reply with
        | none => simp only [native, mem_support_pure_iff] at returned; cases returned
        | some state =>
          simp only [native, mem_support_pure_iff, Option.some.injEq] at returned
          cases returned
          intro owner member
          cases member

/-- Every owner reached from actual initialized startup has the literal source prekey/scalar relation. -/
theorem initialized (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((simulateQ
      (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential) work).run initial.state)) :
    Holds setup result.2.beacons :=
  program setup checks wire route representation initial.created initial.credential work initial.state
    (start setup ensureInit identityIndex serverKeyId initial started) result supported

theorem initialized_owner (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((simulateQ
      (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential) work).run initial.state))
    (index : Nat) (owner : Owner source) (found : result.2.beacons[index]? = some owner) :
    owner.prekeyPublic = PqxdhRootTableInitialization.rootArray (setup.dh.publicKey owner.prekeyScalar) :=
  initialized setup checks wire route representation ensureInit identityIndex serverKeyId initial started work result supported
    owner (List.mem_of_getElem? found)

end BeaconcryptCore.Computational.RegistrationNativePrekeyCoherence

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePrekeyCoherence.metadata_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePrekeyCoherence.metadata_transport

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePrekeyCoherence.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePrekeyCoherence.create

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePrekeyCoherence.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePrekeyCoherence.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePrekeyCoherence.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePrekeyCoherence.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePrekeyCoherence.start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePrekeyCoherence.start

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePrekeyCoherence.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePrekeyCoherence.initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePrekeyCoherence.initialized_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePrekeyCoherence.initialized_owner
