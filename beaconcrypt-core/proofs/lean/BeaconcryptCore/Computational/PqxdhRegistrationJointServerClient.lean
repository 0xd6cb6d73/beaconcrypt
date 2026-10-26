-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule

/-! The existing public one-Server/many-Beacon command client is executed with the initialized indexed Server backend. Neither the client nor its backend carries a generated Server seed parameter. The source equality below uses actual supported complete states, not an honest-target restriction. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointServiceSchedule (Spec Client poolLift finishLift birth create bundle finish)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry EncodedState encodeEntry encodeState)
open PqxdhRegistrationJointFinish (onPool onNative)
open PqxdhRegistrationJointLiveRead (ReadSpec sourceStep clientStep entry_source)
open PqxdhBeaconPhase2Preparation (Word32)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- Beacon private operations and all shared Server/public callbacks use one complete service/native state, without exposing the initialized Server seed. -/
noncomputable def impl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) :
    QueryImpl (Spec KemSK Response) (StateT (PqxdhRegistrationJointFinish.State KemSK) ProbComp)
  | .inl query => PqxdhRegistrationJointFinishCompiler.impl setup codec query
  | .inr query => PqxdhRegistrationJointPublicShared.client setup codec checks identityIndex publicIdentity query

/-- The same complete state reassociation as the existing client, now with the seedless shared backend. -/
noncomputable def execute (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (client : Client KemSK Response Result)
    (state : EncodedState KemSK) : ProbComp (Result × EncodedState KemSK) :=
  (fun result => (result.1.1, ⟨result.2.1, result.2.2, result.1.2⟩)) <$>
    (simulateQ (impl setup codec checks identityIndex publicIdentity) (client.run state.owners)).run (state.pool, state.shared)

/-- A whole private-service client retains the complete shared native state while updating both private pools and their histories. -/
theorem pool_program (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (identityIndex : Nat) (publicIdentity : PublicIdentity) (program : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result)
    (state : PqxdhRegistrationJointFinish.State KemSK) :
    (simulateQ (impl setup codec checks identityIndex publicIdentity) (simulateQ poolLift program)).run state =
      (fun result => (result.1, (result.2, state.2))) <$>
        (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem) program).run state.1 := by
  rw [← QueryImpl.simulateQ_compose]
  have routed : impl setup codec checks identityIndex publicIdentity ∘ₛ poolLift =
      fun query => onPool (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem query) := by
    funext query
    exact simulateQ_spec_query (impl setup codec checks identityIndex publicIdentity) (.inl (.inl query))
  rw [routed, PqxdhRegistrationJointFinish.pool_program]

/-- Routing the existing complete finish program preserves every native tail and private service reply and the entire product state. -/
theorem finish_program (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (program : OracleComp (PqxdhRegistrationJointFinishCompiler.Spec KemSK Response) Result) :
    simulateQ (impl setup codec checks identityIndex publicIdentity) (simulateQ finishLift program) =
      simulateQ (PqxdhRegistrationJointFinishCompiler.impl setup codec) program := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1; funext query
  exact simulateQ_spec_query (impl setup codec checks identityIndex publicIdentity) (.inl query)

/-- The actual source constructor and executable handle constructor have the same full encoded distribution, with identity, prekey and KEM generators in source order. -/
theorem create_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (identityIndex : Nat) (publicIdentity : PublicIdentity) (pin : Word32) (keyId : Std.U64)
    (state : PqxdhRegistrationJointSchedule.State KemSK) :
    execute setup codec checks identityIndex publicIdentity (create pin keyId) (encodeState setup state) =
      (fun result => (result.1, encodeState setup result.2)) <$>
        (PqxdhRegistrationJointSchedule.create setup pin keyId).run state := by
  simp only [execute, StateT.run, create, bind_pure_comp, simulateQ_map]
  change _ <$> StateT.run (_ <$> _) _ = _
  rw [StateT.run_map, pool_program, PqxdhRegistrationJointCreation.client_material]
  simp only [PqxdhRegistrationJointSchedule.create, Functor.map_map]
  congr 1; funext value
  simp [encodeState, encodeEntry, PqxdhRegistrationJointSchedule.created,
    PqxdhRegistrationJointSchedule.birth, PqxdhRegistrationJointCreation.serviceView, birth,
    PqxdhRegistrationJointBundle.encode, PqxdhBeaconPhase1Publication.mapState,
    PqxdhBeaconPhase1Publication.mapPhase, PqxdhRegistrationJointBundle.identityMap,
    PqxdhRegistrationJointBundle.keyMap]

/-- Under the source-generated ownership invariant, every optional bundle result reinstalls the exact encoded source owner and retains all other owners, service histories and shared state. -/
theorem bundle_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (identityIndex : Nat) (publicIdentity : PublicIdentity) (address : Nat)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (owned : PqxdhRegistrationJointSchedule.Invariant state) :
    execute setup codec checks identityIndex publicIdentity (bundle setup codec address) (encodeState setup state) =
      (fun result => (result.1, encodeState setup result.2)) <$>
        (PqxdhRegistrationJointSchedule.bundle setup codec address).run state := by
  cases found : state.owners[address]? with
  | none =>
      simp [execute, StateT.run, bundle, encodeState, List.getElem?_map, found,
        PqxdhRegistrationJointSchedule.bundle]
      rfl
  | some entry =>
      simp only [execute, StateT.run, bundle, encodeState, List.getElem?_map, found,
        Option.map_some, encodeEntry, simulateQ_map]
      change _ <$> StateT.run (_ <$> _) _ = _
      rw [StateT.run_map, pool_program, PqxdhRegistrationJointBundleCompiler.bundle_source setup codec
        entry.identityIndex entry.kemIndex entry.owner state.pool
        (owned entry (List.mem_of_getElem? found)).1]
      simp [PqxdhRegistrationJointSchedule.bundle, found, Functor.map_map, encodeEntry]

/-- Every raw finish attempt uses the selected source-owned identity/KEM slots and reinstalls the complete optional native result without changing any other owner. -/
theorem finish_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (identityIndex : Nat) (publicIdentity : PublicIdentity) (address : Nat) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (owned : PqxdhRegistrationJointSchedule.Invariant state) :
    execute setup codec checks identityIndex publicIdentity (finish setup codec address raw) (encodeState setup state) =
      (fun result => (result.1, encodeState setup result.2)) <$>
        (PqxdhRegistrationJointSchedule.finish setup codec address raw).run state := by
  cases found : state.owners[address]? with
  | none =>
      simp [execute, StateT.run, finish, encodeState, List.getElem?_map, found,
        PqxdhRegistrationJointSchedule.finish]
      rfl
  | some entry =>
      simp only [execute, StateT.run, finish, encodeState, List.getElem?_map, found,
        Option.map_some, encodeEntry, simulateQ_map]
      change _ <$> StateT.run (_ <$> _) _ = _
      rw [StateT.run_map, finish_program, PqxdhRegistrationJointCompiledOwner.owner_source setup codec
        entry.identityIndex entry.kemIndex entry.owner raw (state.pool, state.shared)
        (owned entry (List.mem_of_getElem? found)).1
        (fun control prekey oneTime keys phase => (owned entry (List.mem_of_getElem? found)).2 keys
          (by simp only [PqxdhRegistrationJointOwnership.activeKey, phase]))]
      simp [PqxdhRegistrationJointSchedule.finish, found, Functor.map_map, encodeEntry]


/-- Every shared command runs the exact indexed source callback and preserves the entire reinstalled owner list and both backend states. -/
theorem shared_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (query : PqxdhRegistrationJointServiceSchedule.SharedSpec.Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (owned : state.pool.1.seeds[identityIndex]? = some seed) :
    execute setup codec checks identityIndex (setup.joint.publicKeys seed)
      (StateT.lift ((Spec KemSK Response).query (.inr query))) (encodeState setup state) =
      (fun result => (result.1, encodeState setup result.2)) <$>
        (PqxdhRegistrationJointServerSchedule.onBackend
          (PqxdhRegistrationJointPublicShared.source setup codec checks seed identityIndex query)).run state := by
  simp only [execute, StateT.run_lift, bind_pure_comp, simulateQ_map, StateT.run_map,
    simulateQ_spec_query, impl, encodeState, Functor.map_map]
  rw [PqxdhRegistrationJointPublicShared.query_source setup codec checks seed identityIndex query (state.pool, state.shared) owned]
  simp only [PqxdhRegistrationJointServerSchedule.onBackend, StateT.run, Functor.map_map]
  rfl
/-- The current-field read has exactly the source reply and full encoded poststate at every present or missing address. -/
theorem read_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (identityIndex : Nat) (publicIdentity : PublicIdentity) (request : Nat × PqxdhRegistrationJointLiveRead.Field)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (owned : PqxdhRegistrationJointSchedule.Invariant state) :
    execute setup codec checks identityIndex publicIdentity (clientStep request) (encodeState setup state) =
      pure ((sourceStep request state).1, encodeState setup (sourceStep request state).2) := by
  cases found : state.owners[request.1]? with
  | none =>
      simp [execute, StateT.run, clientStep, sourceStep, encodeState, List.getElem?_map, found]
      rfl
  | some entry =>
      simp only [execute, StateT.run, clientStep, encodeState,
        List.getElem?_map, found, Option.map_some, simulateQ_map]
      change _ <$> StateT.run (_ <$> _) _ = _
      rw [StateT.run_map, pool_program,
        entry_source setup request.2 entry state.pool (owned entry (List.mem_of_getElem? found))]
      simp [sourceStep, found]


/-- Lifting an unchanged native operation through the backend only reassociates state; every pool and owner field is retained. -/
theorem native_backend (work : NativeGame KemSK Result) (state : PqxdhRegistrationJointSchedule.State KemSK) :
    (PqxdhRegistrationJointServerSchedule.onBackend (onNative work)).run state =
      (PqxdhRegistrationJointSchedule.onShared work).run state := by
  simp only [PqxdhRegistrationJointServerSchedule.onBackend, onNative, PqxdhRegistrationJointSchedule.onShared,
    StateT.run, Functor.map_map]

/-- Each of the fourteen public command classes runs against the same initialized private Server slot and source-owned Beacon registry. Full replies and encoded poststate agree without rejecting any command because of ownership. -/
theorem query_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK)
    (owned : PqxdhRegistrationJointServerSchedule.Owned seed identityIndex state) :
    execute setup codec checks identityIndex (setup.joint.publicKeys seed)
      (PqxdhRegistrationJointRevealSchedule.client setup codec query) (encodeState setup state) =
      (fun result => (result.1, encodeState setup result.2)) <$>
        (PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex query).run state := by
  rcases query with (coin | request) | read
  case inl.inr =>
    cases request <;> first
    | exact create_source setup codec checks identityIndex (setup.joint.publicKeys seed) _ _ state
    | exact bundle_source setup codec checks identityIndex (setup.joint.publicKeys seed) _ state owned.1
    | exact finish_source setup codec checks identityIndex (setup.joint.publicKeys seed) _ _ state owned.1
    | exact shared_source setup codec checks seed identityIndex _ state owned.2
    | skip
    all_goals simp only [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointServiceSchedule.handler,
      PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
      PqxdhRegistrationJointSchedule.handler]
    all_goals rw [shared_source setup codec checks seed identityIndex _ state owned.2]
    all_goals simp only [PqxdhRegistrationJointPublicShared.source, native_backend]
    all_goals rfl
  case inl.inl =>
    simp [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointServiceSchedule.handler,
      PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
      execute, StateT.run_lift, bind_pure_comp, simulateQ_map, StateT.run_map, impl,
      PqxdhRegistrationJointFinishCompiler.impl, PqxdhRegistrationJointSchedule.handler, Functor.map_map]
    simp only [StateT.run, onPool, PqxdhLiveKemBirth.impl, encodeState, Functor.map_map]
    rfl
  case inr =>
    simpa only [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointServerSchedule.source,
      PqxdhRegistrationJointRevealSchedule.source, StateT.run, map_pure] using
      read_source setup codec checks identityIndex (setup.joint.publicKeys seed) read state owned.1
/-- Reassociating the client and backend state preserves the complete continuation, including every intermediate owner list and private/native poststate. -/
theorem execute_bind {Next : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : Client KemSK Response Result)
    (next : Result → Client KemSK Response Next) (state : EncodedState KemSK) :
    execute setup codec checks identityIndex publicIdentity (work >>= next) state =
      (execute setup codec checks identityIndex publicIdentity work state >>= fun result =>
        execute setup codec checks identityIndex publicIdentity (next result.1) result.2) := by
  simp only [execute, StateT.run_bind, simulateQ_bind, StateT.run_bind, map_bind, bind_map_left]

/-- Any adaptive original schedule executes with exactly the full encoded source distribution. Ownership is propagated from each actual supported reply, and never becomes an adversary restriction. -/
theorem program_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (identityIndex : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (owned : PqxdhRegistrationJointServerSchedule.Owned seed identityIndex state) :
    execute setup codec checks identityIndex (setup.joint.publicKeys seed) (simulateQ (PqxdhRegistrationJointRevealSchedule.client setup codec) program) (encodeState setup state) =
      (fun result => (result.1, encodeState setup result.2)) <$>
        (simulateQ (PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [execute, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, execute_bind,
        query_source setup codec checks seed identityIndex query state owned,
        bind_map_left, StateT.run_bind, map_bind]
      apply bind_congr_of_forall_mem_support
      exact fun result supported => ih result.1 result.2
        (PqxdhRegistrationJointServerSchedule.query_invariant setup codec checks seed identityIndex query state result owned supported)


end BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.pool_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.pool_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.finish_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.finish_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.create_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.bundle_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.finish_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.shared_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.shared_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.read_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.read_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.native_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.native_backend

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.query_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.execute_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.execute_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerClient.program_source
