-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointBundleCompiler

/-! An executable one-Server/many-Beacon registration schedule uses indexed identity and KEM services for the actual constructor, bundle and finish. Original Server/public operations remain explicit native requests on the same complete shared state; their source work is not a new primitive or an uncharged ambient service. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry EncodedState encodeEntry encodeState)
open PqxdhRegistrationJointFinish (onPool onNative)
open PqxdhBeaconPhase2Preparation (Word32)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- The unchanged native Server/public operations are explicit backend requests, distinct from identity/KEM primitive calls. -/
inductive SharedRequest where
  | accept (raw : Pqxdh.Bytes)
  | build (session : Nat) (payload : Option Pqxdh.Bytes)
  | hmac (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes)
  | hash (bytes : Pqxdh.Bytes)
  | reveal (keyId : Std.U64)

abbrev SharedSpec : OracleSpec SharedRequest
  | .accept _ => Option Nat
  | .build _ _ => Option PqxdhServerRegistrationPublication.Response
  | .hmac _ _ => PqxdhSecretInputKdf.HmacBlock
  | .hash _ => CtxRomAuth.CtxDigest
  | .reveal _ => Option beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel

abbrev Spec (KemSK Response : Type) := PqxdhRegistrationJointFinishCompiler.Spec KemSK Response + SharedSpec
abbrev Client (KemSK Response Result : Type) := StateT (List EncodedEntry) (OracleComp (Spec KemSK Response)) Result

noncomputable def shared (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) : QueryImpl SharedSpec (NativeGame KemSK)
  | .accept raw => nativeAccept setup codec checks serverSeed PqxdhRegistrationSchedule.observationScalar raw
  | .build index payload => nativeBuild setup codec checks index payload
  | .hmac key message => nativeHmac setup serverSeed PqxdhRegistrationSchedule.observationScalar key message
  | .hash bytes => nativeHash bytes
  | .reveal keyId => localState fun state => (revealKernel keyId state, state)

noncomputable def impl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) :
    QueryImpl (Spec KemSK Response) (StateT (PqxdhRegistrationJointFinish.State KemSK) ProbComp)
  | .inl query => PqxdhRegistrationJointFinishCompiler.impl setup codec query
  | .inr query => onNative (shared setup codec checks serverSeed query)

def poolLift : QueryImpl (PqxdhLiveKemBirth.Spec KemSK) (OracleComp (Spec KemSK Response)) :=
  fun query => (Spec KemSK Response).query (.inl (.inl query))

def finishLift : QueryImpl (PqxdhRegistrationJointFinishCompiler.Spec KemSK Response) (OracleComp (Spec KemSK Response)) :=
  fun query => (Spec KemSK Response).query (.inl query)

/-- Only handles, public identity/KEM bytes and the actual private prekey enter the new client owner. -/
def birth (pin : Word32) (keyId : Std.U64) (value : PqxdhRegistrationJointCreation.Birth) : EncodedEntry :=
  (value.identityIndex, value.kemIndex,
    ⟨⟨(value.identityIndex, value.identity.ed25519), keyId, pin,
      .fresh ⟨⟨pin, keyId⟩⟩ value.prekey (value.kemPublic, value.kemIndex)⟩, 0⟩)

/-- The actual indexed constructor never returns None under its source interpreter. The syntactic None branch remains total and makes no owner installation. -/
def create (pin : Word32) (keyId : Std.U64) : Client KemSK Response Nat := fun owners => do
  let value ← simulateQ poolLift (PqxdhRegistrationJointCreation.client (KemSK := KemSK))
  pure (owners.length, match value with
    | none => owners
    | some value => owners ++ [birth pin keyId value])

/-- Every bundle uses the selected live owner and reinstalls its complete optional publication result, retaining its original service indices. -/
def bundle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address : Nat) :
    Client KemSK Response (Option Pqxdh.Bytes) := fun owners =>
  match owners[address]? with
  | none => pure (none, owners)
  | some entry =>
    (fun result => (result.1, owners.set address (entry.1, entry.2.1, result.2))) <$>
      simulateQ poolLift (simulateQ (PqxdhRegistrationJointBundleCompiler.compiler codec)
        (PqxdhLivePhase1Bundle.bundle (PqxdhRegistrationJointBundle.projection setup) entry.2.2))

/-- The original complete finish client returns its actual optional plaintext and complete reinstalled owner through the same private-service backend. -/
noncomputable def finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (address : Nat) (raw : Pqxdh.Bytes) : Client KemSK Response (Option Pqxdh.Bytes) := fun owners =>
  match owners[address]? with
  | none => pure (none, owners)
  | some entry =>
    (fun result => (result.1, owners.set address (entry.1, entry.2.1, result.2))) <$>
      simulateQ finishLift (simulateQ (PqxdhRegistrationJointFinishCompiler.compiler setup codec)
        (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw entry.2.2))

/-- The client has exactly the original public scheduling interface. Private service histories and creation handles are not returned to the caller. -/
noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl PqxdhRegistrationSchedule.Spec (Client KemSK Response)
  | .inl coin => StateT.lift ((Spec KemSK Response).query (.inl (.inl (.inr (.inl coin)))))
  | .inr (.create pin keyId) => create pin keyId
  | .inr (.bundle address) => bundle setup codec address
  | .inr (.accept raw) => StateT.lift ((Spec KemSK Response).query (.inr (.accept raw)))
  | .inr (.build index payload) => StateT.lift ((Spec KemSK Response).query (.inr (.build index payload)))
  | .inr (.finish address raw) => finish setup codec address raw
  | .inr (.hmac key message) => StateT.lift ((Spec KemSK Response).query (.inr (.hmac key message)))
  | .inr (.hash bytes) => StateT.lift ((Spec KemSK Response).query (.inr (.hash bytes)))
  | .inr (.reveal keyId) => StateT.lift ((Spec KemSK Response).query (.inr (.reveal keyId)))

/-- Reassociate the complete client/private-pool/shared state without erasing any field. -/
noncomputable def execute (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (client : Client KemSK Response Result)
    (state : EncodedState KemSK) : ProbComp (Result × EncodedState KemSK) :=
  (fun result => (result.1.1, ⟨result.2.1, result.2.2, result.1.2⟩)) <$>
    (simulateQ (impl setup codec checks serverSeed) (client.run state.owners)).run (state.pool, state.shared)

/-- A whole private-service client retains the complete shared native state while updating both private pools and their histories. -/
theorem pool_program (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (program : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result)
    (state : PqxdhRegistrationJointFinish.State KemSK) :
    (simulateQ (impl setup codec checks serverSeed) (simulateQ poolLift program)).run state =
      (fun result => (result.1, (result.2, state.2))) <$>
        (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem) program).run state.1 := by
  rw [← QueryImpl.simulateQ_compose]
  have routed : impl setup codec checks serverSeed ∘ₛ poolLift =
      fun query => onPool (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem query) := by
    funext query
    exact simulateQ_spec_query (impl setup codec checks serverSeed) (.inl (.inl query))
  rw [routed, PqxdhRegistrationJointFinish.pool_program]

/-- Routing the existing complete finish program preserves every native tail and private service reply and the entire product state. -/
theorem finish_program (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed)
    (program : OracleComp (PqxdhRegistrationJointFinishCompiler.Spec KemSK Response) Result) :
    simulateQ (impl setup codec checks serverSeed) (simulateQ finishLift program) =
      simulateQ (PqxdhRegistrationJointFinishCompiler.impl setup codec) program := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1; funext query
  exact simulateQ_spec_query (impl setup codec checks serverSeed) (.inl query)

/-- The actual source constructor and executable handle constructor have the same full encoded distribution, with identity, prekey and KEM generators in source order. -/
theorem create_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (pin : Word32) (keyId : Std.U64)
    (state : PqxdhRegistrationJointSchedule.State KemSK) :
    execute setup codec checks serverSeed (create pin keyId) (encodeState setup state) =
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
    (checks : Checks) (serverSeed : IdentitySeed) (address : Nat)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (owned : PqxdhRegistrationJointSchedule.Invariant state) :
    execute setup codec checks serverSeed (bundle setup codec address) (encodeState setup state) =
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
    (checks : Checks) (serverSeed : IdentitySeed) (address : Nat) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (owned : PqxdhRegistrationJointSchedule.Invariant state) :
    execute setup codec checks serverSeed (finish setup codec address raw) (encodeState setup state) =
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

/-- Existing Server/public operations retain their actual complete native effects and all private service and client state. -/
theorem shared_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (query : SharedSpec.Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK) :
    execute setup codec checks serverSeed (StateT.lift ((Spec KemSK Response).query (.inr query)))
      (encodeState setup state) =
      (fun result => (result.1, encodeState setup result.2)) <$>
        (PqxdhRegistrationJointSchedule.onShared (shared setup codec checks serverSeed query)).run state := by
  simp [execute, StateT.run_lift, bind_pure_comp, simulateQ_map, StateT.run_map, impl,
    encodeState, Functor.map_map]
  simp [StateT.run, onNative, PqxdhRegistrationJointSchedule.onShared, Functor.map_map]

/-- Each original public request has the exact encoded source reply and complete poststate; the private ownership invariant only justifies representation and never filters requests. -/
theorem query_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (query : PqxdhRegistrationSchedule.Spec.Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (owned : PqxdhRegistrationJointSchedule.Invariant state) :
    execute setup codec checks serverSeed (handler setup codec query) (encodeState setup state) =
      (fun result => (result.1, encodeState setup result.2)) <$>
        (PqxdhRegistrationJointSchedule.handler setup codec checks serverSeed query).run state := by
  rcases query with coin | request
  case inl =>
    simp [handler, execute, StateT.run_lift, bind_pure_comp, simulateQ_map, StateT.run_map, impl,
      PqxdhRegistrationJointFinishCompiler.impl, PqxdhRegistrationJointSchedule.handler, Functor.map_map]
    simp only [StateT.run, onPool, PqxdhLiveKemBirth.impl, encodeState, Functor.map_map]
    rfl
  case inr =>
    cases request <;> first
    | exact create_source setup codec checks serverSeed _ _ state
    | exact bundle_source setup codec checks serverSeed _ state owned
    | exact finish_source setup codec checks serverSeed _ _ state owned
    | exact shared_source setup codec checks serverSeed _ state

/-- Reassociating the client and backend state preserves the complete continuation, including every intermediate owner list and private/native poststate. -/
theorem execute_bind {Next : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (work : Client KemSK Response Result)
    (next : Result → Client KemSK Response Next) (state : EncodedState KemSK) :
    execute setup codec checks serverSeed (work >>= next) state =
      (execute setup codec checks serverSeed work state >>= fun result =>
        execute setup codec checks serverSeed (next result.1) result.2) := by
  simp only [execute, StateT.run_bind, simulateQ_bind, StateT.run_bind, map_bind, bind_map_left]

/-- Any adaptive original schedule executes with exactly the full encoded source distribution. Ownership is propagated from each actual supported reply, and never becomes an adversary restriction. -/
theorem program_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed)
    (program : OracleComp PqxdhRegistrationSchedule.Spec Result)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (owned : PqxdhRegistrationJointSchedule.Invariant state) :
    execute setup codec checks serverSeed (simulateQ (handler setup codec) program) (encodeState setup state) =
      (fun result => (result.1, encodeState setup result.2)) <$>
        (simulateQ (PqxdhRegistrationJointSchedule.handler setup codec checks serverSeed) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [execute, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, execute_bind,
        query_source setup codec checks serverSeed query state owned,
        bind_map_left, StateT.run_bind, map_bind]
      apply bind_congr_of_forall_mem_support
      exact fun result supported => ih result.1 result.2
        (PqxdhRegistrationJointSchedule.query_owned setup codec checks serverSeed query state result owned supported)

/-- From the actual empty owner registry, creation and all subsequent requests discharge every slot premise internally. The caller supplies no honest-target or ownership assertion. -/
theorem generated_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed)
    (program : OracleComp PqxdhRegistrationSchedule.Spec Result)
    (pool : PqxdhRegistrationJointPreparation.Pool KemSK) (native : NativeState KemSK) :
    execute setup codec checks serverSeed (simulateQ (handler setup codec) program) ⟨pool, native, []⟩ =
      (fun result => (result.1, encodeState setup result.2)) <$>
        (simulateQ (PqxdhRegistrationJointSchedule.handler setup codec checks serverSeed) program).run
          (PqxdhRegistrationJointSchedule.initial pool native) := by
  exact program_source setup codec checks serverSeed program (PqxdhRegistrationJointSchedule.initial pool native)
    (PqxdhRegistrationJointSchedule.initial_owned pool native)

/-- The entire compiled adaptive execution retains every source uniform-query allowance, including native Server, tail, public cryptographic and interpreted KEM/base work. -/
theorem program_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (program : OracleComp PqxdhRegistrationSchedule.Spec Result) (budget : Fin 9 → Nat)
    (certified : ∀ kind, program.IsQueryBoundP (fun query => PqxdhRegistrationSchedule.sourceKind query = kind) (budget kind))
    (state : PqxdhRegistrationJointSchedule.State KemSK) (owned : PqxdhRegistrationJointSchedule.Invariant state) :
    (execute setup codec checks serverSeed (simulateQ (handler setup codec) program) (encodeState setup state)).IsTotalQueryBound
      (∑ kind, PqxdhRegistrationSchedule.uniformCost caps 0 kind * budget kind) := by
  rw [program_source setup codec checks serverSeed program state owned, IsTotalQueryBound, isQueryBound_map_iff]
  exact PqxdhRegistrationJointGeneratedFinish.schedule_uniform setup codec checks caps bounded serverSeed program budget certified state

end BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.pool_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.pool_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.finish_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.finish_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.create_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.bundle_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.finish_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.shared_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.shared_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.query_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.execute_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.execute_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.program_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.generated_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.generated_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.program_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule.program_uniform
