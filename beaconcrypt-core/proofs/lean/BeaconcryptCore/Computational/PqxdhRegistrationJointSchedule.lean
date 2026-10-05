-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointOwnership

/-! One annotated dynamic registration scheduler retains complete native owners, separate creation handles, both private service histories and the original shared primitive state. Only the original public schedule requests are available; the retained histories introduce no extra reveal operation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointPreparation (Pool)
open PqxdhRegistrationJointOwnership (Entry Owned)
open PqxdhBeaconPhase2Preparation (Word32)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

structure State (KemSK : Type) where
  pool : Pool KemSK
  shared : NativeState KemSK
  owners : List (Entry KemSK)

/-- Forget only service indices and private service analysis histories; every source owner and shared cache is retained. -/
def source (state : State KemSK) : PqxdhRegistrationSchedule.State KemSK :=
  ⟨state.shared, state.owners.map Entry.owner⟩

def Invariant (state : State KemSK) : Prop := ∀ entry ∈ state.owners, Owned state.pool entry

/-- The initialized schedule has no Beacon owners. Prior service histories may be arbitrary and remain private. -/
def initial (pool : Pool KemSK) (shared : NativeState KemSK) : State KemSK := ⟨pool, shared, []⟩

def birth (pin : Word32) (keyId : Std.U64) (pool : Pool KemSK)
    (material : PqxdhRegistrationJointCreation.Material KemSK) : Entry KemSK :=
  ⟨pool.1.seeds.length, pool.2.keys.length,
    ⟨⟨material.seed, keyId, pin, .fresh ⟨⟨pin, keyId⟩⟩ material.prekey material.keys⟩, 0⟩⟩

def created (setup : Setup baseSpec KemSK) (pin : Word32) (keyId : Std.U64)
    (state : State KemSK) (material : PqxdhRegistrationJointCreation.Material KemSK) : Nat × State KemSK :=
  (state.owners.length, { state with
    pool := (PqxdhRegistrationJointCreation.serviceView setup state.pool material).2,
    owners := state.owners ++ [birth pin keyId state.pool material] })

def create (setup : Setup baseSpec KemSK) (pin : Word32) (keyId : Std.U64) : StateT (State KemSK) ProbComp Nat :=
  fun state => created setup pin keyId state <$> PqxdhRegistrationJointCreation.material setup

/-- Every optional write retains all three signing replies in the exact trace before reinstalling the complete native owner. -/
def bundle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (address : Nat) : StateT (State KemSK) ProbComp (Option Pqxdh.Bytes) := fun state =>
  match state.owners[address]? with
  | none => pure (none, state)
  | some entry =>
      (fun result => (result.1.1, { state with
        pool := (result.2, state.pool.2),
        owners := state.owners.set address { entry with owner := result.1.2 } })) <$>
          PqxdhRegistrationJointBundle.trace setup codec entry.identityIndex entry.owner state.pool.1

/-- Present entries run the existing annotated complete owner once, preserving failure effects and replacing only the selected live owner. -/
noncomputable def finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (address : Nat) (raw : Pqxdh.Bytes) : StateT (State KemSK) ProbComp (Option Pqxdh.Bytes) := fun state =>
  match state.owners[address]? with
  | none => pure (none, state)
  | some entry =>
      (fun result => (result.1.1, { state with
        pool := result.2.1, shared := result.2.2,
        owners := state.owners.set address { entry with owner := result.1.2 } })) <$>
          (simulateQ (PqxdhRegistrationJointFinish.annotated setup codec entry.identityIndex entry.kemIndex)
            (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw entry.owner)).run (state.pool, state.shared)

/-- Server and public operations use the original shared state, retaining every annotated owner and both private pools. -/
def onShared (work : NativeGame KemSK Result) : StateT (State KemSK) ProbComp Result := fun state =>
  (fun result => (result.1, { state with shared := result.2 })) <$> work.run state.shared

noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) :
    QueryImpl PqxdhRegistrationSchedule.Spec (StateT (State KemSK) ProbComp)
  | .inl coin => StateT.lift (unifSpec.query coin : ProbComp _)
  | .inr (.create pin keyId) => create setup pin keyId
  | .inr (.bundle address) => bundle setup codec address
  | .inr (.accept raw) => onShared (nativeAccept setup codec checks serverSeed PqxdhRegistrationSchedule.observationScalar raw)
  | .inr (.build index payload) => onShared (nativeBuild setup codec checks index payload)
  | .inr (.finish address raw) => finish setup codec address raw
  | .inr (.hmac key message) => onShared (nativeHmac setup serverSeed PqxdhRegistrationSchedule.observationScalar key message)
  | .inr (.hash bytes) => onShared (nativeHash bytes)
  | .inr (.reveal keyId) => onShared (localState fun state => (revealKernel keyId state, state))

/-- Empty-owner initialization supplies the ownership invariant without any key or origin assumption. -/
theorem initial_owned (pool : Pool KemSK) (shared : NativeState KemSK) : Invariant (initial pool shared) := by
  simp [Invariant, initial]

/-- The complete constructor distribution projects to the original scheduler, with the source generator order and every earlier owner/cache retained. -/
theorem create_source (setup : Setup baseSpec KemSK) (pin : Word32) (keyId : Std.U64) (state : State KemSK) :
    (fun result => (result.1, source result.2)) <$> (create setup pin keyId).run state =
      (PqxdhRegistrationSchedule.create setup pin keyId).run (source state) := by
  rw [PqxdhRegistrationJointCreation.native_source]
  simp only [create, StateT.run, Functor.map_map]
  congr 1; funext value
  simp [created, source, birth, PqxdhRegistrationJointCreation.install]

/-- The actual optional bundle reply and all reinstalled source owners have the unchanged native distribution, including every writer failure and retry. -/
theorem bundle_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (address : Nat) (state : State KemSK) :
    (fun result => (result.1, source result.2)) <$> (bundle setup codec address).run state =
      (PqxdhRegistrationSchedule.bundle setup codec address).run (source state) := by
  cases found : state.owners[address]? with
  | none =>
      simp only [PqxdhRegistrationSchedule.bundle, StateT.run_bind, StateT.run_get, pure_bind, source, List.getElem?_map, found, Option.map_none, StateT.run_pure]
      simp [bundle, StateT.run, found]
  | some entry =>
      have selected : (source state).owners[address]? = some entry.owner := by simp [source, found]
      rw [PqxdhRegistrationJointBundle.native_source setup codec address entry.identityIndex (source state) entry.owner state.pool.1 selected]
      simp [bundle, StateT.run, found, source, Functor.map_map]

/-- Native finish projection retains the exact optional result, all source owners and the full shared poststate of the same annotated execution. -/
theorem finish_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (address : Nat) (raw : Pqxdh.Bytes) (state : State KemSK) :
    (fun result => (result.1, source result.2)) <$> (finish setup codec address raw).run state =
      (PqxdhRegistrationSchedule.finish setup codec address raw).run (source state) := by
  cases found : state.owners[address]? with
  | none =>
      rw [PqxdhRegistrationSchedule.finish_missing setup codec address raw (source state) (by simp [source, found])]
      simp [finish, StateT.run, found]
  | some entry =>
      rw [PqxdhRegistrationJointFinish.finish_source setup codec address entry.identityIndex entry.kemIndex raw (source state) state.pool entry.owner (by simp [source, found])]
      simp [finish, StateT.run, found, source, Functor.map_map]

/-- The unchanged native Server/public operation retains its whole source poststate after forgetting the private ownership annotation. -/
theorem shared_source (work : NativeGame KemSK Result) (state : State KemSK) :
    (fun result => (result.1, source result.2)) <$> (onShared work).run state =
      (PqxdhRegistrationSchedule.onShared work).run (source state) := by
  simp only [onShared, PqxdhRegistrationSchedule.onShared, StateT.run, Functor.map_map, source]

/-- Each original request preserves its exact reply and full native state distribution; no request is filtered by a private ownership premise. -/
theorem query_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (query : PqxdhRegistrationSchedule.Spec.Domain)
    (state : State KemSK) :
    (fun result => (result.1, source result.2)) <$> (handler setup codec checks serverSeed query).run state =
      (PqxdhRegistrationSchedule.handler setup codec checks serverSeed query).run (source state) := by
  rcases query with coin | request
  case inr =>
    cases request <;> first
    | exact create_source setup _ _ state
    | exact bundle_source setup codec _ state
    | exact finish_source setup codec _ _ state
    | exact shared_source _ state
  case inl => simp only [handler, PqxdhRegistrationSchedule.handler, StateT.run_lift, bind_pure_comp, Functor.map_map]

/-- Every adaptive original schedule has exactly its native full-state distribution after annotation erasure, including arbitrary caller results and all optional callback replies. -/
theorem program_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed)
    (program : OracleComp PqxdhRegistrationSchedule.Spec Result) (state : State KemSK) :
    (fun result => (result.1, source result.2)) <$>
      (simulateQ (handler setup codec checks serverSeed) program).run state =
        (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks serverSeed) program).run (source state) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, ih]
      simpa only [bind_map_left] using congrArg
        (fun work => work >>= fun result =>
          (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks serverSeed) (next result.1)).run result.2)
        (query_source setup codec checks serverSeed query state)

end BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.initial_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.initial_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.create_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.bundle_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.finish_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.shared_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.shared_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.query_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.program_source
