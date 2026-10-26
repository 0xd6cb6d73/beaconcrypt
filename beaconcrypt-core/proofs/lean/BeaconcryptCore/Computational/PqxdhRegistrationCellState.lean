-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationScheduleResources

/-! Exact indexed live-cell representation of the actual registration registry. Numeric addresses remain publicly constructible, including missing and future values. The representation changes only owner storage; the complete shared Server and primitive state is retained. This is an operational interface relation, not a cryptographic term abstraction. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationCells
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhBeaconPhase2Preparation (Word32)
namespace Source
export PqxdhRegistrationSchedule (Owner State)
end Source
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- A live cell has its stable public index; its current value is replaced rather than appended to a historical table. `next` is the allocation counter, not an authentication capability. -/
structure State (KemSK : Type) where
  shared : NativeState KemSK
  next : Nat
  cell : Nat → Option (Source.Owner KemSK)

def encode (state : Source.State KemSK) : State KemSK :=
  ⟨state.shared, state.owners.length, fun index => state.owners[index]?⟩

def replace (state : State KemSK) (index : Nat) (owner : Source.Owner KemSK) : State KemSK :=
  { state with cell := fun selected => if selected = index then some owner else state.cell selected }

def allocate (state : State KemSK) (owner : Source.Owner KemSK) : State KemSK :=
  { replace state state.next owner with next := state.next + 1 }

/-- The exact representation rejects every not-yet-created numeric address without requiring an unguessable private name. -/
theorem future (state : Source.State KemSK) (index : Nat) (outside : state.owners.length ≤ index) :
    (encode state).cell index = none := by
  exact List.getElem?_eq_none outside

/-- Replacing the selected live source owner changes precisely that numeric cell and retains the complete shared state. -/
theorem encode_replace (state : Source.State KemSK) (index : Nat) (owner : Source.Owner KemSK)
    (present : index < state.owners.length) :
    encode { state with owners := state.owners.set index owner } = replace (encode state) index owner := by
  simp only [encode, replace, List.length_set]
  congr 1
  funext selected
  simp only [List.getElem?_set, present, ite_true, eq_comm]

/-- Allocation uses the old public length and appends exactly the new live owner. All other numeric lookups, including every still-future address, retain their prior values. -/
theorem encode_allocate (state : Source.State KemSK) (owner : Source.Owner KemSK) :
    encode { state with owners := state.owners ++ [owner] } = allocate (encode state) owner := by
  simp only [encode, allocate, replace, List.length_append, List.length_singleton]
  congr 1
  funext selected
  by_cases existing : selected < state.owners.length
  · simp only [List.getElem?_append_left existing, Nat.ne_of_lt existing, ite_false]
  · simp only [List.getElem?_append_right (Nat.le_of_not_gt existing), List.getElem?_singleton,
      List.getElem?_eq_none (Nat.le_of_not_gt existing)]
    have same : selected - state.owners.length = 0 ↔ selected = state.owners.length := by omega
    simp only [same]

abbrev Game (KemSK : Type) := StateT (State KemSK) ProbComp

/-- Shared services update the same complete shared state without changing any owner cell or the public allocation counter. -/
def onShared {Result : Type} (work : NativeGame KemSK Result) : Game KemSK Result := fun state =>
  (fun result => (result.1, { state with shared := result.2 })) <$> work state.shared

/-- The selected worker consumes its current live value, runs the original complete callback program, and reinstalls the exact returned owner even on ordinary failure. Missing cells reply before callbacks. -/
def atOwner {Result : Type} (index : Nat)
    (work : Source.Owner KemSK → NativeGame KemSK (Option Result × Source.Owner KemSK)) :
    Game KemSK (Option Result) := fun state =>
  match state.cell index with
  | none => pure (none, state)
  | some owner => (fun result => (result.1.1,
      replace { state with shared := result.2 } index result.1.2)) <$> work owner state.shared

noncomputable def finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (raw : Pqxdh.Bytes) : Game KemSK (Option Pqxdh.Bytes) :=
  atOwner index fun owner => simulateQ (PqxdhRegistrationSchedule.callbacks setup codec)
    (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)

def bundle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) : Game KemSK (Option Pqxdh.Bytes) :=
  atOwner index fun owner => StateT.lift (simulateQ
    (PqxdhRegistrationSchedule.bundleCallbacks setup codec owner.beacon.identity)
    (PqxdhLivePhase1Bundle.bundle (PqxdhRegistrationSchedule.projection setup index) owner))

/-- The same generators run at the same request position and in the same order; the only different operation is the proved live-cell allocation. -/
noncomputable def create (setup : Setup baseSpec KemSK) (pin : Word32) (keyId : Std.U64) :
    Game KemSK Nat := fun state => do
  let identity ← sampleSeed
  let prekey ← sampleScalar
  let keys ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let owner : Source.Owner KemSK := ⟨⟨identity, keyId, pin, .fresh ⟨⟨pin, keyId⟩⟩ prekey keys⟩, 0⟩
  pure (state.next, allocate state owner)

/-- Complete initial-message receive has the exact source reply and full-state distribution under the independent live-cell dispatcher. -/
theorem finish_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (raw : Pqxdh.Bytes) (state : Source.State KemSK) :
    (finish setup codec index raw).run (encode state) =
      (fun result => (result.1, encode result.2)) <$>
        (PqxdhRegistrationSchedule.finish setup codec index raw).run state := by
  cases found : state.owners[index]? with
  | none =>
      rw [PqxdhRegistrationSchedule.finish_missing setup codec index raw state found]
      simp only [finish, atOwner, encode, found, StateT.run, map_pure]
  | some owner =>
      change finish setup codec index raw (encode state) =
        (fun result => (result.1, encode result.2)) <$>
          PqxdhRegistrationSchedule.finish setup codec index raw state
      rw [PqxdhRegistrationSchedule.finish_source setup codec index raw state owner found]
      simp only [finish, atOwner, encode, found, Functor.map_map]
      congr 1
      exact funext fun result => Prod.ext rfl
        (encode_replace { state with shared := result.2 } index result.1.2
          (List.getElem?_eq_some_iff.mp found).1).symm

/-- The Phase-1 worker receives the same current owner, performs every original generator/signature/writer callback, and replaces that cell with the exact returned phase. -/
theorem bundle_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (state : Source.State KemSK) :
    (bundle setup codec index).run (encode state) =
      (fun result => (result.1, encode result.2)) <$>
        (PqxdhRegistrationSchedule.bundle setup codec index).run state := by
  cases found : state.owners[index]? with
  | none =>
      simp only [PqxdhRegistrationSchedule.bundle, StateT.run_bind, StateT.run_get, pure_bind,
        found, StateT.run_pure, map_pure]
      simp only [bundle, atOwner, encode, StateT.run, found]
  | some owner =>
      change bundle setup codec index (encode state) =
        (fun result => (result.1, encode result.2)) <$>
          PqxdhRegistrationSchedule.bundle setup codec index state
      rw [PqxdhRegistrationSchedule.bundle_source setup codec index state owner found]
      simp only [bundle, atOwner, encode, found, StateT.lift, bind_pure_comp, Functor.map_map]
      congr 1
      exact funext fun result => Prod.ext rfl
        (encode_replace state index result.2 (List.getElem?_eq_some_iff.mp found).1).symm

/-- Both interpreters execute identity, prekey and KEM generation in source order, then return the same old public allocation index with the complete encoded state. -/
theorem create_source (setup : Setup baseSpec KemSK) (pin : Word32) (keyId : Std.U64)
    (state : Source.State KemSK) :
    (create setup pin keyId).run (encode state) =
      (fun result => (result.1, encode result.2)) <$>
        (PqxdhRegistrationSchedule.create setup pin keyId).run state := by
  change create setup pin keyId (encode state) =
    (fun result => (result.1, encode result.2)) <$> PqxdhRegistrationSchedule.create setup pin keyId state
  rw [PqxdhRegistrationSchedule.create_source setup pin keyId state]
  simp only [create, map_bind, map_pure, encode_allocate]
  rfl

/-- Full shared operations, including failed accepts/builds and all their cache effects, commute with the live-owner representation. -/
theorem shared_source {Result : Type} (work : NativeGame KemSK Result) (state : Source.State KemSK) :
    (onShared work).run (encode state) = (fun result => (result.1, encode result.2)) <$>
      (PqxdhRegistrationSchedule.onShared work).run state := by
  simp only [onShared, PqxdhRegistrationSchedule.onShared, StateT.run, Functor.map_map, encode]

/-- The independent cell interpreter exposes exactly the original public requests. Server and pending-token operations execute their original native programs. Owner addresses are looked up in live cells; no private name is an admission capability. -/
noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) : QueryImpl PqxdhRegistrationSchedule.Spec (Game KemSK)
  | .inl coin => StateT.lift (unifSpec.query coin : ProbComp _)
  | .inr (.create pin keyId) => create setup pin keyId
  | .inr (.bundle index) => bundle setup codec index
  | .inr (.accept raw) => onShared (nativeAccept setup codec checks serverSeed PqxdhRegistrationSchedule.observationScalar raw)
  | .inr (.build index payload) => onShared (nativeBuild setup codec checks index payload)
  | .inr (.finish index raw) => finish setup codec index raw
  | .inr (.hmac key message) => onShared (nativeHmac setup serverSeed PqxdhRegistrationSchedule.observationScalar key message)
  | .inr (.hash bytes) => onShared (nativeHash bytes)
  | .inr (.reveal keyId) => onShared (localState fun state => (revealKernel keyId state, state))

/-- Every complete one-operation transition preserves the actual optional reply and full encoded source state, with all callback and sampling effects in the same computation. -/
theorem handler_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (query : PqxdhRegistrationSchedule.Spec.Domain)
    (state : Source.State KemSK) :
    (handler setup codec checks serverSeed query).run (encode state) =
      (fun result => (result.1, encode result.2)) <$>
        (PqxdhRegistrationSchedule.handler setup codec checks serverSeed query).run state := by
  cases query with
  | inl coin =>
      simp only [handler, PqxdhRegistrationSchedule.handler, StateT.run_lift, bind_pure_comp,
        Functor.map_map]
  | inr request =>
      cases request with
      | create pin keyId => exact create_source setup pin keyId state
      | bundle index => exact bundle_source setup codec index state
      | finish index raw => exact finish_source setup codec index raw state
      | _ => exact shared_source _ state

/-- Arbitrary adaptive source clients receive exactly their original replies under the live-cell interface. The equality retains the complete final shared/private state and every original uniform query, including rejected requests. -/
theorem program_source {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed)
    (work : OracleComp PqxdhRegistrationSchedule.Spec Result) (state : Source.State KemSK) :
    (simulateQ (handler setup codec checks serverSeed) work).run (encode state) =
      (fun result => (result.1, encode result.2)) <$>
        (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks serverSeed) work).run state := by
  exact (map_run_simulateQ_eq_of_query_map_eq
    (PqxdhRegistrationSchedule.handler setup codec checks serverSeed)
    (handler setup codec checks serverSeed) encode
    (fun query before => (handler_source setup codec checks serverSeed query before).symm)
    work state).symm

/-- The cell encoding discards no source state: equal encodings have the same complete shared state and every original owner, including all private fields and instrumentation. -/
theorem encode_injective : Function.Injective (encode (KemSK := KemSK)) := by
  intro first second same
  exact congrArg₂ PqxdhRegistrationSchedule.State.mk (congrArg State.shared same)
    (List.ext_getElem? fun index => congrArg (fun state => state.cell index) same)

end BeaconcryptCore.Computational.PqxdhRegistrationCells

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationCells.future' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationCells.future
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationCells.encode_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationCells.encode_replace
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationCells.encode_allocate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationCells.encode_allocate
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationCells.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationCells.finish_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationCells.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationCells.bundle_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationCells.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationCells.create_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationCells.shared_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationCells.shared_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationCells.handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationCells.handler_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationCells.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationCells.program_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationCells.encode_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationCells.encode_injective
