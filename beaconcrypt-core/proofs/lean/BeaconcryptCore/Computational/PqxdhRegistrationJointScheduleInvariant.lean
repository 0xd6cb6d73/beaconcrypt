-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule

/-! Generated ownership is preserved by the complete dynamic source scheduler. A current owner carries only its source fields; the private service histories do not create an adversarial restore or reveal capability. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointPreparation (Pool)
open PqxdhRegistrationJointOwnership (Entry Owned activeKey)
open PqxdhBeaconPhase2Preparation (Word32)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

private theorem lookup_append {A : Type} (before extra : List A) (index : Nat) (value : A)
    (found : before[index]? = some value) : (before ++ extra)[index]? = some value := by
  simpa only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).choose] using found

/-- Creating a new private pair preserves the exact ownership of every previously live owner, regardless of equal public encodings. -/
theorem prior_owned (setup : Setup baseSpec KemSK) (pool : Pool KemSK)
    (material : PqxdhRegistrationJointCreation.Material KemSK) (entry : Entry KemSK)
    (owned : Owned pool entry) :
    Owned (PqxdhRegistrationJointCreation.serviceView setup pool material).2 entry := by
  constructor
  case right =>
    exact fun keys live => lookup_append pool.2.keys [material.keys] entry.kemIndex keys (owned.2 keys live)
  case left => exact lookup_append pool.1.seeds [material.seed] entry.identityIndex entry.owner.beacon.identity owned.1

/-- The actual generated constructor draws install the new owner's exact seed and KEM pair at their separate newly allocated slots. -/
theorem birth_owned (setup : Setup baseSpec KemSK) (pin : Word32) (keyId : Std.U64)
    (pool : Pool KemSK) (material : PqxdhRegistrationJointCreation.Material KemSK) :
    Owned (PqxdhRegistrationJointCreation.serviceView setup pool material).2 (birth pin keyId pool material) := by
  simpa [Owned, birth, activeKey] using PqxdhRegistrationJointCreation.service_owns setup pool material

/-- Creation preserves ownership for every earlier owner and the actual new owner simultaneously. -/
theorem created_owned (setup : Setup baseSpec KemSK) (pin : Word32) (keyId : Std.U64)
    (state : State KemSK) (material : PqxdhRegistrationJointCreation.Material KemSK)
    (owned : Invariant state) : Invariant (created setup pin keyId state material).2 := by
  intro entry member
  rcases List.mem_append.mp member with previous | born
  · exact prior_owned setup state.pool material entry (owned entry previous)
  · exact (List.mem_singleton.mp born) ▸ birth_owned setup pin keyId state.pool material

/-- Every supported whole bundle trace retains all private seed slots and ownership of the actual returned owner, including unsuccessful serialization. -/
theorem bundle_trace_owned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (entry : Entry KemSK) (pool : Pool KemSK)
    (result : (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × PqxdhDynamicIdentityPool.SourceState)
    (owned : Owned pool entry)
    (supported : result ∈ support (PqxdhRegistrationJointBundle.trace setup codec entry.identityIndex entry.owner pool.1)) :
    result.2.seeds = pool.1.seeds ∧ Owned (result.2, pool.2) { entry with owner := result.1.2 } := by
  cases phase : entry.owner.beacon.phase <;>
    simp only [PqxdhRegistrationJointBundle.trace, phase, support_map, Set.mem_image, mem_support_pure_iff] at supported
  case fresh =>
    obtain ⟨scalar, _, rfl⟩ := supported
    exact ⟨PqxdhRegistrationJointBundle.after_seeds setup codec entry.identityIndex entry.owner (some scalar) pool.1,
      PqxdhRegistrationJointOwnership.bundle_owned setup codec entry (some scalar) pool owned⟩
  all_goals subst result
  all_goals first
  | exact ⟨rfl, owned⟩
  | exact ⟨PqxdhRegistrationJointBundle.after_seeds setup codec entry.identityIndex entry.owner none pool.1,
      PqxdhRegistrationJointOwnership.bundle_owned setup codec entry none pool owned⟩

/-- Reinstalling one actual returned owner preserves all other ownership facts when callbacks changed only the histories and shared native state. -/
theorem updated_owned (state : State KemSK) (pool : Pool KemSK) (shared : NativeState KemSK)
    (address : Nat) (entry : Entry KemSK)
    (owned : Invariant state) (seeds : pool.1.seeds = state.pool.1.seeds) (keys : pool.2.keys = state.pool.2.keys)
    (replacement : Owned pool entry) : Invariant ⟨pool, shared, state.owners.set address entry⟩ := by
  intro current member
  exact (List.mem_or_eq_of_mem_set member).elim
    (fun previous => PqxdhRegistrationJointOwnership.owned_slots state.pool pool current seeds keys (owned current previous))
    (fun equal => equal ▸ replacement)

/-- Every source bundle attempt preserves ownership of the selected returned owner and all unselected owners. Missing addresses and failed writers remain ordinary outcomes. -/
theorem bundle_owned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (address : Nat) (state : State KemSK) (result : Option Pqxdh.Bytes × State KemSK)
    (owned : Invariant state) (supported : result ∈ support ((bundle setup codec address).run state)) :
    Invariant result.2 := by
  cases found : state.owners[address]? <;>
    simp only [bundle, StateT.run, found, support_map, Set.mem_image, mem_support_pure_iff] at supported
  case some entry =>
    obtain ⟨reached, member, rfl⟩ := supported
    have preserved := bundle_trace_owned setup codec entry state.pool reached (owned entry (List.mem_of_getElem? found)) member
    exact updated_owned state (reached.2, state.pool.2) state.shared address
      { entry with owner := reached.1.2 } owned preserved.1 rfl preserved.2
  case none => simpa only [supported] using owned

/-- Every source finish attempt preserves ownership across all owners and keeps both private slot arrays intact, even when preparation or publication rejects. -/
theorem finish_owned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (address : Nat) (raw : Pqxdh.Bytes) (state : State KemSK) (result : Option Pqxdh.Bytes × State KemSK)
    (owned : Invariant state) (supported : result ∈ support ((finish setup codec address raw).run state)) :
    Invariant result.2 := by
  cases found : state.owners[address]? <;>
    simp only [finish, StateT.run, found, support_map, Set.mem_image, mem_support_pure_iff] at supported
  case some entry =>
    obtain ⟨reached, member, rfl⟩ := supported
    have slots := PqxdhRegistrationJointFinish.annotated_program_slots setup codec entry.identityIndex entry.kemIndex
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw entry.owner) (state.pool, state.shared) reached member
    exact updated_owned state reached.2.1 reached.2.2 address { entry with owner := reached.1.2 } owned slots.1 slots.2
      (PqxdhRegistrationJointOwnership.owner_owned setup codec entry raw (state.pool, state.shared) reached
        (owned entry (List.mem_of_getElem? found)) member)
  case none => simpa only [supported] using owned

/-- Native Server and public primitive requests change no Beacon ownership field or private service slot. -/
theorem shared_owned (work : NativeGame KemSK Result) (state : State KemSK) (result : Result × State KemSK)
    (owned : Invariant state) (supported : result ∈ support ((onShared work).run state)) : Invariant result.2 := by
  obtain ⟨reached, _, rfl⟩ : ∃ reached ∈ support (work.run state.shared),
      (reached.1, { state with shared := reached.2 }) = result := by
    simpa only [onShared, StateT.run, support_map, Set.mem_image] using supported
  exact owned

/-- Every original adaptive scheduler request preserves generated ownership. No request is rejected or restricted because of this private invariant. -/
theorem query_owned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (query : PqxdhRegistrationSchedule.Spec.Domain)
    (state : State KemSK) (result : PqxdhRegistrationSchedule.Spec.Range query × State KemSK)
    (owned : Invariant state) (supported : result ∈ support ((handler setup codec checks serverSeed query).run state)) :
    Invariant result.2 := by
  rcases query with coin | request
  case inr =>
    cases request <;> first
    | exact bundle_owned setup codec _ state result owned supported
    | exact finish_owned setup codec _ _ state result owned supported
    | exact shared_owned _ state result owned supported
    | skip
    case create pin keyId =>
      simp only [handler, create, StateT.run, support_map, Set.mem_image] at supported
      exact supported.elim (fun value witness => witness.2 ▸ created_owned setup pin keyId state value owned)
  case inl =>
    simp only [handler, StateT.run_lift, bind_pure_comp, support_map, Set.mem_image] at supported
    exact supported.elim (fun _ witness => witness.2 ▸ owned)

/-- Generated ownership survives every finite adaptive original schedule, including any number of dynamic creations, failed writers, retries and raw finish attempts. -/
theorem program_owned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (program : OracleComp PqxdhRegistrationSchedule.Spec Result)
    (state : State KemSK) (result : Result × State KemSK) (owned : Invariant state)
    (supported : result ∈ support ((simulateQ (handler setup codec checks serverSeed) program).run state)) :
    Invariant result.2 := by
  exact (run_rel (handler setup codec checks serverSeed) (fun before after => Invariant before → Invariant after)
    (fun _ owned => owned) (fun _ _ _ left right owned => right (left owned))
    (fun query before after member owned => query_owned setup codec checks serverSeed query before after owned member)
    program state result supported) owned

/-- Starting with no Beacon owners discharges ownership from actual creation and every intervening source request, rather than assuming it for a selected target. -/
theorem generated_owned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (program : OracleComp PqxdhRegistrationSchedule.Spec Result)
    (pool : Pool KemSK) (shared : NativeState KemSK) (result : Result × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks serverSeed) program).run (initial pool shared))) :
    Invariant result.2 :=
  program_owned setup codec checks serverSeed program (initial pool shared) result (initial_owned pool shared) supported

/-- The actual reached public owner slot has the exact private seed and InitSent KEM pair required by the existing compiled finish. The caller need not assert either slot premise. -/
theorem generated_slots (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (program : OracleComp PqxdhRegistrationSchedule.Spec Result)
    (pool : Pool KemSK) (shared : NativeState KemSK) (result : Result × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks serverSeed) program).run (initial pool shared)))
    (address : Nat) (entry : Entry KemSK) (found : result.2.owners[address]? = some entry) :
    result.2.pool.1.seeds[entry.identityIndex]? = some entry.owner.beacon.identity ∧
      ∀ control prekey oneTime keys, entry.owner.beacon.phase = .initSent control prekey oneTime keys →
        result.2.pool.2.keys[entry.kemIndex]? = some keys := by
  have owned := generated_owned setup codec checks serverSeed program pool shared result supported entry (List.mem_of_getElem? found)
  exact ⟨owned.1, fun _ _ _ keys active => owned.2 keys (by simp only [activeKey, active])⟩

end BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.prior_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.prior_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.birth_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.birth_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.created_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.created_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.bundle_trace_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.bundle_trace_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.updated_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.updated_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.bundle_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.bundle_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.finish_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.finish_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.shared_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.shared_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.query_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.query_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.program_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.program_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.generated_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.generated_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.generated_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSchedule.generated_slots
