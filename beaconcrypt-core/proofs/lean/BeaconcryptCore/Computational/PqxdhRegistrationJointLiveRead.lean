-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger

/-! Explicit reads of current native Beacon fields. Historical private service pools cannot make an erased field readable: the client checks its current phase before requesting a KEM secret. Returned values are current source fields, with the exact private disclosure history retained. No freshness or secrecy conclusion is imposed by this interface. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointLiveRead
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment
open PqxdhRegistrationJointOwnership (Entry Owned activeKey)
open PqxdhRegistrationJointPreparation (Pool)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry EncodedState encodeEntry encodeState)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Identity Key : Type}

inductive Field where
  | identity | kem | prekey | oneTime | kernel
  deriving DecidableEq

inductive Value (KemSK : Type) where
  | identity (seed : IdentitySeed)
  | kem (secret : KemSK)
  | prekey (scalar : ScalarBytes)
  | oneTime (scalar : ScalarBytes)
  | kernel (state : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel)

/-- Local fields are read directly from the current phase, including exactly the established kernel with its current chains and skipped keys. -/
def localValue (field : Field) (owner : RawCtxBeaconLifecycle.State Identity ScalarBytes Key) : Option (Value KemSK) :=
  match field, owner.beacon.phase with
  | .prekey, .fresh _ scalar _ | .prekey, .freshWithCoins _ scalar _ _ | .prekey, .initSent _ scalar _ _ => some (.prekey scalar)
  | .oneTime, .freshWithCoins _ _ scalar _ | .oneTime, .initSent _ _ scalar _ => some (.oneTime scalar)
  | .kernel, .established _ _ kernel => some (.kernel kernel)
  | _, _ => none

/-- The complete native field projection. Identity stays live after terminal finish; KEM, prekey and one-time fields follow the actual source phase erasure. -/
def value (field : Field) (owner : PqxdhRegistrationSchedule.Owner KemSK) : Option (Value KemSK) :=
  match field with
  | .identity => some (.identity owner.beacon.identity)
  | .kem => (activeKey owner).map fun pair => .kem pair.2
  | _ => localValue field owner

/-- Only a currently present KEM field supplies a service handle. The private pool is not searched on erased phases. -/
def kemHandle (owner : PqxdhRegistrationJointBundle.Owner) : Option Nat :=
  match owner.beacon.phase with
  | .fresh _ _ key | .freshWithCoins _ _ _ key | .initSent _ _ _ key => some key.2
  | _ => none

/-- Record exactly the disclosures made through the primitive services; direct local field reads make no private service call. -/
def entrySource (field : Field) (entry : Entry KemSK) (pool : Pool KemSK) : Option (Value KemSK) × Pool KemSK :=
  match field with
  | .identity => (value field entry.owner,
      (PqxdhDynamicIdentityPool.record (.inr (.reveal entry.identityIndex)) (some entry.owner.beacon.identity) pool.1, pool.2))
  | .kem => match activeKey entry.owner with
    | none => (none, pool)
    | some key => (some (.kem key.2),
        (pool.1, PqxdhLiveKemBirth.record (.reveal entry.kemIndex) (some key.2) pool.2))
  | _ => (localValue field entry.owner, pool)

/-- The handle client accesses only its current owner representation. Service handles and complete private pools are not returned through this interface. -/
def entryClient (field : Field) (entry : EncodedEntry) : OracleComp (PqxdhLiveKemBirth.Spec KemSK) (Option (Value KemSK)) :=
  match field with
  | .identity => Option.map Value.identity <$> (PqxdhLiveKemBirth.Spec KemSK).query (.inl (.inr (.reveal entry.2.2.beacon.identity.1)))
  | .kem => match kemHandle entry.2.2 with
    | none => pure none
    | some index => Option.map Value.kem <$> (PqxdhLiveKemBirth.Spec KemSK).query (.inr (.inr (.reveal index)))
  | _ => pure (localValue field entry.2.2)

set_option backward.isDefEq.respectTransparency false in
/-- Under generated slot ownership, every field read has the exact current native value and complete private poststate, including erased-field rejection. -/
theorem entry_source (setup : Setup baseSpec KemSK) (field : Field) (entry : Entry KemSK) (pool : Pool KemSK)
    (owned : Owned pool entry) :
    (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
      (entryClient field (encodeEntry setup entry))).run pool = pure (entrySource field entry pool) := by
  cases field
  case kem =>
    cases phase : entry.owner.beacon.phase <;>
      simp [entryClient, kemHandle, entrySource, activeKey, encodeEntry, PqxdhRegistrationJointBundle.encode,
        PqxdhBeaconPhase1Publication.mapState, PqxdhBeaconPhase1Publication.mapPhase, phase,
        PqxdhRegistrationJointBundle.keyMap]
    all_goals first | rfl | simp only [PqxdhLiveKemBirth.impl, PqxdhLiveKemBirth.poolImpl, StateT.run, map_pure, Option.map_map]
    all_goals rw [owned.2 _ (by simp only [activeKey, phase]; rfl), Option.map_some, Option.map_some]
    all_goals rfl
  case identity =>
    simp [entryClient, entrySource, value, encodeEntry, PqxdhRegistrationJointBundle.encode,
      PqxdhBeaconPhase1Publication.mapState, PqxdhRegistrationJointBundle.identityMap, StateT.run]
    change StateT.run (_ <$> _) pool = _
    rw [StateT.run_map]
    simp only [PqxdhLiveKemBirth.impl, PqxdhDynamicIdentityPool.lazyImpl,
      PqxdhDynamicIdentityPool.poolImpl, StateT.run, owned.1, map_pure, Option.map_some]
  all_goals cases phase : entry.owner.beacon.phase <;>
    simp [entryClient, entrySource, localValue, encodeEntry, PqxdhRegistrationJointBundle.encode,
      PqxdhBeaconPhase1Publication.mapState, PqxdhBeaconPhase1Publication.mapPhase, phase, StateT.run_pure]

/-- The reply is precisely the current native field projection, independently of either historical private pool. -/
theorem entry_value (field : Field) (entry : Entry KemSK) (pool : Pool KemSK) :
    (entrySource field entry pool).1 = value field entry.owner := by
  cases field <;> cases phase : entry.owner.beacon.phase <;>
    simp [entrySource, value, activeKey, phase]

/-- Disclosure histories can grow, but every exact seed and KEM slot is unchanged. -/
theorem entry_slots (field : Field) (entry : Entry KemSK) (pool : Pool KemSK) :
    (entrySource field entry pool).2.1.seeds = pool.1.seeds ∧
      (entrySource field entry pool).2.2.keys = pool.2.keys := by
  cases field <;> cases phase : entry.owner.beacon.phase <;>
    simp [entrySource, activeKey, phase, PqxdhDynamicIdentityPool.record, PqxdhLiveKemBirth.record]

abbrev ReadSpec (KemSK : Type) : OracleSpec (Nat × Field) := fun _ => Option (Value KemSK)

/-- A missing address rejects. A present owner supplies only its current field and exact disclosure history. -/
def sourceStep (request : Nat × Field) (state : PqxdhRegistrationJointSchedule.State KemSK) :
    Option (Value KemSK) × PqxdhRegistrationJointSchedule.State KemSK :=
  match state.owners[request.1]? with
  | none => (none, state)
  | some entry =>
    let result := entrySource request.2 entry state.pool
    (result.1, { state with pool := result.2 })

def clientStep (request : Nat × Field) : PqxdhRegistrationJointServiceSchedule.Client KemSK Response (Option (Value KemSK)) := fun owners =>
  match owners[request.1]? with
  | none => pure (none, owners)
  | some entry => (fun result => (result, owners)) <$>
      simulateQ PqxdhRegistrationJointServiceSchedule.poolLift (entryClient request.2 entry)

/-- The current-field read has exactly the source reply and full encoded poststate at every present or missing address. -/
theorem read_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (request : Nat × Field)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (owned : PqxdhRegistrationJointSchedule.Invariant state) :
    PqxdhRegistrationJointServiceSchedule.execute setup codec checks serverSeed (clientStep request) (encodeState setup state) =
      pure ((sourceStep request state).1, encodeState setup (sourceStep request state).2) := by
  cases found : state.owners[request.1]? with
  | none =>
      simp [PqxdhRegistrationJointServiceSchedule.execute, StateT.run, clientStep, sourceStep, encodeState, List.getElem?_map, found]
      rfl
  | some entry =>
      simp only [PqxdhRegistrationJointServiceSchedule.execute, StateT.run, clientStep, encodeState,
        List.getElem?_map, found, Option.map_some, simulateQ_map]
      change _ <$> StateT.run (_ <$> _) _ = _
      rw [StateT.run_map, PqxdhRegistrationJointServiceSchedule.pool_program,
        entry_source setup request.2 entry state.pool (owned entry (List.mem_of_getElem? found))]
      simp [sourceStep, found]

/-- Current-field disclosure preserves generated ownership for every owner, with no restriction on earlier or later compromise. -/
theorem read_owned (request : Nat × Field) (state : PqxdhRegistrationJointSchedule.State KemSK)
    (owned : PqxdhRegistrationJointSchedule.Invariant state) :
    PqxdhRegistrationJointSchedule.Invariant (sourceStep request state).2 := by
  cases found : state.owners[request.1]? with
  | none => simpa only [sourceStep, found] using owned
  | some entry =>
      simp only [sourceStep, found, PqxdhRegistrationJointSchedule.Invariant]
      exact fun other present => PqxdhRegistrationJointOwnership.owned_slots state.pool
        (entrySource request.2 entry state.pool).2 other
        (entry_slots request.2 entry state.pool).1 (entry_slots request.2 entry state.pool).2
        (owned other present)

/-- The native compromise interface reads only the current addressed owner and leaves the complete protocol state unchanged. -/
def nativeStep (request : Nat × Field) (state : PqxdhRegistrationSchedule.State KemSK) :
    Option (Value KemSK) × PqxdhRegistrationSchedule.State KemSK :=
  ((state.owners[request.1]?).bind (value request.2), state)

/-- Removing private service annotations gives the literal current-native-field read and the unchanged complete native state. -/
theorem read_projection (request : Nat × Field) (state : PqxdhRegistrationJointSchedule.State KemSK) :
    ((sourceStep request state).1, PqxdhRegistrationJointSchedule.source (sourceStep request state).2) =
      nativeStep request (PqxdhRegistrationJointSchedule.source state) := by
  cases found : state.owners[request.1]? <;>
    simp [sourceStep, nativeStep, PqxdhRegistrationJointSchedule.source, List.getElem?_map, found, entry_value]

/-- Erased KEM fields cause no historical service lookup or history append, even when that old private slot still exists. -/
theorem erased_client (entry : EncodedEntry) (erased : kemHandle entry.2.2 = none) :
    entryClient (KemSK := KemSK) .kem entry = pure none := by
  simp only [entryClient, erased]

end BeaconcryptCore.Computational.PqxdhRegistrationJointLiveRead

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointLiveRead.entry_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointLiveRead.entry_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointLiveRead.entry_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointLiveRead.entry_value

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointLiveRead.entry_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointLiveRead.entry_slots

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointLiveRead.read_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointLiveRead.read_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointLiveRead.read_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointLiveRead.read_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointLiveRead.read_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointLiveRead.read_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointLiveRead.erased_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointLiveRead.erased_client
