-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner

/-! Exact private-slot ownership for the dynamically created native Beacon owners. These are representation invariants, not cryptographic authentication or freshness premises. Active KEM fields are checked in every source phase that still contains them; erased fields are not reconstructed from historical pools. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointOwnership
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment
open PqxdhRegistrationJointPreparation (Pool)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- An analysis entry distinguishes its public list address from both private service creation indices. The native owner is retained in full. -/
structure Entry (KemSK : Type) where
  identityIndex : Nat
  kemIndex : Nat
  owner : PqxdhRegistrationSchedule.Owner KemSK

/-- Exactly the KEM pair currently present in the source owner, never a recovered historical field. -/
def activeKey (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    Option (PqxdhKemIndCca.MlKem768PublicKey × KemSK) :=
  match owner.beacon.phase with
  | .fresh _ _ keys | .freshWithCoins _ _ _ keys | .initSent _ _ _ keys => some keys
  | .established _ _ _ | .aborted _ => none

/-- Every current identity field names its actual generated seed; each still-live KEM field names its exact generated pair. Equality of public encodings is never used to identify a slot. -/
def Owned (pool : Pool KemSK) (entry : Entry KemSK) : Prop :=
  pool.1.seeds[entry.identityIndex]? = some entry.owner.beacon.identity ∧
    ∀ keys, activeKey entry.owner = some keys → pool.2.keys[entry.kemIndex]? = some keys

/-- Callback histories can change freely while both private slot arrays retain their exact values. -/
theorem owned_slots (before after : Pool KemSK) (entry : Entry KemSK)
    (seeds : after.1.seeds = before.1.seeds) (keys : after.2.keys = before.2.keys)
    (owned : Owned before entry) : Owned after entry := by
  simpa only [Owned, seeds, keys] using owned

/-- The complete bundle trace retains its exact identity and active KEM fields, including a failed writer and retained-coin retry. -/
theorem bundle_fields (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (generated : Option ScalarBytes) (pool : PqxdhDynamicIdentityPool.SourceState) :
    (PqxdhRegistrationJointBundle.after setup codec index owner generated pool).1.2.beacon.identity = owner.beacon.identity ∧
      activeKey (PqxdhRegistrationJointBundle.after setup codec index owner generated pool).1.2 = activeKey owner := by
  cases phase : owner.beacon.phase <;> cases generated <;>
    simp only [PqxdhRegistrationJointBundle.after, PqxdhBeaconPhase1Publication.prepare, phase,
      Option.map_none, Option.map_some]
  all_goals first | trivial | split <;> simp [PqxdhBeaconPhase1Publication.publish, activeKey, phase]

/-- All three signatures and the optional writer preserve ownership of the actual returned native owner and every private seed slot. -/
theorem bundle_owned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (entry : Entry KemSK) (generated : Option ScalarBytes) (pool : Pool KemSK)
    (owned : Owned pool entry) :
    Owned ((PqxdhRegistrationJointBundle.after setup codec entry.identityIndex entry.owner generated pool.1).2, pool.2)
      { entry with owner := (PqxdhRegistrationJointBundle.after setup codec entry.identityIndex entry.owner generated pool.1).1.2 } := by
  simpa only [Owned, PqxdhRegistrationJointBundle.after_seeds,
    (bundle_fields setup codec entry.identityIndex entry.owner generated pool.1).1,
    (bundle_fields setup codec entry.identityIndex entry.owner generated pool.1).2] using owned

/-- Every terminal finish branch retains identity while removing the live KEM field, whether publication succeeds or aborts. -/
theorem finish_fields (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    (PqxdhBeaconPhase2Publication.finish control owner staged).2.beacon.identity = owner.beacon.identity ∧
      activeKey (PqxdhBeaconPhase2Publication.finish control owner staged).2 = none := by
  cases staged <;> simp only [PqxdhBeaconPhase2Publication.finish]
  all_goals (try split_ifs) <;> simp [PqxdhBeaconPhase2Preparation.abort, PqxdhBeaconPhase2Publication.publish, activeKey]

/-- A complete successful or refused native finish keeps identity and can only discard its live KEM field. The full callback state remains in the support premise. -/
theorem owner_fields {A : Type}
    (handler : QueryImpl (PqxdhRegistrationJointFinish.NativeSpec KemSK Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (before : A)
    (result : (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × A)
    (supported : result ∈ support ((simulateQ handler (PqxdhBeaconPhase2Publication.nativeOwner decode raw owner)).run before)) :
    result.1.2.beacon.identity = owner.beacon.identity ∧
      ∀ keys, activeKey result.1.2 = some keys → activeKey owner = some keys := by
  rcases result with ⟨⟨_ | plaintext, after⟩, final⟩
  case none =>
    have failed := PqxdhBeaconPhase2Publication.native_failure handler decode raw owner after before final supported
    cases phase : owner.beacon.phase <;> simp only [phase] at failed <;>
      simp [failed, PqxdhBeaconPhase2Preparation.abort, activeKey]
  case some =>
    obtain ⟨staged, _, _, published⟩ := PqxdhBeaconPhase2Publication.native_success handler decode raw plaintext owner after before final supported
    have afterEq : after = (PqxdhBeaconPhase2Publication.publish owner staged).2 := (congrArg Prod.snd published).symm
    simp [afterEq, PqxdhBeaconPhase2Publication.publish, activeKey]

/-- Actual annotated finish preserves exact slot ownership of its returned native owner and both complete private histories. -/
theorem owner_owned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (entry : Entry KemSK) (raw : Pqxdh.Bytes) (state : PqxdhRegistrationJointFinish.State KemSK)
    (result : (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × PqxdhRegistrationJointFinish.State KemSK)
    (owned : Owned state.1 entry)
    (supported : result ∈ support ((simulateQ
      (PqxdhRegistrationJointFinish.annotated setup codec entry.identityIndex entry.kemIndex)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw entry.owner)).run state)) :
    Owned result.2.1 { entry with owner := result.1.2 } := by
  have slots := PqxdhRegistrationJointFinish.annotated_program_slots setup codec entry.identityIndex entry.kemIndex
    (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw entry.owner) state result supported
  have fields := owner_fields (PqxdhRegistrationJointFinish.annotated setup codec entry.identityIndex entry.kemIndex)
    codec.frameRead raw entry.owner state result supported
  simp only [Owned, slots.1, slots.2, fields.1]
  exact ⟨owned.1, fun keys live => owned.2 keys (fields.2 keys live)⟩

end BeaconcryptCore.Computational.PqxdhRegistrationJointOwnership

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOwnership.owned_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOwnership.owned_slots

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOwnership.bundle_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOwnership.bundle_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOwnership.bundle_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOwnership.bundle_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOwnership.finish_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOwnership.finish_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOwnership.owner_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOwnership.owner_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOwnership.owner_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOwnership.owner_owned
