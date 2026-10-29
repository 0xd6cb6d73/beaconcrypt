-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistory
import BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleMetadata

/-! Generated handles, rather than public-key bytes, identify each native signing history. The actual source signing step and current-owner history update preserve exact signed-message synchronization. Optional static DH remains in the service transcript and changes no signing message. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityHistorySync
open PqxdhJointIdentity
open PqxdhDynamicIdentityPool (SourceState record)
open RegistrationNativeIdentityFrontend (Owner)
open RegistrationNativeIdentityHistory (history)
variable {source : RegistrationNativeMldsa.Source}

def handles (owners : RegistrationNativeIdentityFrontend.State source) : List Nat :=
  owners.map fun owner => owner.identity.handle

def Distinct (owners : RegistrationNativeIdentityFrontend.State source) : Prop :=
  (handles owners).Nodup

def Synced (pool : SourceState) (owners : RegistrationNativeIdentityFrontend.State source) : Prop :=
  ∀ owner ∈ owners, signedMessages (history owner.identity.handle pool.transcript) = signedMessages owner.edHistory

theorem distinct_fields (before after : RegistrationNativeIdentityFrontend.State source)
    (same : RegistrationNativeIdentityMetadata.keys after = RegistrationNativeIdentityMetadata.keys before)
    (prior : Distinct before) : Distinct after := by
  have projected := congrArg (List.map fun value => value.1.handle) same
  have sameHandles : handles after = handles before := by
    simpa only [RegistrationNativeIdentityMetadata.keys, RegistrationNativeIdentityMetadata.key,
      handles, List.map_map, Function.comp_def] using projected
  change (handles after).Nodup
  rw [sameHandles]
  exact prior

theorem synced_empty (pool : SourceState) : Synced pool ([] : RegistrationNativeIdentityFrontend.State source) := by
  intro owner member
  cases member

theorem signed_append (earlier later : History) :
    signedMessages (earlier ++ later) = signedMessages earlier ++ signedMessages later :=
  List.filterMap_append

private theorem other (pool : SourceState) (identity selected : Nat) (different : selected ≠ identity)
    (message : Pqxdh.Bytes) (signature : PqxdhEd25519EufCma.Ed25519Signature) :
    signedMessages (history identity
      (record (.inr (.service selected (.sign message))) (some signature) pool).transcript) =
      signedMessages (history identity pool.transcript) := by
  exact congrArg signedMessages
    (RegistrationNativeIdentityHistory.other_sign_history identity selected different pool.transcript message signature)

/-- The signature attempt reaches both chronological logs before any native packing or later publication result. Distinctness is about generated handles only. -/
theorem signed_sync (pool : SourceState) (owners : RegistrationNativeIdentityFrontend.State source)
    (index : Nat) (owner : Owner source) (found : owners[index]? = some owner)
    (unique : Distinct owners) (prior : Synced pool owners)
    (message : Pqxdh.Bytes) (signature : PqxdhEd25519EufCma.Ed25519Signature) :
    Synced (record (.inr (.service owner.identity.handle (.sign message))) (some signature) pool)
      (owners.set index { owner with edHistory := owner.edHistory ++ [.signed message signature] }) := by
  induction owners generalizing index with
  | nil => simp only [List.getElem?_nil] at found; cases found
  | cons first rest ih =>
      have distinct : first.identity.handle ∉ handles rest ∧ Distinct rest := by
        simpa only [Distinct, handles, List.map_cons, List.nodup_cons] using unique
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero] at found
          have sameOwner : first = owner := Option.some.inj found
          subst owner
          intro selected member
          change selected ∈ { first with edHistory := first.edHistory ++ [.signed message signature] } :: rest at member
          rcases List.mem_cons.mp member with same | member
          · subst selected
            change signedMessages (history first.identity.handle (pool.transcript ++
                [⟨.inr (.service first.identity.handle (.sign message)), some signature⟩])) =
              signedMessages (first.edHistory ++ [.signed message signature])
            rw [RegistrationNativeIdentityHistory.sign_history]
            simp only [signed_append, prior first (by simp)]
          · have different : first.identity.handle ≠ selected.identity.handle := by
              intro same
              exact distinct.1 (same ▸ List.mem_map.mpr ⟨selected, member, rfl⟩)
            rw [other pool selected.identity.handle first.identity.handle different]
            exact prior selected (List.mem_cons_of_mem first member)
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          have selectedMember : owner ∈ rest := List.mem_of_getElem? found
          have different : owner.identity.handle ≠ first.identity.handle := by
            intro same
            exact distinct.1 (same ▸ List.mem_map.mpr ⟨owner, selectedMember, rfl⟩)
          have later := ih index found distinct.2 (fun selected member => prior selected (List.mem_cons_of_mem first member))
          intro selected member
          change selected ∈ first :: rest.set index { owner with edHistory := owner.edHistory ++ [.signed message signature] } at member
          rcases List.mem_cons.mp member with same | member
          · subst selected
            rw [other pool first.identity.handle owner.identity.handle different]
            exact prior first (by simp)
          · exact later selected member

/-- Phase settlement retains every synchronized signing message even after failed publication or terminal abort. -/
theorem phase_sync (pool : SourceState) (owners : RegistrationNativeIdentityFrontend.State source)
    (index : Nat) (owner : Owner source) (phase : RegistrationNativeBeaconFrontend.Phase)
    (found : owners[index]? = some owner) (prior : Synced pool owners) :
    Synced pool (owners.set index { owner with phase }) := by
  intro selected member
  rcases List.mem_or_eq_of_mem_set member with member | rfl
  · exact prior selected member
  · exact prior owner (List.mem_of_getElem? found)

end BeaconcryptCore.Computational.RegistrationNativeIdentityHistorySync

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistorySync.distinct_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistorySync.distinct_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistorySync.synced_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistorySync.synced_empty

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistorySync.signed_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistorySync.signed_append

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistorySync.signed_sync' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistorySync.signed_sync

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistorySync.phase_sync' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistorySync.phase_sync
