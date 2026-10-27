-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptProperties

/-! The source ledger retains literal constructor fields after native erasure and exactly matches each creation index's ordinary signing history. Its invariant is established by actual creation and preserved by source operations, rather than imposed on an accepted candidate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInvariant
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhEd25519EufCma
open PqxdhRegistrationJointOwnership (Entry)
open PqxdhRegistrationJointSigningTranscript (messagesAt)
open PqxdhRegistrationJointIssuedAttempts (history Fixed)
open PqxdhRegistrationJointAttemptTrace (LiveFixed)
open PqxdhRegistrationJointAttemptLedger
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

def attempts (ledger : Ledger) (index : Nat) : List Phase1KeyTuple :=
  ((ledger index).map Receipt.attempts).getD []

/-- Every immutable receipt is allocated by a source birth and retains its original public KEM slot. All actual signatures, including failed-writer attempts, are represented in order. Live source fields agree with this older receipt; they are never reconstructed after erasure. -/
structure Invariant (setup : Setup baseSpec KemSK) (state : State KemSK) : Prop where
  allocated : ∀ index receipt, state.2 index = some receipt → index < state.1.pool.1.seeds.length
  kem : ∀ index receipt, state.2 index = some receipt →
    (state.1.pool.2.keys[receipt.kemIndex]?).map Prod.fst = some receipt.pqKey
  fixed : ∀ index receipt, state.2 index = some receipt → Fixed receipt.prekey receipt.pqKey receipt.attempts
  exactHistory : ∀ index, messagesAt index state.1.pool.1.transcript = history (attempts state.2 index)
  live : ∀ entry ∈ state.1.owners, ∃ receipt, state.2 entry.identityIndex = some receipt ∧
    receipt.kemIndex = entry.kemIndex ∧ LiveFixed setup entry.owner receipt.prekey receipt.pqKey

/-- No constructor receipt exists at a future allocation index. -/
theorem future_empty (setup : Setup baseSpec KemSK) (state : State KemSK) (valid : Invariant setup state)
    (index : Nat) (future : state.1.pool.1.seeds.length ≤ index) : state.2 index = none := by
  cases found : state.2 index with
  | none => rfl
  | some receipt => exact False.elim (Nat.not_lt_of_ge future (valid.allocated index receipt found))

/-- Actual identity/KEM creation appends no successful signing message at any index. -/
theorem created_messages (setup : Setup baseSpec KemSK) (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (material : PqxdhRegistrationJointCreation.Material KemSK) (index : Nat) :
    messagesAt index (PqxdhRegistrationJointCreation.serviceView setup pool material).2.1.transcript =
      messagesAt index pool.1.transcript := by
  simp [PqxdhRegistrationJointCreation.serviceView, PqxdhDynamicIdentityPool.createdReply,
    PqxdhDynamicIdentityPool.record, messagesAt, PqxdhRegistrationJointSigningTranscript.messageAt]

/-- Empty-owner initialization supplies every receipt invariant once the actual prior service prefix has issued no signatures. -/
theorem initial_invariant (setup : Setup baseSpec KemSK) (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (shared : NativeState KemSK) (unsigned : ∀ index, messagesAt index pool.1.transcript = []) :
    Invariant setup (initial (PqxdhRegistrationJointSchedule.initial pool shared)) := by
  constructor <;> simp [initial, PqxdhRegistrationJointSchedule.initial, attempts, history, unsigned]

/-- Actual creation records only its new constructor fields while retaining every prior receipt, signing history and live-owner relation. -/
theorem created_invariant (setup : Setup baseSpec KemSK) (pin : PqxdhBeaconPhase2Preparation.Word32)
    (keyId : Std.U64) (state : State KemSK) (material : PqxdhRegistrationJointCreation.Material KemSK)
    (valid : Invariant setup state) : Invariant setup (created setup pin keyId state material).2 := by
  constructor
  case allocated =>
    intro index receipt found
    by_cases same : index = state.1.pool.1.seeds.length
    · simp [created, PqxdhRegistrationJointSchedule.created, PqxdhRegistrationJointCreation.serviceView,
        PqxdhDynamicIdentityPool.createdReply, PqxdhDynamicIdentityPool.record, same]
    · simp only [created, Function.update_apply, ite_eq_right same] at found
      simpa [created, PqxdhRegistrationJointSchedule.created, PqxdhRegistrationJointCreation.serviceView,
        PqxdhDynamicIdentityPool.createdReply, PqxdhDynamicIdentityPool.record] using Nat.lt_succ_of_lt (valid.allocated index receipt found)
  case kem =>
    intro index receipt found
    by_cases same : index = state.1.pool.1.seeds.length
    · have equal : birth setup state.1.pool.2.keys.length material = receipt := by simpa [created, same] using found
      subst receipt
      simp [created, birth, PqxdhRegistrationJointSchedule.created, PqxdhRegistrationJointCreation.serviceView,
        PqxdhLiveKemBirth.created, PqxdhLiveKemBirth.record]
    · have before : state.2 index = some receipt := by simpa [created, Function.update_apply, same] using found
      obtain ⟨pair, atIndex, _⟩ := Option.map_eq_some_iff.mp (valid.kem index receipt before)
      change ((state.1.pool.2.keys ++ [material.keys])[receipt.kemIndex]?).map Prod.fst = some receipt.pqKey
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp atIndex).choose]
      exact valid.kem index receipt before
  case fixed =>
    intro index receipt found
    by_cases same : index = state.1.pool.1.seeds.length
    · have equal : birth setup state.1.pool.2.keys.length material = receipt := by simpa [created, same] using found
      subst receipt
      simp [birth, Fixed]
    · exact valid.fixed index receipt (by simpa [created, Function.update_apply, same] using found)
  case exactHistory =>
    intro index
    change messagesAt index (PqxdhRegistrationJointCreation.serviceView setup state.1.pool material).2.1.transcript = _
    rw [created_messages, valid.exactHistory]
    by_cases same : index = state.1.pool.1.seeds.length
    · subst index
      simp [attempts, created, birth, future_empty setup state valid _ (Nat.le_refl _)]
    · simp [attempts, created, same]
  case live =>
    intro entry member
    rcases List.mem_append.mp member with previous | born
    · obtain ⟨receipt, found, kem, live⟩ := valid.live entry previous
      have different := Nat.ne_of_lt (valid.allocated entry.identityIndex receipt found)
      exact ⟨receipt, by simpa [created, Function.update_apply, different] using found, kem, live⟩
    · obtain rfl := List.mem_singleton.mp born
      refine ⟨birth setup state.1.pool.2.keys.length material, ?_, rfl, ?_⟩
      · simp [created, PqxdhRegistrationJointSchedule.birth]
      · simp [LiveFixed, PqxdhRegistrationJointAttemptTrace.basis, birth, PqxdhRegistrationJointSchedule.birth]

/-- Reinstall the same complete returned owner and private signing transcript while replacing only the selected receipt's chronological attempts. -/
theorem bundle_result (setup : Setup baseSpec KemSK) (state : State KemSK) (address : Nat)
    (entry : Entry KemSK) (receipt : Receipt) (valid : Invariant setup state)
    (found : state.2 entry.identityIndex = some receipt) (sameKem : receipt.kemIndex = entry.kemIndex)
    (result : PqxdhRegistrationJointAttemptTrace.NativeResult KemSK × List Phase1KeyTuple)
    (good : PqxdhRegistrationJointAttemptProperties.Good setup entry.identityIndex receipt state.1.pool.1 result) :
    Invariant setup
      ((⟨(result.1.2, state.1.pool.2), state.1.shared,
        state.1.owners.set address { entry with owner := result.1.1.2 }⟩ : PqxdhRegistrationJointSchedule.State KemSK),
        Function.update state.2 entry.identityIndex (some { receipt with attempts := result.2 })) := by
  constructor
  case allocated =>
    intro index current selected
    by_cases same : index = entry.identityIndex
    · simpa only [good.1, same] using valid.allocated entry.identityIndex receipt found
    · have previous : state.2 index = some current := by simpa [Function.update_apply, same] using selected
      simpa only [good.1] using valid.allocated index current previous
  case kem =>
    intro index current selected
    by_cases same : index = entry.identityIndex
    · have equal : { receipt with attempts := result.2 } = current := by simpa [same] using selected
      subst current
      exact valid.kem entry.identityIndex receipt found
    · exact valid.kem index current (by simpa [Function.update_apply, same] using selected)
  case fixed =>
    intro index current selected
    by_cases same : index = entry.identityIndex
    · have equal : { receipt with attempts := result.2 } = current := by simpa [same] using selected
      subst current
      exact good.2.1
    · exact valid.fixed index current (by simpa [Function.update_apply, same] using selected)
  case exactHistory =>
    intro index
    change messagesAt index result.1.2.transcript = _
    rw [good.2.2.2 index]
    by_cases same : index = entry.identityIndex <;>
      simp [attempts, same, valid.exactHistory index]
  case live =>
    intro current member
    rcases List.mem_or_eq_of_mem_set member with previous | replaced
    · obtain ⟨earlier, recorded, kem, live⟩ := valid.live current previous
      by_cases same : current.identityIndex = entry.identityIndex
      · have equal : earlier = receipt := Option.some.inj (recorded.symm.trans (same ▸ found))
        subst earlier
        exact ⟨{ receipt with attempts := result.2 }, by simp [same], kem, live⟩
      · exact ⟨earlier, by simpa [Function.update_apply, same] using recorded, kem, live⟩
    · subst current
      exact ⟨{ receipt with attempts := result.2 }, by simp, sameKem, good.2.2.1⟩

/-- Every actual present or missing bundle request preserves the full constructor/attempt invariant, including fresh draws, retained-coin retries, serialization failure and inactive owners. -/
theorem bundle_invariant (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (address : Nat) (state : State KemSK) (result : Option Pqxdh.Bytes × State KemSK)
    (valid : Invariant setup state) (supported : result ∈ support ((bundle setup codec address).run state)) :
    Invariant setup result.2 := by
  cases found : state.1.owners[address]? <;>
    simp only [bundle, StateT.run, found, support_map, Set.mem_image, mem_support_pure_iff] at supported
  case none => simpa only [supported] using valid
  case some entry =>
    obtain ⟨receipt, recorded, kem, live⟩ := valid.live entry (List.mem_of_getElem? found)
    simp only [recorded, Option.map_some, Option.getD_some] at supported
    obtain ⟨reached, member, rfl⟩ := supported
    exact bundle_result setup state address entry receipt valid recorded kem reached
      (PqxdhRegistrationJointAttemptProperties.trace_good setup codec entry.identityIndex entry.owner state.1.pool.1 receipt
        (valid.fixed entry.identityIndex receipt recorded) live
        (by simpa only [attempts, recorded, Option.map_some, Option.getD_some] using valid.exactHistory entry.identityIndex)
        reached member)

end BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInvariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInvariant.future_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInvariant.future_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInvariant.created_messages' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInvariant.created_messages

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInvariant.initial_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInvariant.initial_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInvariant.created_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInvariant.created_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInvariant.bundle_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInvariant.bundle_result

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInvariant.bundle_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInvariant.bundle_invariant
