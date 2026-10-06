-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptInvariant

/-! Literal non-signing source operations retain the immutable constructor receipts and all previously issued attempts. Native finish may erase live fields; this proof never reconstructs or reveals them from its analysis ledger. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptPreservation
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhEd25519EufCma
open PqxdhRegistrationJointOwnership (Entry)
open PqxdhRegistrationJointSigningTranscript (messagesAt)
open PqxdhRegistrationJointAttemptTrace (LiveFixed)
open PqxdhRegistrationJointAttemptLedger PqxdhRegistrationJointAttemptInvariant
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- Complete native updates retain the historical receipt invariant whenever they preserve the literal private slots/signing projection and the current live-field relation. -/
theorem retained (setup : Setup baseSpec KemSK) (state : State KemSK)
    (after : PqxdhRegistrationJointSchedule.State KemSK) (valid : Invariant setup state)
    (seeds : after.pool.1.seeds = state.1.pool.1.seeds) (keys : after.pool.2.keys = state.1.pool.2.keys)
    (messages : ∀ index, messagesAt index after.pool.1.transcript = messagesAt index state.1.pool.1.transcript)
    (live : ∀ entry ∈ after.owners, ∃ receipt, state.2 entry.identityIndex = some receipt ∧
      receipt.kemIndex = entry.kemIndex ∧ LiveFixed setup entry.owner receipt.prekey receipt.pqKey) :
    Invariant setup (after, state.2) := by
  exact ⟨fun index receipt found => by simpa only [seeds] using valid.allocated index receipt found,
    fun index receipt found => by simpa only [keys] using valid.kem index receipt found,
    valid.fixed, fun index => (messages index).trans (valid.exactHistory index), live⟩

/-- Whole native finish retains constructor receipts, original KEM slots and every signing attempt even when it erases or aborts the current owner. -/
theorem finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (address : Nat) (raw : Pqxdh.Bytes) (state : State KemSK)
    (result : Option Pqxdh.Bytes × PqxdhRegistrationJointSchedule.State KemSK)
    (valid : Invariant setup state)
    (supported : result ∈ support ((PqxdhRegistrationJointSchedule.finish setup codec address raw).run state.1)) :
    Invariant setup (result.2, state.2) := by
  cases found : state.1.owners[address]? <;>
    simp only [PqxdhRegistrationJointSchedule.finish, StateT.run, found, support_map, Set.mem_image, mem_support_pure_iff] at supported
  case none => simpa only [supported] using valid
  case some entry =>
    obtain ⟨reached, member, rfl⟩ := supported
    have slots := PqxdhRegistrationJointFinish.annotated_program_slots setup codec entry.identityIndex entry.kemIndex
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw entry.owner) (state.1.pool, state.1.shared) reached member
    apply retained setup state _ valid slots.1 slots.2
    · exact fun index => PqxdhRegistrationJointNonSigningHistory.finish setup codec entry.identityIndex entry.kemIndex index
        codec.frameRead raw entry.owner (state.1.pool, state.1.shared) reached member
    · intro current present
      rcases List.mem_or_eq_of_mem_set present with previous | updated
      · exact valid.live current previous
      · subst current
        obtain ⟨receipt, recorded, kem, live⟩ := valid.live entry (List.mem_of_getElem? found)
        exact ⟨receipt, recorded, kem, fun actual active => live actual
          (PqxdhRegistrationJointAttemptTrace.finish_basis setup
            (PqxdhRegistrationJointFinish.annotated setup codec entry.identityIndex entry.kemIndex)
            codec.frameRead raw entry.owner (state.1.pool, state.1.shared) reached member actual active)⟩

/-- Actual raw Server acceptance retains the complete earlier issued-attempt history through all signature checks, DH, root generation and optional pending publication. -/
theorem accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : State KemSK)
    (result : Option Nat × PqxdhRegistrationJointSchedule.State KemSK)
    (valid : Invariant setup state)
    (supported : result ∈ support ((PqxdhRegistrationJointServerSchedule.onBackend
      (PqxdhRegistrationJointServerAccept.source setup codec checks seed identityIndex raw)).run state.1)) :
    Invariant setup (result.2, state.2) := by
  simp only [PqxdhRegistrationJointServerSchedule.onBackend, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨reached, member, rfl⟩ := supported
  have slots := PqxdhRegistrationJointServerAccept.source_slots setup codec checks seed identityIndex raw (state.1.pool, state.1.shared) reached member
  exact retained setup state _ valid slots.1 slots.2
    (fun index => PqxdhRegistrationJointNonSigningHistory.server_accept setup codec checks seed identityIndex index raw
      (state.1.pool, state.1.shared) reached member) valid.live

/-- Current-field disclosure preserves immutable receipts and signing history; disclosure does not make erased native fields live again. -/
theorem read (setup : Setup baseSpec KemSK) (request : Nat × PqxdhRegistrationJointLiveRead.Field)
    (state : State KemSK) (valid : Invariant setup state) :
    Invariant setup ((PqxdhRegistrationJointLiveRead.sourceStep request state.1).2, state.2) := by
  cases found : state.1.owners[request.1]? with
  | none => simpa only [PqxdhRegistrationJointLiveRead.sourceStep, found] using valid
  | some entry =>
      apply retained setup state _ valid
        (by simpa only [PqxdhRegistrationJointLiveRead.sourceStep, found] using (PqxdhRegistrationJointLiveRead.entry_slots request.2 entry state.1.pool).1)
        (by simpa only [PqxdhRegistrationJointLiveRead.sourceStep, found] using (PqxdhRegistrationJointLiveRead.entry_slots request.2 entry state.1.pool).2)
      · exact fun index => PqxdhRegistrationJointNonSigningHistory.live_read request state.1 index
      · simpa only [PqxdhRegistrationJointLiveRead.sourceStep, found] using valid.live

/-- Actual shared Server/public work retains every owner receipt and signing transcript while preserving its own complete shared poststate. -/
theorem shared (setup : Setup baseSpec KemSK) (work : NativeGame KemSK Result) (state : State KemSK)
    (result : Result × PqxdhRegistrationJointSchedule.State KemSK) (valid : Invariant setup state)
    (supported : result ∈ support ((PqxdhRegistrationJointSchedule.onShared work).run state.1)) :
    Invariant setup (result.2, state.2) := by
  simp only [PqxdhRegistrationJointSchedule.onShared, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨reached, _, rfl⟩ := supported
  exact retained setup state _ valid rfl rfl (fun _ => rfl) valid.live

end BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptPreservation

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptPreservation.retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptPreservation.retained

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptPreservation.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptPreservation.finish

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptPreservation.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptPreservation.accept

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptPreservation.read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptPreservation.read

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptPreservation.shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptPreservation.shared
