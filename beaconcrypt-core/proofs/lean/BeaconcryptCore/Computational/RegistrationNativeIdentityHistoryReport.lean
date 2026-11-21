-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryObservation
import BeaconcryptCore.Computational.RegistrationNativeIdentityMain
import BeaconcryptCore.Computational.RegistrationNativeEdOrigin

/-! Candidate reports keep every matching generated public-key alias. At the report prefix, synchronized actual native signing histories yield the owner's fixed prekey or the ordinary joint-use field-origin event at that same generated handle. Freshness and finite family capacity remain explicit in this local adapter; no field or alias index is guessed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReport
open PqxdhJointIdentity
open PqxdhDynamicIdentityPool (SourceState)
open PqxdhDynamicIdentityReports (PublicSnapshot sourceKeys)
open PqxdhJointPhase1Reports
open RegistrationNativeIdentityFrontend (Owner)
open RegistrationNativeIdentityHistorySync (Synced)
variable {source : RegistrationNativeMldsa.Source}

def snapshot (joint : Primitives) (count : Nat) (pool : SourceState) : PublicSnapshot count :=
  ⟨sourceKeys joint pool.seeds, RegistrationNativeIdentityHistory.replay count pool.transcript⟩

theorem generated_key (joint : Primitives) (pool : SourceState)
    (owners : RegistrationNativeIdentityFrontend.State source)
    (owned : RegistrationNativeIdentityRealization.Owned joint pool owners)
    (owner : Owner source) (member : owner ∈ owners) :
    sourceKeys joint pool.seeds owner.identity.handle = some owner.identity.publicIdentity := by
  obtain ⟨seed, receipt⟩ := owned owner member
  simp only [sourceKeys, receipt.1, Option.map_some, ← receipt.2]

theorem monitor_fixed (joint : Primitives) (count : Nat) (pool : SourceState)
    (owners : RegistrationNativeIdentityFrontend.State source) (synced : Synced pool owners)
    (owner : Owner source) (member : owner ∈ owners) (valid : owner.identity.handle < count)
    (fixed : RegistrationNativeEdOrigin.FixedPrekey (PqxdhPhase2InputBytes.word owner.prekeyPublic) owner.edHistory) :
    RegistrationNativeEdOrigin.FixedPrekey (PqxdhPhase2InputBytes.word owner.prekeyPublic)
      ((snapshot joint count pool).history.histories ⟨owner.identity.handle, valid⟩) := by
  intro message issued
  change message ∈ signedMessages ((RegistrationNativeIdentityHistory.replay count pool.transcript).histories
    ⟨owner.identity.handle, valid⟩) at issued
  have equal := RegistrationNativeIdentityHistoryObservation.replay_signed ⟨owner.identity.handle, valid⟩ pool owners synced owner member rfl
  rw [equal] at issued
  exact fixed message issued

/-- An actual changed accepted prekey is recognized by the existing ordinary generated-index monitor at this prefix. -/
theorem prekey_or_event (joint : Primitives) (count : Nat) (pool : SourceState)
    (owners : RegistrationNativeIdentityFrontend.State source)
    (owned : RegistrationNativeIdentityRealization.Owned joint pool owners) (synced : Synced pool owners)
    (owner : Owner source) (member : owner ∈ owners) (valid : owner.identity.handle < count)
    (fixed : RegistrationNativeEdOrigin.FixedPrekey (PqxdhPhase2InputBytes.word owner.prekeyPublic) owner.edHistory)
    (fresh : (⟨owner.identity.handle, valid⟩ : Fin count) ∉ (snapshot joint count pool).history.reveals)
    (candidate : PqxdhEd25519EufCma.Phase1Candidate) (decoded : PqxdhEd25519EufCma.Phase1KeyTuple)
    (accepted : PqxdhEd25519EufCma.acceptPhase1Candidate joint.verify candidate = some (owner.identity.publicIdentity.ed25519, decoded)) :
    decoded.prekey = PqxdhPhase2InputBytes.word owner.prekeyPublic ∨
      candidateAccepted joint ⟨owner.identity.handle, candidate⟩ (snapshot joint count pool) = true := by
  have origin := RegistrationNativeEdOrigin.prekey_or_report joint owner.identity.publicIdentity candidate decoded
    ((snapshot joint count pool).history.histories ⟨owner.identity.handle, valid⟩) accepted
    (PqxdhPhase2InputBytes.word owner.prekeyPublic) (monitor_fixed joint count pool owners synced owner member valid fixed)
  rcases origin with same | ⟨forgery, selected, _winning⟩
  · exact Or.inl same
  · right
    apply (candidateAccepted_iff joint _ _).mpr
    refine ⟨valid, owner.identity.publicIdentity, decoded, generated_key joint pool owners owned owner member, accepted, fresh, ?_⟩
    have unissued := selectUnissued_some _ candidate forgery selected
    exact ⟨forgery, unissued.1, unissued.2⟩

/-- Public-key aliases all remain in the actual pre-accept report list; this membership requires no injectivity or selected alias. -/
theorem reports_owner (packet : registration.InitPacket) (owners : RegistrationNativeIdentityFrontend.State source)
    (owner : Owner source) (member : owner ∈ owners)
    (matched : PqxdhEd25519EufCma.encodedIdentity owner.identity.publicIdentity.ed25519 =
      PqxdhRefinement.absBytes packet.identity_key) :
    (⟨owner.identity.handle, RegistrationRootInput.candidate packet⟩ : CandidateReport) ∈
      RegistrationNativeIdentityMain.reports packet owners := by
  apply List.mem_filterMap.mpr
  exact ⟨owner, member, by simp only [ite_eq_left matched]⟩

/-- Actual accepted native candidates have the tagged identity encoding used by the real alias-report filter. -/
theorem reports_accepted (joint : Primitives) (packet : registration.InitPacket)
    (owners : RegistrationNativeIdentityFrontend.State source) (owner : Owner source) (member : owner ∈ owners)
    (decoded : PqxdhEd25519EufCma.Phase1KeyTuple)
    (accepted : PqxdhEd25519EufCma.acceptPhase1Candidate joint.verify (RegistrationRootInput.candidate packet) =
      some (owner.identity.publicIdentity.ed25519, decoded)) :
    (⟨owner.identity.handle, RegistrationRootInput.candidate packet⟩ : CandidateReport) ∈
      RegistrationNativeIdentityMain.reports packet owners := by
  apply reports_owner packet owners owner member
  exact (PqxdhEd25519EufCma.acceptPhase1Candidate_some_witness joint.verify (RegistrationRootInput.candidate packet)
    owner.identity.publicIdentity.ed25519 decoded accepted).1.symm

end BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReport

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReport.generated_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReport.generated_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReport.monitor_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReport.monitor_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReport.prekey_or_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReport.prekey_or_event

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReport.reports_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReport.reports_owner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReport.reports_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReport.reports_accepted
