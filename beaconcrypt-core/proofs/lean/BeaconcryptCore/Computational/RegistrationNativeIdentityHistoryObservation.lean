-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistorySync
import BeaconcryptCore.Computational.RegistrationNativeIdentityCompiler

/-! Dropping duplicate uniform observations from the private source projection changes no joint-service history. A public report therefore uses the same signed-message freshness as the actual native owner's chronological log once synchronization is established. The report remains at the actual generated handle. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryObservation
open PqxdhJointIdentity
open PqxdhDynamicIdentityPool (SourceState Observation)
open RegistrationNativeIdentityHistory
variable {source : RegistrationNativeMldsa.Source}

theorem history_filter (identity : Nat) (transcript : List Observation) :
    history identity (transcript.filter RegistrationNativeIdentityCompiler.keep) = history identity transcript := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      rcases observation with ⟨query, answer⟩
      cases query with
      | inl coin => simpa only [RegistrationNativeIdentityCompiler.keep, List.filter_cons_of_neg,
          Bool.false_eq_true, not_false_eq_true, history, List.filterMap_cons, entry] using ih
      | inr request =>
          rw [List.filter_cons_of_pos (show RegistrationNativeIdentityCompiler.keep ⟨.inr request, answer⟩ = true from rfl)]
          simp only [history] at ih
          cases request with
          | create => cases answer <;> simpa [history, entry, List.filterMap_cons] using ih
          | reveal selected => simpa [history, entry, List.filterMap_cons] using ih
          | service selected request =>
              cases answer with
              | none => simpa [history, entry, List.filterMap_cons] using ih
              | some reply =>
                  by_cases same : selected = identity <;> simp [history, entry, same, ih]

theorem pool_view_history (identity : Nat) (pool : SourceState) :
    history identity (RegistrationNativeIdentityCompiler.poolView pool).transcript = history identity pool.transcript :=
  history_filter identity pool.transcript

theorem pool_view_synced (pool : SourceState) (owners : RegistrationNativeIdentityFrontend.State source) :
    RegistrationNativeIdentityHistorySync.Synced (RegistrationNativeIdentityCompiler.poolView pool) owners ↔
      RegistrationNativeIdentityHistorySync.Synced pool owners := by
  simp only [RegistrationNativeIdentityHistorySync.Synced, pool_view_history]

/-- The ordinary public monitor's exact transcript history has the same weak-EUF signing freshness as the native current owner. -/
theorem replay_signed {count : Nat} (identity : Fin count) (pool : SourceState)
    (owners : RegistrationNativeIdentityFrontend.State source)
    (synced : RegistrationNativeIdentityHistorySync.Synced pool owners)
    (owner : RegistrationNativeIdentityFrontend.Owner source) (member : owner ∈ owners)
    (handle : owner.identity.handle = identity.1) :
    signedMessages ((replay count pool.transcript).histories identity) = signedMessages owner.edHistory := by
  rw [replay_history, ← handle]
  exact synced owner member

end BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryObservation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryObservation.history_filter' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryObservation.history_filter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryObservation.pool_view_history' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryObservation.pool_view_history

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryObservation.pool_view_synced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryObservation.pool_view_synced

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryObservation.replay_signed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryObservation.replay_signed
