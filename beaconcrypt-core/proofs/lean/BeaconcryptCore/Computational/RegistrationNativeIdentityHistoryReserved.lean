-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistory
import BeaconcryptCore.Computational.RegistrationNativeIdentityWorld

/-! A future generated handle has no earlier successful joint-service history. This property follows from the actual indexed source's rejection of uncreated handles and survives arbitrary adaptive source work. It supplies the empty chronological history at a later genuine birth, including histories containing rejected future-handle requests. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReserved
open PqxdhDynamicIdentityPool
open RegistrationNativeIdentityHistory (history entry)
open PqxdhServerAuthExperiment (Setup Checks)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

def ReservedEmpty (pool : SourceState) : Prop :=
  ∀ identity, pool.seeds.length ≤ identity → history identity pool.transcript = []

theorem record_history (identity : Nat) (query : DynamicSpec.Domain) (answer : DynamicSpec.Range query)
    (pool : SourceState) :
    history identity (record query answer pool).transcript =
      history identity pool.transcript ++ (entry identity ⟨query, answer⟩).toList := by
  simp only [record, history, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases entry identity ⟨query, answer⟩ <;> rfl

theorem initial_empty : ReservedEmpty initialState := by
  intro identity _
  rfl

/-- Rejected future service calls cannot create a signing or static-DH receipt for an identity not yet born. -/
theorem lazy_step (joint : PqxdhJointIdentity.Primitives) (query : DynamicSpec.Domain)
    (before : SourceState) (result : DynamicSpec.Range query × SourceState)
    (prior : ReservedEmpty before) (supported : result ∈ support ((lazyImpl joint query).run before)) :
    ReservedEmpty result.2 := by
  cases query with
  | inl coin =>
      simp only [lazyImpl, poolImpl, StateT.run, mem_support_bind_iff] at supported
      obtain ⟨reply, _, finished⟩ := supported
      simp only [mem_support_pure_iff] at finished
      cases finished
      intro identity future
      simpa [record, history, entry, List.filterMap_append] using prior identity future
  | inr query => cases query with
    | create =>
        rw [lazyImpl_create, support_map] at supported
        obtain ⟨seed, _, returned⟩ := supported
        cases returned
        intro identity future
        have earlier : before.seeds.length ≤ identity := by
          change (before.seeds ++ [seed]).length ≤ identity at future
          simp only [List.length_append, List.length_singleton] at future
          omega
        simpa [createdReply, record, history, entry, List.filterMap_append] using prior identity earlier
    | service selected request =>
        simp only [lazyImpl, poolImpl, StateT.run, mem_support_pure_iff] at supported
        cases supported
        intro identity future
        cases found : before.seeds[selected]? with
        | none =>
            simpa [record, history, found, entry, List.filterMap_append] using prior identity future
        | some seed =>
            have born := (List.getElem?_eq_some_iff.mp found).1
            have different : selected ≠ identity := by
              change before.seeds.length ≤ identity at future
              omega
            simpa [record, history, found, entry, different, List.filterMap_append] using prior identity future
    | reveal selected =>
        simp only [lazyImpl, poolImpl, StateT.run, mem_support_pure_iff] at supported
        cases supported
        intro identity future
        simpa [record, history, entry, List.filterMap_append] using prior identity future

theorem world_step (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Aeneas.Std.Array Aeneas.Std.U8 151#usize))
    (query : (RegistrationNativeIdentityFrontend.Trusted n KemSK).Domain)
    (before : RegistrationNativeIdentityWorld.State n KemSK)
    (result : (RegistrationNativeIdentityFrontend.Trusted n KemSK).Range query × RegistrationNativeIdentityWorld.State n KemSK)
    (prior : ReservedEmpty before.identities)
    (supported : result ∈ support ((RegistrationNativeIdentityWorld.implementation (mlSource := source)
      setup checks representation created query).run before)) : ReservedEmpty result.2.identities := by
  cases query with
  | inl query =>
      simp only [RegistrationNativeIdentityWorld.implementation, StateT.run, support_map] at supported
      obtain ⟨inner, _, returned⟩ := supported
      cases returned
      exact prior
  | inr query =>
      simp only [RegistrationNativeIdentityWorld.implementation, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, reached, returned⟩ := supported
      cases returned
      apply lazy_step setup.joint (.inr query) before.identities inner.1 prior
      apply OracleComp.support_simulateQ_run'_subset RegistrationWorldCoinCompiler.coin _ before.context.server.world.world.1
      rw [StateT.run'_eq, support_map]
      exact Set.mem_image_of_mem Prod.fst reached

/-- The internal reserved-handle property is derived at every reached prefix of an arbitrary actual native indexed-source program. -/
theorem world_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Aeneas.Std.Array Aeneas.Std.U8 151#usize))
    (work : OracleComp (RegistrationNativeIdentityFrontend.Trusted n KemSK) Value)
    (before : RegistrationNativeIdentityWorld.State n KemSK)
    (result : Value × RegistrationNativeIdentityWorld.State n KemSK)
    (prior : ReservedEmpty before.identities)
    (supported : result ∈ support ((simulateQ (RegistrationNativeIdentityWorld.implementation (mlSource := source)
      setup checks representation created) work).run before)) : ReservedEmpty result.2.identities :=
  OracleComp.simulateQ_run_preserves_inv_of_query _ (fun current => ReservedEmpty current.identities)
    (fun query current valid next reached => world_step setup checks representation created query current next valid reached)
    work before prior result supported

end BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReserved

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReserved.record_history' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReserved.record_history

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReserved.initial_empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReserved.initial_empty

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReserved.lazy_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReserved.lazy_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReserved.world_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReserved.world_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReserved.world_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReserved.world_program
