-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3KeyService

/-! Successful descriptor flags imply the inner realized-input preparation fact throughout the actual compiler stack. Consequently the direct G2 service has the exact complete reply and descriptor-flag state of both compiled phases, for arbitrary adaptive clients. The proof derives this invariant from cold startup and all actual queries; no protocol-security or desired-frontend equality premise is introduced. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3KeyServiceProjection
open RegistrationNativeG3KeyService (Spec State Valid direct stacked)
open RegistrationNativeRelatedFamily (Message)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
variable {Value : Type}
attribute [local irreducible] PqxdhServerAuthKeySchedule.fromRoot

private theorem valid_some (input : Message → Option Pqxdh.Bytes) (before : State) (valid : Valid input before)
    (message : Message) (bytes : Pqxdh.Bytes) (realized : input message = some bytes) :
    Valid input (Function.update before.1 message true,
      { before.2 with prepared := Function.update before.2.prepared bytes true, prepares := before.2.prepares + 1, roots := before.2.roots + 1 }) := by
  intro current active
  by_cases same : current = message
  · subst current
    exact ⟨bytes, realized, Function.update_self _ _ _⟩
  · have previous : before.1 current = true := by simpa only [Function.update_of_ne same] using active
    obtain ⟨oldBytes, oldInput, oldPrepared⟩ := valid current previous
    refine ⟨oldBytes, oldInput, ?_⟩
    by_cases sameBytes : oldBytes = bytes
    · subst oldBytes
      exact Function.update_self _ _ _
    · exact (Function.update_of_ne sameBytes _ _).trans oldPrepared

private theorem valid_none (input : Message → Option Pqxdh.Bytes) (before : State) (valid : Valid input before) (message : Message) :
    Valid input (Function.update before.1 message false, { before.2 with prepares := before.2.prepares + 1 }) := by
  intro current active
  by_cases same : current = message
  · subst current
    simp only [Function.update_self] at active
    cases active
  · exact valid current (by simpa only [Function.update_of_ne same] using active)

/-- Every actual stacked query preserves its derived successful-descriptor/prepared-input invariant. -/
theorem query_valid (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (query : Spec.Domain) (before : State) (result : Spec.Range query × State) (valid : Valid input before)
    (supported : result ∈ support ((stacked source input inside query).run before)) : Valid input result.2 := by
  cases query with
  | inl coin =>
      rw [RegistrationNativeG3KeyService.coin, support_map] at supported
      obtain ⟨reply, _possible, equal⟩ := supported
      cases equal
      exact valid
  | inr query => cases query with
    | prepare message =>
        cases realized : input message with
        | none =>
            rw [RegistrationNativeG3KeyService.prepare_none source input inside message realized before, mem_support_pure_iff] at supported
            cases supported
            exact valid_none input before valid message
        | some bytes =>
            rw [RegistrationNativeG3KeyService.prepare_some source input inside message bytes realized before, mem_support_pure_iff] at supported
            cases supported
            exact valid_some input before valid message bytes realized
    | demand message =>
        by_cases prepared : before.1 message = true
        · obtain ⟨bytes, realized, inner⟩ := valid message prepared
          cases protectedInput : inside bytes with
          | false =>
              rw [RegistrationNativeG3KeyService.demand_known source input inside message bytes before prepared realized inner protectedInput,
                mem_support_pure_iff] at supported
              cases supported
              exact valid
          | true =>
              rw [RegistrationNativeG3KeyService.demand_hidden source input inside message bytes before prepared realized inner protectedInput,
                support_map] at supported
              obtain ⟨output, _possible, equal⟩ := supported
              cases equal
              exact valid
        · have missing : before.1 message = false := Bool.eq_false_iff.mpr prepared
          rw [RegistrationNativeG3KeyService.demand_unprepared source input inside message before missing, mem_support_pure_iff] at supported
          cases supported
          exact valid

/-- Dropping only private metadata yields the exact direct-service reply and complete descriptor flags for every actual query. -/
theorem query_source (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (query : Spec.Domain) (before : State) (valid : Valid input before) :
    Prod.map id Prod.fst <$> (stacked source input inside query).run before = (direct source input inside query).run before.1 := by
  cases query with
  | inl coin =>
      rw [RegistrationNativeG3KeyService.coin]
      simp only [direct, StateT.run_lift, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]
      rfl
  | inr query => cases query with
    | prepare message =>
        cases realized : input message with
        | none =>
            rw [RegistrationNativeG3KeyService.prepare_none source input inside message realized before, map_pure]
            simp only [direct, StateT.run, realized, Option.map_none]
            rfl
        | some bytes =>
            rw [RegistrationNativeG3KeyService.prepare_some source input inside message bytes realized before, map_pure]
            simp only [direct, StateT.run, realized, Option.map_some, Option.isSome_some]
            rfl
    | demand message =>
        by_cases prepared : before.1 message = true
        · obtain ⟨bytes, realized, inner⟩ := valid message prepared
          cases protectedInput : inside bytes with
          | false =>
              rw [RegistrationNativeG3KeyService.demand_known source input inside message bytes before prepared realized inner protectedInput, map_pure]
              simp only [direct, StateT.run, prepared, ite_true, realized, protectedInput, Bool.false_eq_true, ite_false]
              rfl
          | true =>
              rw [RegistrationNativeG3KeyService.demand_hidden source input inside message bytes before prepared realized inner protectedInput]
              simp only [direct, StateT.run, prepared, ite_true, realized, protectedInput, Functor.map_map, Prod.map_def, id_eq]
              rfl
        · have missing : before.1 message = false := Bool.eq_false_iff.mpr prepared
          rw [RegistrationNativeG3KeyService.demand_unprepared source input inside message before missing, map_pure]
          simp only [direct, StateT.run, missing, Bool.false_eq_true, ite_false]
          rfl



/-- The full adaptive key-service stack has the same source value and descriptor flags as the direct uniform108-byte service. -/
theorem program_source (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp Spec Value) (before : State) (valid : Valid input before) :
    Prod.map id Prod.fst <$> (simulateQ (stacked source input inside) work).run before =
      (simulateQ (direct source input inside) work).run before.1 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [← query_source source input inside query before valid, bind_map_left]
      apply bind_congr_of_forall_mem_support
      intro reached possible
      exact ih reached.1 reached.2 (query_valid source input inside query before reached valid possible)

end BeaconcryptCore.Computational.RegistrationNativeG3KeyServiceProjection
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KeyServiceProjection.query_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KeyServiceProjection.query_valid
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KeyServiceProjection.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KeyServiceProjection.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KeyServiceProjection.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KeyServiceProjection.program_source
