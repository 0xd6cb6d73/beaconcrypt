-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeStageTrace
import BeaconcryptCore.Computational.RegistrationNativeRawAdapter
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRawRegistrationJournal
open RegistrationNativeRawAdapter (TypedSpec resultOption responseOption)
variable {S A : Type}
inductive Mark where
  | bundle (owner : Nat) (reply : Option Pqxdh.Bytes)
  | accept (packet : registration.InitPacket) (reply : Option Nat)

def typedMark : (query : TypedSpec.Domain) → TypedSpec.Range query → Option Mark
  | .inr (.bundle owner), reply => some (.bundle owner (resultOption reply))
  | .inr (.accept packet), reply => some (.accept packet (resultOption reply))
  | _, _ => none

def rawMarks (wire : RegistrationNativeWire.Wire) :
    (query : RegistrationNativeInterface.Spec.Domain) → RegistrationNativeInterface.Spec.Range query → List Mark
  | .inr (.bundle owner), reply => [.bundle owner reply]
  | .inr (.accept bytes), reply => match RegistrationNativeWire.readInit wire bytes with
      | none => []
      | some packet => [.accept packet reply]
  | _, _ => []

noncomputable def logging (implementation : QueryImpl TypedSpec (StateT S ProbComp)) :
    QueryImpl TypedSpec (StateT (S × List Mark) ProbComp) := fun query before =>
  (fun result => (result.1, (result.2, before.2 ++ (typedMark query result.1).toList))) <$>
    (implementation query).run before.1

/-- One typed call records its exact registration observation beside the same full source poststate. -/
theorem query_log (implementation : QueryImpl TypedSpec (StateT S ProbComp)) (query : TypedSpec.Domain)
    (before : S × List Mark) (result : TypedSpec.Range query × (S × List Mark))
    (supported : result ∈ support ((logging implementation query).run before)) :
    result.2.2 = before.2 ++ (typedMark query result.1).toList := by
  simp only [logging, StateT.run, support_map] at supported
  obtain ⟨returned, _called, rfl⟩ := supported
  rfl

private theorem mapped_query (implementation : QueryImpl TypedSpec (StateT S ProbComp)) (query : TypedSpec.Domain)
    (observe : TypedSpec.Range query → A) (marks : A → List Mark)
    (normalized : ∀ answer, (typedMark query answer).toList = marks (observe answer))
    (before : S × List Mark) (result : A × (S × List Mark))
    (supported : result ∈ support ((observe <$> logging implementation query).run before)) :
    result.2.2 = before.2 ++ marks result.1 := by
  rw [StateT.run_map, support_map] at supported
  obtain ⟨returned, called, rfl⟩ := supported
  exact (query_log implementation query before returned called).trans (congrArg (before.2 ++ ·) (normalized returned.1))

/-- The actual raw parser/compiler adds precisely one decoded registration marker, retaining failed parsed accepts and every failure poststate. -/
theorem raw_step (wire : RegistrationNativeWire.Wire) (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (query : RegistrationNativeInterface.Spec.Domain) (before : S × List Mark)
    (result : RegistrationNativeInterface.Spec.Range query × (S × List Mark))
    (supported : result ∈ support ((RegistrationNativeRawAdapter.handler wire (logging implementation) query).run before)) :
    result.2.2 = before.2 ++ rawMarks wire query result.1 := by
  cases query with
  | inl coin =>
    exact query_log implementation (.inl coin) before result (by
      simpa only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
        RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] using supported)
  | inr command =>
    cases command with
    | bundle owner =>
      apply mapped_query implementation (.inr (.bundle owner)) resultOption (rawMarks wire (.inr (.bundle owner)))
        (fun _ => rfl) before result
      exact supported
    | accept bytes =>
      cases parsed : RegistrationNativeWire.readInit wire bytes with
      | none =>
        simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter,
          parsed, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        simp only [rawMarks, parsed, List.append_nil]
      | some packet =>
        apply mapped_query implementation (.inr (.accept packet)) resultOption (rawMarks wire (.inr (.accept bytes)))
          (fun _ => by simp only [typedMark, rawMarks, parsed, Option.toList_some]) before result
        simpa only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter,
          parsed, simulateQ_map, simulateQ_spec_query] using supported
    | create edPin mlPin keyId =>
      cases edParsed : PqxdhDeploymentInterface.parsePin edPin with
      | none =>
        simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
          RegistrationNativeRawAdapter.adapter, edParsed, simulateQ_pure,
          StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        simp only [rawMarks, List.append_nil]
      | some concreteEd =>
        cases mlParsed : RegistrationNativeWire.parseMldsaPin mlPin with
        | none =>
          simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, edParsed, mlParsed, simulateQ_pure,
            StateT.run_pure, mem_support_pure_iff] at supported
          cases supported
          simp only [rawMarks, List.append_nil]
        | some concreteMl =>
          apply mapped_query implementation (.inr (.create concreteEd concreteMl keyId))
            resultOption (fun _ => []) (fun _ => rfl) before result
          simpa only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
            RegistrationNativeRawAdapter.adapter, edParsed, mlParsed,
            simulateQ_map, simulateQ_spec_query] using supported
    | build session application =>
      apply mapped_query implementation (.inr (.build session (RegistrationNativeRawAdapter.application application))) responseOption
        (fun _ => []) (fun _ => rfl) before result
      exact supported
    | finish owner bytes =>
      apply mapped_query implementation (.inr (.finish owner (RegistrationNativeWire.readResponse wire bytes))) resultOption
        (fun _ => []) (fun _ => rfl) before result
      exact supported
    | hmac key message => exact query_log implementation (.inr (.hmac key message)) before result (by
        simpa only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
          RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] using supported)
    | hash bytes => exact query_log implementation (.inr (.hash bytes)) before result (by
        simpa only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
          RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] using supported)
    | serverSend keyId plaintext => exact query_log implementation (.inr (.serverSend keyId plaintext)) before result (by
        simpa only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
          RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] using supported)
    | serverRaw bytes => exact query_log implementation (.inr (.serverRaw bytes)) before result (by
        simpa only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
          RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] using supported)
    | beaconSend owner plaintext => exact query_log implementation (.inr (.beaconSend owner plaintext)) before result (by
        simpa only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
          RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] using supported)
    | beaconRaw owner bytes => exact query_log implementation (.inr (.beaconRaw owner bytes)) before result (by
        simpa only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
          RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] using supported)
end BeaconcryptCore.Computational.RegistrationNativeRawRegistrationJournal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRawRegistrationJournal.query_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRawRegistrationJournal.query_log
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRawRegistrationJournal.raw_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRawRegistrationJournal.raw_step
