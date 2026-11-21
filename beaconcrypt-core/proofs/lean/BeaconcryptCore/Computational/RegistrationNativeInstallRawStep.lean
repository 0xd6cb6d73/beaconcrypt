-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallTypedEntry

/-! Actual raw decoding transports the typed suffix receipts without changing public handle ordinals. Invalid parses are literal pure rejections; failed typed callbacks keep their complete reached state and contribute no successful handle. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallRawStep
open RegistrationNativeRawAdapter (TypedSpec adapter handler)
open RegistrationNativeInstallOrdinals (handles)
open RegistrationNativeInstallStep (RoleStep)
open RegistrationNativeInstallTypedEntry (entry change_entry)
variable {n : Nat} {NativeState : Type}
variable (typed : QueryImpl TypedSpec (StateT NativeState ProbComp)) (wire : RegistrationNativeWire.Wire)
    (events : NativeState → List RegistrationNativeG2Trace.Event)
    (slots : NativeState → PqxdhDeploymentInterface.Handle → Option (PqxdhRecordLiftInterface.Slot n))
    (valid : NativeState → Prop) (selected : RegistrationNativeRelatedFamily.Message → Prop)
    (step : ∀ query before result, valid before → result ∈ support ((typed query).run before) →
      ∀ role, RoleStep role (events before) (events result.2) (entry query result.1) (slots result.2) selected)

include step
private theorem mapped (query : RegistrationNativeInterface.Spec.Domain) (request : TypedSpec.Domain)
    (observe : TypedSpec.Range request → RegistrationNativeInterface.Spec.Range query)
    (source : adapter wire query = observe <$> (TypedSpec.query request : OracleComp TypedSpec _))
    (same : ∀ reply role, handles role [entry request reply] = handles role [⟨.inl query, observe reply⟩])
    (before : NativeState) (result : RegistrationNativeInterface.Spec.Range query × NativeState)
    (prior : valid before) (supported : result ∈ support ((handler wire typed query).run before))
    (role : PqxdhRecordLiftInterface.Role) :
    RoleStep role (events before) (events result.2) ⟨.inl query, result.1⟩ (slots result.2) selected := by
  rw [handler, QueryImpl.apply_compose, source, simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
  obtain ⟨actual, called, rfl⟩ := supported
  exact change_entry role _ _ _ _ _ _ (same actual.1 role) (step request before actual prior called role)

omit step in
private theorem rejected (query : RegistrationNativeInterface.Spec.Domain)
    (reply : RegistrationNativeInterface.Spec.Range query) (source : adapter wire query = pure reply)
    (empty : ∀ role, handles role [⟨.inl query, reply⟩] = [])
    (before : NativeState) (result : RegistrationNativeInterface.Spec.Range query × NativeState)
    (supported : result ∈ support ((handler wire typed query).run before)) (role : PqxdhRecordLiftInterface.Role) :
    RoleStep role (events before) (events result.2) ⟨.inl query, result.1⟩ (slots result.2) selected := by
  rw [handler, QueryImpl.apply_compose, source, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  exact RegistrationNativeInstallStep.of_quiet role _ _ _ _ _ rfl (empty role)

/-- Every actual raw native callback carries the typed successful installation receipt for its original query and reply. -/
theorem raw (query : RegistrationNativeInterface.Spec.Domain) (before : NativeState)
    (result : RegistrationNativeInterface.Spec.Range query × NativeState)
    (prior : valid before) (supported : result ∈ support ((handler wire typed query).run before))
    (role : PqxdhRecordLiftInterface.Role) :
    RoleStep role (events before) (events result.2) ⟨.inl query, result.1⟩ (slots result.2) selected := by
  cases query with
  | inl coin =>
      exact mapped typed wire events slots valid selected step _ (.inl coin) id rfl
        (fun reply role => by cases role <;> rfl) before result prior supported role
  | inr command => cases command with
    | create edPin mlPin keyId =>
        cases ed : PqxdhDeploymentInterface.parsePin edPin with
        | none =>
            exact rejected typed wire events slots selected (.inr (.create edPin mlPin keyId)) none (by simp only [adapter, ed])
              (fun role => by cases role <;> rfl) before result supported role
        | some edParsed => cases ml : RegistrationNativeWire.parseMldsaPin mlPin with
          | none =>
              exact rejected typed wire events slots selected (.inr (.create edPin mlPin keyId)) none (by simp only [adapter, ed, ml])
                (fun role => by cases role <;> rfl) before result supported role
          | some mlParsed =>
              exact mapped typed wire events slots valid selected step _ (.inr (.create edParsed mlParsed keyId))
                RegistrationNativeRawAdapter.resultOption (by simp only [adapter, ed, ml])
                (fun reply role => by cases role <;> rfl) before result prior supported role
    | accept raw =>
        cases parsed : RegistrationNativeWire.readInit wire raw with
        | none =>
            exact rejected typed wire events slots selected (.inr (.accept raw)) none (by simp only [adapter, parsed])
              (fun role => by cases role <;> rfl) before result supported role
        | some packet =>
            exact mapped typed wire events slots valid selected step _ (.inr (.accept packet))
              RegistrationNativeRawAdapter.resultOption (by simp only [adapter, parsed])
              (fun reply role => by cases role <;> rfl) before result prior supported role
    | bundle owner =>
        exact mapped typed wire events slots valid selected step _ (.inr (.bundle owner))
          RegistrationNativeRawAdapter.resultOption rfl (fun reply role => by cases role <;> rfl) before result prior supported role
    | build handle payload =>
        exact mapped typed wire events slots valid selected step _ (.inr (.build handle (RegistrationNativeRawAdapter.application payload)))
          RegistrationNativeRawAdapter.responseOption rfl (fun reply role => by
            cases role <;> cases reply with
            | fail _ => rfl
            | div => rfl
            | ok answer => cases answer <;> rfl) before result prior supported role
    | finish owner raw =>
        exact mapped typed wire events slots valid selected step _ (.inr (.finish owner (RegistrationNativeWire.readResponse wire raw)))
          RegistrationNativeRawAdapter.resultOption rfl (fun reply role => by
            cases role <;> cases reply with
            | fail _ => rfl
            | div => rfl
            | ok answer => cases answer <;> rfl) before result prior supported role
    | hmac key message =>
        exact mapped typed wire events slots valid selected step _ (.inr (.hmac key message)) id rfl
          (fun reply role => by cases role <;> rfl) before result prior supported role
    | hash bytes =>
        exact mapped typed wire events slots valid selected step _ (.inr (.hash bytes)) id rfl
          (fun reply role => by cases role <;> rfl) before result prior supported role
    | serverSend keyId plaintext =>
        exact mapped typed wire events slots valid selected step _ (.inr (.serverSend keyId plaintext)) id rfl
          (fun reply role => by cases role <;> rfl) before result prior supported role
    | serverRaw raw =>
        exact mapped typed wire events slots valid selected step _ (.inr (.serverRaw raw)) id rfl
          (fun reply role => by cases role <;> rfl) before result prior supported role
    | beaconSend owner plaintext =>
        exact mapped typed wire events slots valid selected step _ (.inr (.beaconSend owner plaintext)) id rfl
          (fun reply role => by cases role <;> rfl) before result prior supported role
    | beaconRaw owner raw =>
        exact mapped typed wire events slots valid selected step _ (.inr (.beaconRaw owner raw)) id rfl
          (fun reply role => by cases role <;> rfl) before result prior supported role

end BeaconcryptCore.Computational.RegistrationNativeInstallRawStep
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallRawStep.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallRawStep.raw
