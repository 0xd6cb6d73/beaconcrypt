-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerRoster
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCore

/-! The selected local owner's remaining lifecycle credit is one until terminal consumption, including before its future birth. Actual creation and bundle cannot revive consumed positions, and finish consumes before optional packet admission. The credit tracks a local role only; its KEM handle remains a separate retained source field. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerCredit
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicFrontend (State M handler)
open RegistrationNativeSecretWordLifecycleOwnerPhase (Terminal Done)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def canFinish : RegistrationNativeBeaconFrontend.Phase → Bool
  | .initSent pending _ => match pending.aborted_state with
      | .ok _ => true
      | _ => false
  | _ => false

def credit (selected : Nat) (before : State source) : Nat :=
  match before.beacons[selected]? with
  | none => 1
  | some owner => if Terminal owner.view.phase then 0 else 1

def cost (selected : Nat) : RegistrationNativeRawAdapter.TypedSpec.Domain → State source → Nat
  | .inr (.finish index _), before => if index = selected then
      match before.beacons[index]? with
      | none => 0
      | some owner => if canFinish owner.view.phase then 1 else 0
    else 0
  | _, _ => 0

/-- Actual terminal ownership is exactly the exhaustion of this local role credit. -/
theorem credit_zero (selected : Nat) (before : State source) : credit selected before = 0 ↔ Done selected before.beacons := by
  cases found : before.beacons[selected]? with
  | none => simp [credit, Done, found]
  | some owner =>
      by_cases terminal : Terminal owner.view.phase <;> simp [credit, Done, found, terminal]

/-- A selected role has one remaining attempt at most, including before its owner has been created. -/
theorem credit_le (selected : Nat) (before : State source) : credit selected before ≤ 1 := by
  unfold credit
  split
  · exact Nat.le_refl _
  · split <;> omega

private theorem server_done (selected : Nat) (routeSelected : Bool) (work : RegistrationServerOpenReferenceCompiler.M n KemSK Value)
    (before : State source) (result : Value × State source) (valid : Done selected before.beacons)
    (supported : result ∈ support ((RegistrationNativePublicFrontend.serverOpen routeSelected work).run before)) :
    Done selected result.2.beacons := by
  simp only [RegistrationNativePublicFrontend.serverOpen, StateT.run, support_map] at supported
  obtain ⟨middle, _stepped, equal⟩ := supported
  cases equal
  exact valid

private theorem beacon_done (selected : Nat)
    (work : RegistrationNativePublicOwners.M n KemSK RegistrationServerRoleBackend.State source Value)
    (keeps : ∀ owners env result, Done selected owners → result ∈ support ((work.run owners).run env) → Done selected result.1.2)
    (before : State source) (result : Value × State source) (valid : Done selected before.beacons)
    (supported : result ∈ support ((RegistrationNativePublicFrontend.beacon work).run before)) :
    Done selected result.2.beacons := by
  simp only [RegistrationNativePublicFrontend.beacon, StateT.run, support_map] at supported
  obtain ⟨middle, stepped, equal⟩ := supported
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ stepped
  cases equal
  exact keeps before.beacons before.environment middle valid original

private theorem lifted_done (selected : Nat) (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State source) (result : Value × State source) (valid : Done selected before.beacons)
    (supported : result ∈ support ((StateT.lift work : M n KemSK source Value).run before)) :
    Done selected result.2.beacons := by
  simp only [StateT.run_lift, bind_pure_comp, support_map] at supported
  obtain ⟨reply, _stepped, equal⟩ := supported
  cases equal
  exact valid

private theorem record_done (selected : Nat) (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State source) (valid : Done selected before.beacons)
    (supported : result ∈ support ((RegistrationNativePublicFrontend.record (n := n) (KemSK := KemSK) query).run before)) :
    Done selected result.2.beacons := by
  rcases query with query | ⟨index, query⟩
  · simp only [RegistrationNativePublicFrontend.record, StateT.run, support_map] at supported
    obtain ⟨reply, _stepped, equal⟩ := supported
    cases equal
    exact valid
  · cases query <;> cases found : before.beacons[index]? with
    | none =>
        simp only [RegistrationNativePublicFrontend.record, StateT.run, found, mem_support_pure_iff] at supported
        cases supported
        exact valid
    | some owner =>
        simp only [RegistrationNativePublicFrontend.record, StateT.run, found, support_map] at supported
        obtain ⟨reply, _stepped, equal⟩ := supported
        cases equal
        exact valid

attribute [local irreducible] RegistrationServerOpenReferenceCompiler.accept RegistrationServerOpenReferenceCompiler.build

/-- Every actual typed operation preserves a previously consumed selected-owner position; no future creation or bundle revives it. -/
theorem query_done (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source) (valid : Done selectedOwner before.beacons)
    (supported : result ∈ support
      ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before)) :
    Done selectedOwner result.2.beacons := by
  cases query with
  | inl coin => exact lifted_done _ _ before result valid supported
  | inr query => cases query with
    | create edPin mlPin keyId =>
        exact beacon_done selectedOwner _
          (fun owners env result valid supported => RegistrationNativeSecretWordLifecycleOwnerRoster.create_done
            setup selectedOwner selectedOwner publicPrekey edPin mlPin keyId owners env result valid supported)
          before result valid supported
    | bundle index =>
        exact beacon_done selectedOwner _
          (fun owners env result valid supported => RegistrationNativeSecretWordLifecycleOwnerRoster.bundle_done
            setup wire selectedOwner selectedOwner index publicPrekey owners env result valid supported)
          before result valid supported
    | finish index packet =>
        exact beacon_done selectedOwner _
          (fun owners env result valid supported => RegistrationNativeSecretWordLifecycleOwnerRoster.finish_done
            setup selectedOwner index packet owners env result valid supported)
          before result valid supported
    | accept packet =>
        simp only [handler, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_modify] at supported
        exact server_done selectedOwner _ _ { before with parsedAccepts := before.parsedAccepts + 1 } result valid supported
    | build handle application => exact server_done selectedOwner false _ before result valid supported
    | hmac key bytes =>
        simp only [handler, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        exact valid
    | hash bytes => exact lifted_done _ _ before result valid supported
    | serverSend keyId plaintext => exact record_done selectedOwner (.inl (.inl (plaintext, keyId))) before result valid supported
    | serverRaw bytes => exact record_done selectedOwner (.inl (.inr bytes)) before result valid supported
    | beaconSend index plaintext => exact record_done selectedOwner (.inr (index, .inl plaintext)) before result valid supported
    | beaconRaw index bytes => exact record_done selectedOwner (.inr (index, .inr bytes)) before result valid supported

private theorem cost_le (selected : Nat) (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source) :
    cost selected query before ≤ 1 := by
  cases query with
  | inl coin => exact Nat.zero_le _
  | inr query =>
      cases query <;> simp only [cost]
      all_goals repeat first | omega | split

/-- Spending this role credit witnesses the actual selected local lookup and successful native terminal-move gate. -/
theorem spent (selected : Nat) (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source)
    (charged : cost selected query before = 1) :
    ∃ packet owner pending oneTime aborted,
      query = .inr (.finish selected packet) ∧ before.beacons[selected]? = some owner ∧
      owner.view.phase = .initSent pending oneTime ∧ pending.aborted_state = .ok aborted := by
  cases query with
  | inl coin => cases charged
  | inr query =>
      cases query <;> try cases charged
      case finish index packet =>
        by_cases same : index = selected
        · subst index
          cases found : before.beacons[selected]? with
          | none => simp only [cost, ite_true, found] at charged; cases charged
          | some owner =>
              cases phase : owner.view.phase with
              | fresh | freshWithCoins _ | established _ | aborted _ =>
                  simp only [cost, ite_true, found, canFinish, phase, Bool.false_eq_true, ite_false] at charged
                  cases charged
              | initSent pending oneTime =>
                  simp only [cost, ite_true, found, canFinish, phase] at charged
                  cases moved : pending.aborted_state with
                  | fail error | div => simp only [moved, Bool.false_eq_true, ite_false] at charged; cases charged
                  | ok aborted => exact ⟨packet, owner, pending, oneTime, aborted, rfl, rfl, phase, moved⟩
        · simp only [cost, same, ite_false] at charged
          cases charged

/-- The literal actual frontend step that spends the selected role credit leaves that position terminal on every result. -/
theorem query_spent (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source)
    (charged : cost selectedOwner query before = 1)
    (supported : result ∈ support
      ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before)) :
    Done selectedOwner result.2.beacons := by
  obtain ⟨packet, owner, pending, oneTime, aborted, selected, found, sent, moved⟩ := spent selectedOwner query before charged
  subst query
  simp only [handler, RegistrationNativePublicFrontend.beacon, StateT.run, support_map] at supported
  obtain ⟨middle, stepped, equal⟩ := supported
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ stepped
  cases equal
  exact RegistrationNativeSecretWordLifecycleOwnerRoster.finish_consumes setup selectedOwner packet before.beacons
    before.environment owner found pending oneTime aborted sent moved middle original

/-- Actual selected-owner terminal consumption pays for the sole possible decapsulation attempt across all later commands. -/
theorem query_credit (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source)
    (supported : result ∈ support
      ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before)) :
    credit selectedOwner result.2 + cost selectedOwner query before ≤ credit selectedOwner before := by
  by_cases charged : cost selectedOwner query before = 1
  · have afterDone := query_spent setup checks wire sign selectedOwner selectedAccept publicPrekey query before result charged supported
    have afterZero := (credit_zero selectedOwner result.2).mpr afterDone
    obtain ⟨packet, owner, pending, oneTime, aborted, _selected, found, sent, _moved⟩ := spent selectedOwner query before charged
    have beforeOne : credit selectedOwner before = 1 := by simp only [credit, found, sent, Terminal, ite_false]
    omega
  · have costZero : cost selectedOwner query before = 0 := by have small := cost_le selectedOwner query before; omega
    by_cases beforeZero : credit selectedOwner before = 0
    · have beforeDone := (credit_zero selectedOwner before).mp beforeZero
      have afterDone := query_done setup checks wire sign selectedOwner selectedAccept publicPrekey query before result beforeDone supported
      have afterZero := (credit_zero selectedOwner result.2).mpr afterDone
      omega
    · have beforeSmall := credit_le selectedOwner before
      have afterSmall := credit_le selectedOwner result.2
      omega

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerCredit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerCredit.credit_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerCredit.credit_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerCredit.credit_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerCredit.credit_le
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerCredit.query_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerCredit.query_done

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerCredit.spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerCredit.spent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerCredit.query_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerCredit.query_spent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerCredit.query_credit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerCredit.query_credit
