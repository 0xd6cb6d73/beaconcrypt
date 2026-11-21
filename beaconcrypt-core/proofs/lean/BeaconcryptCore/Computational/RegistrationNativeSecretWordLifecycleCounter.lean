-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCore

/-! The actual parsed-accept ordinal advances before authentication, including every rejection, while every other frontend command retains it. Consequently a selected ordinal can fund at most one selected Server invocation over any adaptive original ledger. This proof uses the literal frontend state updates rather than a successful-session counter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCounter
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicFrontend (State M handler)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def increment : RegistrationNativeRawAdapter.TypedSpec.Domain → Nat
  | .inr (.accept _) => 1
  | _ => 0

def available (selected counter : Nat) : Nat := if counter ≤ selected then 1 else 0

def credit (selected : Nat) (before : State source) : Nat := available selected before.parsedAccepts

def cost (selected : Nat) (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source) : Nat :=
  if increment query = 1 ∧ before.parsedAccepts = selected then 1 else 0

private theorem server_counter (selected : Bool) (work : RegistrationServerOpenReferenceCompiler.M n KemSK Value)
    (before : State source) (result : Value × State source)
    (supported : result ∈ support ((RegistrationNativePublicFrontend.serverOpen selected work).run before)) :
    result.2.parsedAccepts = before.parsedAccepts := by
  simp only [RegistrationNativePublicFrontend.serverOpen, StateT.run, support_map] at supported
  obtain ⟨middle, _called, equal⟩ := supported
  cases equal
  rfl

private theorem beacon_counter
    (work : RegistrationNativePublicOwners.M n KemSK RegistrationServerRoleBackend.State source Value)
    (before : State source) (result : Value × State source)
    (supported : result ∈ support ((RegistrationNativePublicFrontend.beacon work).run before)) :
    result.2.parsedAccepts = before.parsedAccepts := by
  simp only [RegistrationNativePublicFrontend.beacon, StateT.run, support_map] at supported
  obtain ⟨middle, _called, equal⟩ := supported
  cases equal
  rfl

private theorem lifted_counter (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State source) (result : Value × State source)
    (supported : result ∈ support ((StateT.lift work : M n KemSK source Value).run before)) :
    result.2.parsedAccepts = before.parsedAccepts := by
  simp only [StateT.run_lift, bind_pure_comp, support_map] at supported
  obtain ⟨reply, _called, equal⟩ := supported
  cases equal
  rfl

private theorem record_counter (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State source)
    (supported : result ∈ support
      ((RegistrationNativePublicFrontend.record (n := n) (KemSK := KemSK) query).run before)) :
    result.2.parsedAccepts = before.parsedAccepts := by
  rcases query with query | ⟨index, query⟩
  · simp only [RegistrationNativePublicFrontend.record, StateT.run, support_map] at supported
    obtain ⟨reply, _called, equal⟩ := supported
    cases equal
    rfl
  · cases query <;> cases found : before.beacons[index]? with
    | none =>
        simp only [RegistrationNativePublicFrontend.record, StateT.run, found, mem_support_pure_iff] at supported
        cases supported
        rfl
    | some owner =>
        simp only [RegistrationNativePublicFrontend.record, StateT.run, found, support_map] at supported
        obtain ⟨reply, _called, equal⟩ := supported
        cases equal
        rfl

attribute [local irreducible] RegistrationServerOpenReferenceCompiler.accept RegistrationServerOpenReferenceCompiler.build

/-- The selected ordinal counts every actual parsed attempt before authentication and survives all other commands literally. -/
theorem query_counter (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source)
    (supported : result ∈ support
      ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before)) :
    result.2.parsedAccepts = before.parsedAccepts + increment query := by
  cases query with
  | inl coin => exact lifted_counter _ before result supported
  | inr query => cases query with
    | create edPin mlPin keyId => exact beacon_counter _ before result supported
    | bundle index => exact beacon_counter _ before result supported
    | finish index packet => exact beacon_counter _ before result supported
    | accept packet =>
        simp only [handler, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_modify] at supported
        exact server_counter (decide (before.parsedAccepts = selectedAccept)) _
          { before with parsedAccepts := before.parsedAccepts + 1 } result supported
    | build handle application => exact server_counter false _ before result supported
    | hmac key bytes =>
        simp only [handler, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        rfl
    | hash bytes => exact lifted_counter _ before result supported
    | serverSend keyId plaintext => exact record_counter (.inl (.inl (plaintext, keyId))) before result supported
    | serverRaw bytes => exact record_counter (.inl (.inr bytes)) before result supported
    | beaconSend index plaintext => exact record_counter (.inr (index, .inl plaintext)) before result supported
    | beaconRaw index bytes => exact record_counter (.inr (index, .inr bytes)) before result supported

/-- A selected parsed attempt spends the sole available ordinal credit; all other actual commands preserve or decrease that credit. -/
theorem query_credit (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source)
    (supported : result ∈ support
      ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before)) :
    credit selectedAccept result.2 + cost selectedAccept query before ≤ credit selectedAccept before := by
  have advanced := query_counter setup checks wire sign selectedOwner selectedAccept publicPrekey query before result supported
  have unit : increment query = 0 ∨ increment query = 1 := by
    cases query with
    | inl coin => exact Or.inl rfl
    | inr query => cases query <;> first | exact Or.inl rfl | exact Or.inr rfl
  simp only [credit, available, cost, advanced]
  split_ifs <;> omega

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCounter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCounter.query_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCounter.query_counter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCounter.query_credit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCounter.query_credit
