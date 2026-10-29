-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinSource

/-! Original raw constructor parsing and every failed native reply implement precisely the public configured-pin summary update under the actual Word source. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinRaw
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeSecretWordOwnerPins (key)
open RegistrationNativeOwnerPinSummaryStep (advance)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
local notation "typedImpl" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
local notation "rawImpl" => RegistrationNativeRawAdapter.handler wire typedImpl

/-- Every original raw program without construction retains all immutable configured owner pins. -/
theorem quiet (work : OracleComp RegistrationNativeInterface.Spec Value)
    (bounded : work.IsQueryBoundP (fun query => RegistrationNativeLedgerCaps.coreKind query = 1) 0)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((simulateQ rawImpl work).run before)) : result.2.1.beacons.map key = before.1.beacons.map key := by
  rw [RegistrationNativeRawAdapter.program_native] at supported
  exact RegistrationNativeSecretWordOwnerPinSource.typed_quiet setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
    _ (RegistrationNativeRawAdapter.compile_bound wire work 1 0 bounded) before result supported

/-- Successful raw construction appends its same parsed configured pin; every malformed or rejected creation appends nothing. -/
theorem create (edPin mlPin : Pqxdh.Bytes) (keyId : U64) (before : State n KemSK source)
    (reply : Option Nat) (after : State n KemSK source)
    (supported : (reply, after) ∈ support ((rawImpl (.inr (.create edPin mlPin keyId))).run before)) :
    after.1.beacons.map key = advance (before.1.beacons.map key) (.inr (.create edPin mlPin keyId)) reply := by
  simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter] at supported
  cases parsed : PqxdhDeploymentInterface.parsePin edPin with
  | none =>
      simp only [parsed, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | some word =>
      cases parsedMl : RegistrationNativeWire.parseMldsaPin mlPin with
      | none =>
          simp only [parsed, parsedMl, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
          cases supported
          rfl
      | some publicKey =>
          simp only [parsed, parsedMl, simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
          obtain ⟨⟨answer, current⟩, reached, equal⟩ := supported
          have actual := RegistrationNativeSecretWordOwnerPinSource.typed_create setup checks wire route sign input inside provider outer
            selectedOwner selectedAccept publicPrekey word publicKey keyId before answer current reached
          cases answer with
          | fail error | div =>
              simp only [RegistrationNativeRawAdapter.resultOption, Prod.mk.injEq] at equal
              obtain ⟨rfl, rfl⟩ := equal
              exact actual
          | ok chosen =>
              simp only [RegistrationNativeRawAdapter.resultOption, Prod.mk.injEq] at equal
              obtain ⟨rfl, rfl⟩ := equal
              cases chosen <;> simpa only [advance, parsed] using actual

/-- Every original raw callback implements the literal public configured-pin summary update. -/
theorem step (query : RegistrationNativeInterface.Spec.Domain) (before : State n KemSK source)
    (reply : RegistrationNativeInterface.Spec.Range query) (after : State n KemSK source)
    (supported : (reply, after) ∈ support ((rawImpl query).run before)) :
    after.1.beacons.map key = advance (before.1.beacons.map key) query reply := by
  by_cases counted : RegistrationNativeLedgerCaps.coreKind query = 1
  · cases query with
    | inl coin => cases counted
    | inr command => cases command with
      | create edPin mlPin keyId => exact create setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey edPin mlPin keyId before reply after supported
      | _ => cases counted
  · have bounded : OracleComp.IsQueryBoundP (RegistrationNativeInterface.Spec.query query : OracleComp RegistrationNativeInterface.Spec _)
        (fun request => RegistrationNativeLedgerCaps.coreKind request = 1) 0 := by
      rw [isQueryBoundP_query_iff]
      intro contrary
      exact False.elim (counted contrary)
    have preserved := quiet setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
      (RegistrationNativeInterface.Spec.query query : OracleComp RegistrationNativeInterface.Spec _) bounded before (reply, after)
      (by simpa only [simulateQ_spec_query] using supported)
    cases query with
    | inl coin => exact preserved
    | inr command => cases command <;> first
      | exact (counted rfl).elim
      | exact preserved
end BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinRaw
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinRaw.quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinRaw.quiet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinRaw.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinRaw.create
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinRaw.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinRaw.step
