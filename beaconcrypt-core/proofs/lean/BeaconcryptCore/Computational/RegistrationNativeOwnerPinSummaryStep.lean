-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummaryCore

/-! The original raw create command appends exactly its parsed configured binding, while every failed creation and every other raw command retains the prior immutable pin list. This is a direct native source law for the transcript summary update. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummaryStep
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeExperiment (State)
open RegistrationNativeOwnerPinSummaryCore (pins)
open RegistrationNativeParsedCounterLedger (native)
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat} {source : RegistrationNativeMldsa.Source}

/-- Every actual successful constructor appends its configured binding, and failure appends nothing. -/
theorem typed_create_pins (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : PqxdhBeaconPhase2Preparation.Word32) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : State n KemSK source) (reply : RustM (Option Nat)) (after : State n KemSK source)
    (supported : (reply, after) ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)).run before)) :
    pins after.beacons = match reply with
      | .ok (some _) => pins before.beacons ++ [(edPin, keyId)]
      | _ => pins before.beacons := by
  have shape := RegistrationNativeScalarRoster.create_shape setup checks representation created edPin mlPin keyId before (reply, after) supported
  cases reply with
  | fail error | div => simpa only [RegistrationNativeKemBirthCreateShape.Shape, shape] using congrArg pins shape
  | ok reply => cases reply with
    | none => simpa only [RegistrationNativeKemBirthCreateShape.Shape, shape] using congrArg pins shape
    | some index =>
        change index = before.beacons.length ∧ ∃ owner, after.beacons = before.beacons ++ [owner] at shape
        obtain ⟨indexEq, born, roster⟩ := shape
        obtain ⟨owner, found, binding, _⟩ := RegistrationNativeOwnerPinTrace.source_create setup checks representation created edPin mlPin keyId index before after supported
        rw [roster, indexEq] at found
        simp only [List.getElem?_append, Nat.lt_irrefl, ite_false, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at found
        have bornBinding : born.pin.binding = ⟨edPin, keyId⟩ :=
          (congrArg (fun owner => owner.pin.binding) found).trans binding
        have identity := congrArg (fun value : pqxdh.ServerBinding => value.identity_public_key) bornBinding
        have assigned := congrArg (fun value : pqxdh.ServerBinding => value.identity_key_id) bornBinding
        simp only [roster, pins, List.map_append, List.map_cons, List.map_nil, identity, assigned]

def advance (before : List (PqxdhBeaconPhase2Preparation.Word32 × U64)) :
    (query : RegistrationNativeInterface.Spec.Domain) → RegistrationNativeInterface.Spec.Range query → List (PqxdhBeaconPhase2Preparation.Word32 × U64)
  | .inr (.create edPin _ keyId), some _ =>
      match PqxdhDeploymentInterface.parsePin edPin with
      | some word => before ++ [(word, keyId)]
      | none => before
  | _, _ => before

/-- The exact raw constructor preserves its parsed pin and optional native reply while updating the current pin list. -/
theorem raw_create_pins (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (edPin mlPin : Pqxdh.Bytes) (keyId : U64) (before : State n KemSK source)
    (reply : Option Nat) (after : State n KemSK source)
    (supported : (reply, after) ∈ support ((native setup checks wire route representation created credential
      (.inr (.create edPin mlPin keyId))).run before)) :
    pins after.beacons = advance (pins before.beacons) (.inr (.create edPin mlPin keyId)) reply := by
  simp only [native, RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter] at supported
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
          have actual := typed_create_pins setup checks representation created word publicKey keyId before answer current reached
          cases answer with
          | fail error | div =>
              simp only [RegistrationNativeRawAdapter.resultOption, Prod.mk.injEq] at equal
              obtain ⟨rfl, rfl⟩ := equal
              exact actual
          | ok chosen =>
              simp only [RegistrationNativeRawAdapter.resultOption, Prod.mk.injEq] at equal
              obtain ⟨rfl, rfl⟩ := equal
              cases chosen <;> simpa only [advance, parsed] using actual

private theorem noncreate_pins (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeInterface.Spec.Domain) (quiet : RegistrationNativeLedgerCaps.coreKind query ≠ 1)
    (before : State n KemSK source) (reply : RegistrationNativeInterface.Spec.Range query) (after : State n KemSK source)
    (supported : (reply, after) ∈ support ((native setup checks wire route representation created credential query).run before)) :
    pins after.beacons = pins before.beacons := by
  have bounded : OracleComp.IsQueryBoundP (RegistrationNativeInterface.Spec.query query : OracleComp RegistrationNativeInterface.Spec _)
      (fun request => RegistrationNativeLedgerCaps.coreKind request = 1) 0 := by
    rw [isQueryBoundP_query_iff]
    intro counted
    exact False.elim (quiet counted)
  apply RegistrationNativeOwnerPinSummaryCore.raw_quiet setup checks wire route representation created credential
    (RegistrationNativeInterface.Spec.query query : OracleComp RegistrationNativeInterface.Spec _) bounded before (reply, after)
  simpa only [simulateQ_spec_query] using supported

/-- Every original raw source callback implements exactly the public pin-summary update. -/
theorem raw_step (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeInterface.Spec.Domain) (before : State n KemSK source)
    (reply : RegistrationNativeInterface.Spec.Range query) (after : State n KemSK source)
    (supported : (reply, after) ∈ support ((native setup checks wire route representation created credential query).run before)) :
    pins after.beacons = advance (pins before.beacons) query reply := by
  cases query with
  | inl coin => exact noncreate_pins setup checks wire route representation created credential _ (by simp [RegistrationNativeLedgerCaps.coreKind, RegistrationNativeInterface.eraseCore, PqxdhDeploymentCompileBudget.commandKind]) before reply after supported
  | inr command => cases command with
    | create edPin mlPin keyId => exact raw_create_pins setup checks wire route representation created credential edPin mlPin keyId before reply after supported
    | bundle owner => exact noncreate_pins setup checks wire route representation created credential _ (by simp [RegistrationNativeLedgerCaps.coreKind, RegistrationNativeInterface.eraseCore, RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind]) before reply after supported
    | accept raw => exact noncreate_pins setup checks wire route representation created credential _ (by simp [RegistrationNativeLedgerCaps.coreKind, RegistrationNativeInterface.eraseCore, RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind]) before reply after supported
    | build handle payload => exact noncreate_pins setup checks wire route representation created credential _ (by simp [RegistrationNativeLedgerCaps.coreKind, RegistrationNativeInterface.eraseCore, RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind]) before reply after supported
    | finish owner raw => exact noncreate_pins setup checks wire route representation created credential _ (by simp [RegistrationNativeLedgerCaps.coreKind, RegistrationNativeInterface.eraseCore, RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind]) before reply after supported
    | hmac key message => exact noncreate_pins setup checks wire route representation created credential _ (by simp [RegistrationNativeLedgerCaps.coreKind, RegistrationNativeInterface.eraseCore, RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind]) before reply after supported
    | hash bytes => exact noncreate_pins setup checks wire route representation created credential _ (by simp [RegistrationNativeLedgerCaps.coreKind, RegistrationNativeInterface.eraseCore, RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind]) before reply after supported
    | serverSend keyId plaintext => exact noncreate_pins setup checks wire route representation created credential _ (by simp [RegistrationNativeLedgerCaps.coreKind, RegistrationNativeInterface.eraseCore, RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind]) before reply after supported
    | serverRaw raw => exact noncreate_pins setup checks wire route representation created credential _ (by simp [RegistrationNativeLedgerCaps.coreKind, RegistrationNativeInterface.eraseCore, RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind]) before reply after supported
    | beaconSend owner plaintext => exact noncreate_pins setup checks wire route representation created credential _ (by simp [RegistrationNativeLedgerCaps.coreKind, RegistrationNativeInterface.eraseCore, RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind]) before reply after supported
    | beaconRaw owner raw => exact noncreate_pins setup checks wire route representation created credential _ (by simp [RegistrationNativeLedgerCaps.coreKind, RegistrationNativeInterface.eraseCore, RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind]) before reply after supported

end BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummaryStep

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummaryStep.typed_create_pins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummaryStep.typed_create_pins
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummaryStep.raw_create_pins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummaryStep.raw_create_pins
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummaryStep.raw_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummaryStep.raw_step
