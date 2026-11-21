-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOwnerPinBirth
import BeaconcryptCore.Computational.RegistrationNativeOwnerRoster
import BeaconcryptCore.Computational.RegistrationNativeParsedCounterLedger

/-! Successful original raw create entries retain their literal configured Server binding in the final owner roster. Later creation, signatures, failed publication and terminal finish preserve that immutable pin. The trace neither identifies an owner with an accepted Ed identity nor assumes that its creation preceded any selected accept. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOwnerPinTrace
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeExperiment (State)
open RegistrationNativeInterface (Entry)
open RegistrationNativeWire (Wire)
open RegistrationNativeOwnerFields (metadata)
open RegistrationNativeParsedCounterLedger (native)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationNativeExperiment.handler

def creation : Entry → Option (Nat × PqxdhBeaconPhase2Preparation.Word32 × U64)
  | ⟨.inl (.inr (.create edPin _ keyId)), some index⟩ =>
      (PqxdhDeploymentInterface.parsePin edPin).map fun word => (index, word, keyId)
  | _ => none

def Holds (transcript : List Entry) (owners : RegistrationNativeBeaconFrontend.State source) : Prop :=
  ∀ entry ∈ transcript, ∀ index pin keyId, creation entry = some (index, pin, keyId) →
    ∃ owner, owners[index]? = some owner ∧ owner.pin.binding = ⟨pin, keyId⟩

private theorem transport (transcript : List Entry) (before after : RegistrationNativeBeaconFrontend.State source)
    (prior : Holds transcript before) (preserved : RegistrationNativeOwnerRoster.Prefix before after) : Holds transcript after := by
  intro entry member index pin keyId created
  obtain ⟨old, found, binding⟩ := prior entry member index pin keyId created
  obtain ⟨current, currentAt, same⟩ := RegistrationNativeOwnerRoster.lookup before after preserved index old found
  have pinned : current.pin = old.pin := congrArg (fun owner => owner.pin) same
  exact ⟨current, currentAt, pinned ▸ binding⟩

/-- The same actual source KEM/World callbacks retain the literal pin in the owner appended by a successful native create. -/
theorem source_create (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (index : Nat) (before after : State n KemSK source)
    (supported : (.ok (some index), after) ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)).run before)) :
    ∃ owner, after.beacons[index]? = some owner ∧ owner.pin.binding = ⟨edPin, keyId⟩ ∧ owner.pin.public_key = mlPin := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, mem_support_bind_iff,
    mem_support_pure_iff] at supported
  obtain ⟨⟨⟨⟨value, ownersAfter⟩, envAfter⟩, sourceAfter⟩, interpreted, returned⟩ := supported
  have valueEq : value = .ok (some index) := congrArg Prod.fst returned.symm
  subst value
  have original : ((.ok (some index), ownersAfter), envAfter) ∈ support
      (((RegistrationNativeBeaconFrontend.create (n := n) setup source edPin mlPin keyId).run before.beacons).run
        (RegistrationWorldAgreementCompiler.erase before.server.world)) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeExperiment.trusted setup checks representation created source) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst interpreted
  have owners : after.beacons = ownersAfter := congrArg (fun result => result.2.beacons) returned
  rw [owners]
  exact RegistrationNativeOwnerPinBirth.create_pin setup source edPin mlPin keyId before.beacons _ index ownersAfter envAfter original

/-- Raw create parsing preserves the exact configured classical pin, independent of the generated owner identity. -/
theorem raw_create (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (edPin mlPin : Pqxdh.Bytes) (keyId : U64) (word : PqxdhBeaconPhase2Preparation.Word32)
    (parsed : PqxdhDeploymentInterface.parsePin edPin = some word) (index : Nat)
    (before after : State n KemSK source)
    (supported : (some index, after) ∈ support ((native setup checks wire route representation created credential
      (.inr (.create edPin mlPin keyId))).run before)) :
    ∃ owner, after.beacons[index]? = some owner ∧ owner.pin.binding = ⟨word, keyId⟩ := by
  simp only [native, RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
    RegistrationNativeRawAdapter.adapter, parsed] at supported
  cases parsedMl : RegistrationNativeWire.parseMldsaPin mlPin with
  | none => simp only [parsedMl, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported; cases supported
  | some publicKey =>
      simp only [parsedMl, simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
      obtain ⟨⟨reply, current⟩, reached, equal⟩ := supported
      cases actual : reply with
      | fail error | div => simp [actual, RegistrationNativeRawAdapter.resultOption] at equal
      | ok reply =>
          simp only [actual, RegistrationNativeRawAdapter.resultOption, Prod.mk.injEq] at equal
          obtain ⟨rfl, rfl⟩ := equal
          obtain ⟨owner, found, binding, _⟩ := source_create setup checks representation created word publicKey keyId index before current
            (by simpa only [actual, RegistrationNativeExperiment.handler] using reached)
          exact ⟨owner, found, binding⟩

/-- Every original secrecy-ledger step preserves all earlier create-pin receipts and adds its actual successful raw constructor receipt. -/
theorem step_keeps (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK source) (prior : Holds before.1.transcript before.2.beacons)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire
      created.server.server.metadata.sender bounds
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) query).run before)) :
    Holds result.2.1.transcript result.2.2.beacons := by
  have preserved := RegistrationNativeOwnerRoster.full_step_prefix setup checks wire route representation created credential bounds query before result supported
  have retained := transport before.1.transcript before.2.beacons result.2.2.beacons prior preserved
  have trace := RegistrationNativeParsedCounterLedger.step_trace setup checks wire route representation created credential bounds query before result supported
  intro entry member index pin keyId born
  rw [trace, List.mem_append, List.mem_singleton] at member
  rcases member with earlier | rfl
  · exact retained entry earlier index pin keyId born
  · cases query with
    | inr secrecy => cases born
    | inl query =>
        rw [RegistrationNativeParsedCounterLedger.core_run, support_map] at supported
        obtain ⟨⟨reply, after⟩, reached, equal⟩ := supported
        cases equal
        cases query with
        | inl coin => cases born
        | inr command => cases command with
          | create edPin mlPin keyId =>
              cases reply with
              | none => cases born
              | some returned =>
                  cases parsed : PqxdhDeploymentInterface.parsePin edPin with
                  | none => simp only [creation, parsed, Option.map_none, reduceCtorEq] at born
                  | some word =>
                      simp only [creation, parsed, Option.map_some, Option.some.injEq, Prod.mk.injEq] at born
                      obtain ⟨rfl, rfl, rfl⟩ := born
                      exact raw_create setup checks wire route representation created credential edPin mlPin keyId word parsed returned before.2 after reached
          | _ => cases born

/-- Full original native runs retain their configured owner pins through all later aliases and private secrecy draws. -/
theorem run_holds (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before)) :
    Holds result.2.1.transcript result.2.2.beacons := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query
    (RegistrationNativeFullCompiler.handler setup.source.crypto wire created.server.server.metadata.sender bounds
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential))
    (fun current => Holds current.1.transcript current.2.beacons)
    (fun query current valid next reached => step_keeps setup checks wire route representation created credential bounds query current valid next reached)
    _ (RegistrationNativeLedger.empty, before) _ result supported
  intro entry member
  cases member

end BeaconcryptCore.Computational.RegistrationNativeOwnerPinTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerPinTrace.source_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerPinTrace.source_create
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerPinTrace.raw_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerPinTrace.raw_create
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerPinTrace.step_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerPinTrace.step_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerPinTrace.run_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerPinTrace.run_holds
