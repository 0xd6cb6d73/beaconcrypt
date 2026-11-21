-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRosterRun

/-! Every actual original-ledger bundle in the concrete symbolic source retains its original signed PQ payload and current owner. The provenance survives arbitrary later constructors, terminal incoming operations and random material answers. Native bounded encoder readback is the only representation premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublicationRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeInterface (Entry)
open RegistrationNativeWire (Wire)
open RegistrationNativeSecretWordTargetLedger (native)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {source : RegistrationNativeMldsa.Source}
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
local notation "typed" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
attribute [local irreducible] RegistrationNativeSecretWordTargetSource.typed

def publication : Entry → Option (Nat × Pqxdh.Bytes)
  | ⟨.inl (.inr (.bundle owner)), some raw⟩ => some (owner, raw)
  | _ => none

def Holds (wire : Wire) (transcript : List Entry) (owners : RegistrationNativePublicOwners.State source) : Prop :=
  ∀ entry ∈ transcript, ∀ owner raw, publication entry = some (owner, raw) →
    ∃ selected packet, owners[owner]? = some selected ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      RegistrationNativeKemTarget.PacketKey packet selected.view.kemPublic

private theorem transport (wire : Wire) (transcript : List Entry)
    (before after : RegistrationNativePublicOwners.State source)
    (prior : Holds wire transcript before) (preserved : RegistrationNativeSecretWordTargetRoster.Prefix before after) :
    Holds wire transcript after := by
  intro entry member owner raw published
  obtain ⟨old, packet, found, parsed, key⟩ := prior entry member owner raw published
  obtain ⟨current, currentAt, same⟩ := RegistrationNativeSecretWordTargetRoster.lookup before after preserved owner old found
  have publicKey : current.view.kemPublic = old.view.kemPublic := congrArg Prod.snd same
  exact ⟨current, packet, currentAt, parsed, by simpa only [publicKey] using key⟩

/-- A successful original raw bundle has the actual earlier symbolic owner and its decoded signed PQ payload. -/
theorem raw_bundle (readback : RegistrationNativeWire.InitReadBack wire) (index : Nat) (raw : Pqxdh.Bytes)
    (before after : State n KemSK source)
    (supported : (some raw, after) ∈ support
      ((native setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
        (.inr (.bundle index))).run before)) :
    ∃ owner packet, before.1.beacons[index]? = some owner ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      RegistrationNativeKemTarget.PacketKey packet owner.view.kemPublic := by
  simp only [native, RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
    RegistrationNativeRawAdapter.adapter, simulateQ_map, simulateQ_spec_query, StateT.run_map,
    support_map] at supported
  obtain ⟨⟨reply, reachedState⟩, called, equal⟩ := supported
  cases actual : reply with
  | fail error | div => simp [actual, RegistrationNativeRawAdapter.resultOption] at equal
  | ok reply =>
      simp only [actual, RegistrationNativeRawAdapter.resultOption, Prod.mk.injEq] at equal
      obtain ⟨rfl, rfl⟩ := equal
      rw [RegistrationNativeSecretWordTargetSource.typed_run, support_map] at called
      obtain ⟨reached, supported, projected⟩ := called
      have original : reached.1 ∈ support
          ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
            selectedOwner selectedAccept publicPrekey (.inr (.bundle index))).run before.1) := by
        apply OracleComp.support_simulateQ_run'_subset
          (RegistrationNativeSecretWordTargetSource.implementation setup wire route sign input inside provider outer) _ before.2
        rw [StateT.run'_eq, support_map]
        exact Set.mem_image_of_mem Prod.fst supported
      have sameReply : reached.1.1 = .ok (some raw) := by simpa only [actual] using congrArg Prod.fst projected
      rcases reached with ⟨⟨value, frontend⟩, privateState⟩
      dsimp only at sameReply
      subst value
      simp only [RegistrationNativeSecretWordFrontend.handler, RegistrationNativeSecretWordFrontend.beacon,
        StateT.run, support_map] at original
      obtain ⟨ownerResult, lifted, equal⟩ := original
      have nativeOwner := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ lifted
      have resultValue : ownerResult.1.1 = .ok (some raw) := congrArg Prod.fst equal
      rcases ownerResult with ⟨⟨value, owners⟩, env⟩
      dsimp only at resultValue
      subst value
      exact RegistrationNativeSecretWordTargetPublication.bundle_key setup wire readback selectedOwner index publicPrekey
        before.1.beacons before.1.environment raw owners env nativeOwner

/-- Complete original ledger steps preserve all earlier actual publication receipts and add the reached native bundle receipt. -/
theorem step_keeps (readback : RegistrationNativeWire.InitReadBack wire) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK source)
    (prior : Holds wire before.1.transcript before.2.1.beacons)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire
      serverKeyId bounds
      (typed) query).run before)) :
    Holds wire result.2.1.transcript result.2.2.1.beacons := by
  have preserved := RegistrationNativeSecretWordTargetRosterRun.full_step_prefix setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId bounds query before result supported
  have retained := transport wire before.1.transcript before.2.1.beacons result.2.2.1.beacons prior preserved
  have trace := RegistrationNativeSecretWordTargetLedger.step_trace setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId bounds query before result supported
  intro entry member owner raw published
  rw [trace, List.mem_append, List.mem_singleton] at member
  rcases member with earlier | rfl
  · exact retained entry earlier owner raw published
  · cases query with
    | inr secrecy => cases published
    | inl query =>
        rw [RegistrationNativeSecretWordTargetLedger.core_run, support_map] at supported
        obtain ⟨⟨reply, after⟩, reached, equal⟩ := supported
        cases equal
        cases query with
        | inl coin => cases published
        | inr command => cases command with
          | bundle index =>
              cases reply with
              | none => cases published
              | some encoded =>
                  simp only [publication, Option.some.injEq, Prod.mk.injEq] at published
                  obtain ⟨rfl, rfl⟩ := published
                  obtain ⟨old, packet, found, parsed, key⟩ := raw_bundle setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey readback index encoded before.2 after reached
                  obtain ⟨current, currentAt, same⟩ := RegistrationNativeSecretWordTargetRoster.lookup before.2.1.beacons after.1.beacons preserved index old found
                  have publicKey : current.view.kemPublic = old.view.kemPublic := congrArg Prod.snd same
                  exact ⟨current, packet, currentAt, parsed, by simpa only [publicKey] using key⟩
          | _ => cases published

/-- Every supported complete original native run retains all bundle-to-current-owner PQ receipts, including failed raw and private secrecy paths. -/
theorem run_holds (readback : RegistrationNativeWire.InitReadBack wire) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK source) (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before)) :
    Holds wire result.2.1.transcript result.2.2.1.beacons := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query
    (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds
      (typed))
    (fun current => Holds wire current.1.transcript current.2.1.beacons)
    (fun query current valid next reached => step_keeps setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId readback bounds query current valid next reached)
    _ (RegistrationNativeLedger.empty, before) _ result supported
  intro entry member
  cases member

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublicationRun
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublicationRun.raw_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublicationRun.raw_bundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublicationRun.step_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublicationRun.step_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublicationRun.run_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublicationRun.run_holds
