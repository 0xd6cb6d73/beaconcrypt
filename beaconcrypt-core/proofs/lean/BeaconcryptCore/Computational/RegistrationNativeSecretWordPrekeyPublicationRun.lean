-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRosterRun
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyPublication
import BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerMaskInvariant

/-! Every selected-owner bundle in the complete initialized Word ledger carries its canonical public prekey. The invariant follows the actual typed controller and survives constructor, authentication, raw-adapter, secrecy and terminal failure branches. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyPublicationRun
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

def Holds (wire : Wire) (selectedOwner : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (transcript : List Entry) : Prop :=
  ∀ entry ∈ transcript, ∀ raw, publication entry = some (selectedOwner, raw) →
    ∃ packet, RegistrationNativeWire.readInit wire raw = some packet ∧
      (PqxdhRefinement.absBytes packet.pre_key).drop 64 = PqxdhEd25519EufCma.prekeyMessage publicPrekey

/-- Concrete typed callbacks retain the canonical public prekey through arbitrary outer stateful replies. -/
theorem typed_canonical (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State n KemSK source) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (valid : RegistrationNativePublicOwnerMask.Canonical selectedOwner publicPrekey before.1.beacons)
    (supported : result ∈ support ((typed query).run before)) :
    RegistrationNativePublicOwnerMask.Canonical selectedOwner publicPrekey result.2.1.beacons := by
  rw [RegistrationNativeSecretWordTargetSource.typed_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  have original : reached.1 ∈ support
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
        selectedOwner selectedAccept publicPrekey query).run before.1) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeSecretWordTargetSource.implementation setup wire route sign input inside provider outer) _ before.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst called
  cases equal
  exact RegistrationNativeSecretWordOwnerMaskInvariant.query_canonical setup checks wire sign
    selectedOwner selectedAccept publicPrekey query before.1 reached.1 valid original

private theorem program_canonical (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (valid : RegistrationNativePublicOwnerMask.Canonical selectedOwner publicPrekey before.1.beacons)
    (supported : result ∈ support ((simulateQ typed work).run before)) :
    RegistrationNativePublicOwnerMask.Canonical selectedOwner publicPrekey result.2.1.beacons :=
  OracleComp.simulateQ_run_preserves_inv_of_query typed
    (fun current => RegistrationNativePublicOwnerMask.Canonical selectedOwner publicPrekey current.1.beacons)
    (fun query current prior next called => typed_canonical setup checks wire route sign input inside provider outer
      selectedOwner selectedAccept publicPrekey query current next prior called) work before valid result supported

private theorem raw_canonical (work : OracleComp RegistrationNativeInterface.Spec Value)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (valid : RegistrationNativePublicOwnerMask.Canonical selectedOwner publicPrekey before.1.beacons)
    (supported : result ∈ support ((simulateQ (RegistrationNativeRawAdapter.handler wire typed) work).run before)) :
    RegistrationNativePublicOwnerMask.Canonical selectedOwner publicPrekey result.2.1.beacons := by
  rw [RegistrationNativeRawAdapter.program_native] at supported
  exact program_canonical setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
    _ before result valid supported

private theorem full_canonical (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK source)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source))
    (valid : RegistrationNativePublicOwnerMask.Canonical selectedOwner publicPrekey before.2.1.beacons)
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed query).run before)) :
    RegistrationNativePublicOwnerMask.Canonical selectedOwner publicPrekey result.2.2.1.beacons := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨inner, called, rfl⟩ := supported
  exact raw_canonical setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
    _ before.2 inner valid called

/-- A successful original raw bundle has the actual earlier symbolic owner and its decoded signed PQ payload. -/
theorem raw_bundle (readback : RegistrationNativeWire.InitReadBack wire) (index : Nat) (raw : Pqxdh.Bytes)
    (before after : State n KemSK source)
    (supported : (some raw, after) ∈ support
      ((native setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
        (.inr (.bundle index))).run before)) :
    ∃ owner packet, before.1.beacons[index]? = some owner ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      (PqxdhRefinement.absBytes packet.pre_key).drop 64 = PqxdhEd25519EufCma.prekeyMessage (PqxdhPhase2InputBytes.word owner.view.prekeyPublic) := by
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
      exact RegistrationNativeSecretWordPrekeyPublication.bundle_prekey setup wire readback selectedOwner index publicPrekey
        before.1.beacons before.1.environment raw owners env nativeOwner

/-- Each actual full ledger step records the selected owner's unchanged public signed prekey. -/
theorem step_keeps (readback : RegistrationNativeWire.InitReadBack wire) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK source)
    (prior : RegistrationNativePublicOwnerMask.Canonical selectedOwner publicPrekey before.2.1.beacons ∧
      Holds wire selectedOwner publicPrekey before.1.transcript)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed query).run before)) :
    RegistrationNativePublicOwnerMask.Canonical selectedOwner publicPrekey result.2.2.1.beacons ∧
      Holds wire selectedOwner publicPrekey result.2.1.transcript := by
  refine ⟨full_canonical setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId bounds query before result prior.1 supported, ?_⟩
  have trace := RegistrationNativeSecretWordTargetLedger.step_trace setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId bounds query before result supported
  intro entry member raw published
  rw [trace, List.mem_append, List.mem_singleton] at member
  rcases member with earlier | rfl
  · exact prior.2 entry earlier raw published
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
                  obtain ⟨sameOwner, rfl⟩ := published
                  subst index
                  obtain ⟨owner, packet, found, parsed, key⟩ := raw_bundle setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey readback selectedOwner encoded before.2 after reached
                  have canonical := prior.1 selectedOwner owner found
                  simp only [RegistrationNativePublicOwnerMask.At, ite_true] at canonical
                  refine ⟨packet, parsed, ?_⟩
                  simpa only [canonical.2, PqxdhPhase2InputBytes.word_rootArray] using key
          | _ => cases published

/-- The selected public prekey is recovered from every actual published bundle of the complete initialized Word source. -/
theorem run_holds (readback : RegistrationNativeWire.InitReadBack wire) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK source) (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (empty : before.1.beacons = [])
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before)) :
    Holds wire selectedOwner publicPrekey result.2.1.transcript := by
  have invariant := OracleComp.simulateQ_run_preserves_inv_of_query
    (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed)
    (fun current => RegistrationNativePublicOwnerMask.Canonical selectedOwner publicPrekey current.2.1.beacons ∧
      Holds wire selectedOwner publicPrekey current.1.transcript)
    (fun query current valid next reached => step_keeps setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId readback bounds query current valid next reached)
    _ (RegistrationNativeLedger.empty, before)
    (And.intro (empty ▸ RegistrationNativePublicOwnerMask.empty selectedOwner publicPrekey)
      (by intro entry member; cases member)) result supported
  exact invariant.2

end BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyPublicationRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyPublicationRun.typed_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyPublicationRun.typed_canonical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyPublicationRun.raw_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyPublicationRun.raw_bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyPublicationRun.step_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyPublicationRun.step_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyPublicationRun.run_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyPublicationRun.run_holds
