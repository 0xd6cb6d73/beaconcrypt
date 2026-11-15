-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRosterRun
import BeaconcryptCore.Computational.RegistrationNativePlatformNativeBundleFields
import BeaconcryptCore.Computational.RegistrationNativeLedgerJournal
import BeaconcryptCore.Computational.RegistrationNativePrekeyPublicationTrace
import BeaconcryptCore.Computational.RegistrationNativeIdentityPublicationTrace
/-! Every successful concrete source bundle remains tied to the final retained owner identity and prekey. The full adaptive ledger proof keeps stateful writer failures and all ordinary record effects. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicationTrace
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

variable {A : Type} [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "wire" => RegistrationNativePlatformConcreteSource.wire
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets
local notation "typed" => RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation created credential
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "native" => RegistrationNativeRawAdapter.handler canonical typed
open RegistrationNativeOwnerRoster (Prefix)
open RegistrationNativePrekeyPublicationTrace (publication)
open RegistrationNativeOwnerFields (metadata)


def Holds (ledger : List RegistrationNativeInterface.Entry) (owners : RegistrationNativeBeaconFrontend.State source) : Prop :=
  ∀ entry ∈ ledger,∀ index raw,publication entry = some (index,raw) →
    ∃ owner packet,owners[index]? = some owner ∧ RegistrationNativeWire.readInit canonical raw = some packet ∧
      (PqxdhRefinement.absBytes packet.pre_key).drop 64 = PqxdhEd25519EufCma.prekeyMessage (PqxdhPhase2InputBytes.word owner.prekeyPublic) ∧
      PqxdhEd25519EufCma.parseIdentity (PqxdhRefinement.absBytes packet.identity_key) = some (setup.joint.publicKeys owner.identitySeed).ed25519

omit primitive in
private theorem transport (ledger : List RegistrationNativeInterface.Entry)
    (before after : RegistrationNativeBeaconFrontend.State source) (prior : Holds setup ledger before)
    (prefixOwners : Prefix before after) : Holds setup ledger after := by
  intro entry member index raw published
  obtain ⟨old,packet,found,decoded,key,identity⟩ := prior entry member index raw published
  obtain ⟨current,currentAt,same⟩ := RegistrationNativeOwnerRoster.lookup before after prefixOwners index old found
  have prekey : current.prekeyPublic = old.prekeyPublic := congrArg (fun owner => owner.prekeyPublic) same
  have seed : current.identitySeed = old.identitySeed := congrArg (fun owner => owner.identitySeed) same
  exact ⟨current,packet,currentAt,decoded,by simpa only [prekey] using key,by simpa only [seed] using identity⟩

omit primitive in
private theorem unpack {X : Type} (work : StateT Native (StateT Platform ProbComp) X)
    (before : Native × Platform) (result : X × (Native × Platform))
    (supported : result ∈ support ((RegistrationNativePlatformPackedState.pack work).run before)) :
    ((result.1,result.2.1),result.2.2) ∈ support ((work.run before.1).run before.2) := by
  simp only [RegistrationNativePlatformPackedState.pack,StateT.run,support_map] at supported
  obtain ⟨actual,called,same⟩ := supported
  cases same
  exact called

/-- Every literal successful raw bundle returns its pre-call native owner and concrete identity/prekey packet. -/
theorem raw_bundle (index : Nat) (raw : Pqxdh.Bytes) (before after : Native × Platform)
    (supported : (some raw,after) ∈ support ((native (.inr (.bundle index))).run before)) :
    ∃ owner packet,before.1.beacons[index]? = some owner ∧ RegistrationNativeWire.readInit canonical raw = some packet ∧
      (PqxdhRefinement.absBytes packet.pre_key).drop 64 = PqxdhEd25519EufCma.prekeyMessage (PqxdhPhase2InputBytes.word owner.prekeyPublic) ∧
      PqxdhEd25519EufCma.parseIdentity (PqxdhRefinement.absBytes packet.identity_key) = some (setup.joint.publicKeys owner.identitySeed).ed25519 := by
  simp only [RegistrationNativeRawAdapter.handler,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,
    simulateQ_map,simulateQ_spec_query,StateT.run_map,support_map] at supported
  obtain ⟨⟨reply,reached⟩,called,equal⟩ := supported
  cases actual : reply with
  | fail error | div => simp [actual,RegistrationNativeRawAdapter.resultOption] at equal
  | ok optional =>
    simp only [actual,RegistrationNativeRawAdapter.resultOption,Prod.mk.injEq] at equal
    obtain ⟨rfl,rfl⟩ := equal
    rw [actual] at called
    have original := unpack (RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.bundle index))) before (RustM.ok (some raw),reached) called
    exact RegistrationNativePlatformNativeBundleFields.bundle RegistrationNativePlatformMldsaProgram.coins setup checks representation created reservePackets
      index before.1 reached.1 before.2 reached.2 raw original

/-- Each original full-ledger step preserves all earlier concrete publication tuples at their same final owner indices. -/
theorem step_keeps (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × (Native × Platform)) (prior : Holds setup before.1.transcript before.2.1.beacons)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × (Native × Platform)))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto canonical created.server.server.metadata.sender bounds typed query).run before)) :
    Holds setup result.2.1.transcript result.2.2.1.beacons := by
  have prefixOwners := RegistrationNativePlatformOrdinaryRosterRun.full_prefix setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds query before result supported
  have retained := transport setup before.1.transcript before.2.1.beacons result.2.2.1.beacons prior prefixOwners
  have trace := RegistrationNativeLedgerJournal.handler_records native setup.source.crypto (RegistrationNativeWire.ledgerCodec canonical)
    created.server.server.metadata.sender bounds query before result supported
  intro entry member index raw published
  rw [trace,List.mem_append,List.mem_singleton] at member
  rcases member with earlier | rfl
  · exact retained entry earlier index raw published
  · cases query with
    | inr secrecy => cases published
    | inl query =>
      rw [RegistrationNativeTargetLedgerCore.run,support_map] at supported
      obtain ⟨⟨reply,after⟩,called,equal⟩ := supported
      cases equal
      cases query with
      | inl coin => cases published
      | inr command => cases command with
        | bundle actualIndex =>
          cases reply with
          | none => cases published
          | some encoded =>
            simp only [publication,Option.some.injEq,Prod.mk.injEq] at published
            obtain ⟨rfl,rfl⟩ := published
            obtain ⟨old,packet,found,decoded,key,identity⟩ := raw_bundle setup checks route representation created credential view failure allocation
              reserveRegistration reservePeer reserveFrame erased helper reservePackets actualIndex encoded before.2 after called
            obtain ⟨current,currentAt,same⟩ := RegistrationNativeOwnerRoster.lookup before.2.1.beacons after.1.beacons prefixOwners actualIndex old found
            have prekey : current.prekeyPublic = old.prekeyPublic := congrArg (fun owner => owner.prekeyPublic) same
            have seed : current.identitySeed = old.identitySeed := congrArg (fun owner => owner.identitySeed) same
            exact ⟨current,packet,currentAt,decoded,by simpa only [prekey] using key,by simpa only [seed] using identity⟩
        | _ => cases published

/-- The complete actual corrected full raw execution retains every successful publication's identity and prekey in its final roster. -/
theorem run_holds (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : Native × Platform)
    (result : A × (RegistrationNativeLedger.State × (Native × Platform)))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto canonical created.server.server.metadata.sender bounds typed mode work before)) :
    Holds setup result.2.1.transcript result.2.2.1.beacons := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query
    (RegistrationNativeFullCompiler.handler setup.source.crypto canonical created.server.server.metadata.sender bounds typed)
    (fun current => Holds setup current.1.transcript current.2.1.beacons)
    (fun query current valid next reached => step_keeps setup checks route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reservePackets bounds query current valid next reached)
    _ (RegistrationNativeLedger.empty,before) _ result supported
  intro entry member
  cases member

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicationTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicationTrace.raw_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicationTrace.raw_bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicationTrace.step_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicationTrace.step_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicationTrace.run_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPublicationTrace.run_holds
