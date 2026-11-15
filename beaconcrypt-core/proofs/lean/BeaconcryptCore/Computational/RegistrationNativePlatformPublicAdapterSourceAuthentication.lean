-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningHistory
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceEvents
import BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent
/-! The Server response unsigned-origin decision reads only actual SDK objects, returned source tokens, parsed public input and earlier source signing observations. Protection is public-key qualification; no key uniqueness or signature uniqueness is imposed. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthentication
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicAdapterStore (Store erase)
open RegistrationNativePlatformExtractedSdkCarrier (Carrier BeaconTable)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
open RegistrationNativePlatformPublicAdapterSourceSigningHistory (history)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK R P : Type} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

inductive Bad (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (serverPublic : Std.Array U8 1952#usize) (log : List Stage) :
    (command : RegistrationNativePlatformPublicAdapterInterface.Command) → Store n KemSK R P →
      RegistrationNativePlatformPublicAdapterInterface.CommandSpec.Range command → Store n KemSK R P → Prop where
  | finish (index : Nat) (input : Slice U8) (packet : registration.ResponsePacket) (application : Pqxdh.Bytes)
      (before after : Store n KemSK R P) (owner : beaconcrypt_public_wrapper.beacon.Beacon)
      (pending : registration.BeaconPending) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
      (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
      (decoded : RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)=some packet)
      (found : before.beacons index=some owner) (phase : owner.state=.InitSent pending prekey oneTime kem)
      (protectedKey : pending.binding.server_pin.public_key=serverPublic)
      (absent : ¬ MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial true pending packet
        (history (PqxdhRefinement.absBytes pending.binding.server_pin.public_key) log))) :
      Bad view serverPublic log (.finish index input) before (some application) after

def stages (events : List (RegistrationNativePlatformPublicAdapterSourceEvents.Event n KemSK R P)) : List Stage :=
  events.filterMap fun event => match event with
    | .stage actual => some actual
    | _ => none

/-- A failure belongs to one exact source callback: only its actual source operations occur between the matching opening and closing. Its history is the strict earlier source prefix. -/
def Occurred (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (serverPublic : Std.Array U8 1952#usize)
    (events : List (RegistrationNativePlatformPublicAdapterSourceEvents.Event n KemSK R P)) : Prop :=
  ∃ command : RegistrationNativePlatformPublicAdapterInterface.Command, ∃ leading middle trailing before reply objects backend,
    events=leading ++ RegistrationNativePlatformPublicAdapterSourceEvents.Event.opened (.inl (.inr command)) before ::
      (List.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage middle ++
        RegistrationNativePlatformPublicAdapterSourceEvents.Event.closed (.inl (.inr command)) (.ok (reply,objects)) backend :: trailing) ∧
    Bad view serverPublic (stages leading) command before reply
      (RegistrationNativePlatformPublicAdapterSourceRuntime.join objects backend)

noncomputable def flag (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (serverPublic : Std.Array U8 1952#usize)
    (events : List (RegistrationNativePlatformPublicAdapterSourceEvents.Event n KemSK R P)) : Bool := by
  classical
  exact decide (Occurred view serverPublic events)

theorem flag_iff (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (serverPublic : Std.Array U8 1952#usize)
    (events : List (RegistrationNativePlatformPublicAdapterSourceEvents.Event n KemSK R P)) :
    flag view serverPublic events=true ↔ Occurred view serverPublic events := by
  simp only [flag,decide_eq_true_eq]

theorem beacon (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source) (current : Native × P)
    (before : Carrier (R:=R) view views joint created credential current)
    (index : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (found : (erase before.objects).beacons index=some self) :
    ∃ owner, current.1.beacons[index]?=some owner ∧ AdapterPublicWrapperState.Beacon view joint current.1.pool self owner
      current.1.server.world.world.1.owners[owner.worldOwner]? := by
  have held := before.beacons index
  change before.objects.beacons index=some self at found
  cases selected : current.1.beacons[index]? with
  | none =>
    simp only [selected] at held
    rw [found] at held
    cases held
  | some owner =>
    simp only [selected] at held
    obtain ⟨original,same,related⟩ := held
    have equal : original=self := Option.some.inj (same.symm.trans found)
    cases equal
    exact ⟨owner,rfl,related⟩

omit platform in
theorem pending (view : AdapterPublicWrapperState.MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (world : Option PqxdhRecordLiftBeacon.Phase)
    (held : AdapterPublicWrapperState.Beacon view joint pool self owner world)
    (pending : registration.BeaconPending) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (phase : self.state=.InitSent pending prekey oneTime kem) :
    ∃ scalar, owner.phase=.initSent pending scalar := by
  have matched := held.phase
  cases current : owner.phase with
  | fresh | freshWithCoins scalar | established completed | aborted control =>
    simp only [AdapterPublicWrapperState.Phase,phase,current] at matched
  | initSent retained scalar =>
    simp only [AdapterPublicWrapperState.Phase,phase,current] at matched
    cases matched.1
    exact ⟨scalar,rfl⟩

theorem finish (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source) (current : Native × P)
    (before : Carrier (R:=R) view views joint created credential current)
    (log : List Stage)
    (historyEq : ∀ key, RegistrationSigningShared.historyFor key (RegistrationNativeMldsaShared.nativeProject current.1)=history key log)
    (index : Nat) (packet : registration.ResponsePacket) (application : Pqxdh.Bytes)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (found : (erase before.objects).beacons index=some self)
    (retained : registration.BeaconPending) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (phase : self.state=.InitSent retained prekey oneTime kem)
    (protectedKey : retained.binding.server_pin.public_key=credential.publicKey)
    (absent : ¬ MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial true retained packet
      (history (PqxdhRefinement.absBytes retained.binding.server_pin.public_key) log))) :
    RegistrationNativeMldsaOriginEvent.Bad source credential (.inr (.finish index (some packet))) current.1 (.ok (some application)) := by
  obtain ⟨owner,selected,held⟩ := beacon view views joint created credential current before index self found
  obtain ⟨scalar,ownerPhase⟩ := pending view joint current.1.pool self owner _ held retained prekey oneTime kem phase
  apply RegistrationNativeMldsaOriginEvent.Bad.finish index packet application current.1 owner retained scalar selected ownerPhase protectedKey
  simpa only [historyEq] using absent

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthentication.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthentication.beacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthentication.pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthentication.pending
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthentication.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthentication.finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthentication.flag_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthentication.flag_iff
