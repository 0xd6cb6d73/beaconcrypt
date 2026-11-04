-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier
import BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerReifier
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerReification
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkReification
variable {n : Nat} {KemSK Platform : Type} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Snapshot" => RegistrationNativePlatformExtractedSdkCarrier.SourceSnapshot n KemSK Platform source

def rawAttempts (state : Native) : Nat :=
  (state.server.world.world.1.server.map (fun records=>records.records.rawAttempts)).getD 0

def snapshot (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (self : beaconcrypt_public_wrapper.server.Server)
    (environment : Option (RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State))
    (raw : Native×Platform) : Snapshot :=
  .server environment (AdapterPublicOrdinaryServerReifier.server view views self (rawAttempts raw.1)) raw

def acceptEnvironment {R : Type} (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (before : Native) (receipt : AdapterPublicServerReservationReceipt.Receipt R) :
    Option (RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) :=
  match receipt with
  | some (.ok ((_,journal),capture))=>some ⟨AdapterPublicAgreementServerWorld.project view capture,
      before.server.world.requests++RegistrationAgreementWorldTrace.recorded journal,
      before.server.world.recordRequests,before.server.world.world.2⟩
  | _=>none

def environmentCommit (environment : Option (RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State))
    (raw : Native) : Native := match environment with | none=>raw | some returned=>commitEnvironment returned raw

private theorem effect_backend {R : Type} (effect : RustM agreement.AgreementEffect)
    (word : RustM (AdapterPublicServerAgreementReceipt.Word R)) (raw : Native) :
    backend (AdapterPublicServerAgreementRetention.projectEffect effect (word,raw)).2=backend raw ∧
      (AdapterPublicServerAgreementRetention.projectEffect effect (word,raw)).2.server.world.world.1.server=raw.server.world.world.1.server := by
  cases effect with
  | fail error | div => cases word <;> exact ⟨rfl,rfl⟩
  | ok effect =>
    cases effect <;> try { cases word <;> exact ⟨rfl,rfl⟩ }
    case ServerComplete completed =>
      cases word with
      | fail error | div => exact ⟨rfl,rfl⟩
      | ok word =>
        rcases word with ⟨token,self,rng⟩
        cases token <;> exact ⟨rfl,rfl⟩

private theorem accept_restored {R : Type}
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (before raw after : Native) (receipt : AdapterPublicServerReservationReceipt.Receipt R)
    (word : AdapterPublicServerAgreementReceipt.Word R) (reply : RustM (Option Nat))
    (projected : AdapterPublicServerReservationNative.project view before ((receipt,.ok word),raw)=.ok (reply,after))
    (poolEq : raw.pool=before.pool) :
    backend (environmentCommit (acceptEnvironment view before receipt) raw)=backend after ∧
      after.server.world.world.1.server=raw.server.world.world.1.server := by
  cases receipt with
  | none =>
    have same:=congrArg Prod.snd (RustM.ok.inj projected)
    cases same
    exact ⟨rfl,rfl⟩
  | some receipt =>
    cases receipt with
    | fail error | div => cases projected
    | ok pair =>
      rcases pair with ⟨⟨effect,journal⟩,capture⟩
      let current : Native := {before with server:={before.server with world:=
        (RegistrationAgreementWorldTrace.restore before.server.world
          (((effect,journal),AdapterPublicAgreementServerWorld.project view capture),raw.server.world.world.1)).2}}
      have same : AdapterPublicServerAgreementRetention.projectEffect effect (.ok word,current)=(reply,after) :=
        RustM.ok.inj projected
      have currentBackend : backend (environmentCommit (acceptEnvironment view before (some (.ok ((effect,journal),capture)))) raw)=backend current := by
        change (⟨_,raw.pool,_⟩ : Backend n KemSK)=⟨_,before.pool,_⟩
        rw [poolEq]
        rfl
      have unchanged:=effect_backend effect (.ok word) current
      have afterEq:=congrArg Prod.snd same
      rw [afterEq] at unchanged
      exact ⟨currentBackend.trans unchanged.1.symm,unchanged.2⟩

private theorem snapshot_commit (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (self : beaconcrypt_public_wrapper.server.Server) (environment) (raw : Native×Platform)
    (matched : raw.1.server.world.world.1.server=some (AdapterPublicOrdinaryServerReifier.server view views self (rawAttempts raw.1))) :
    (snapshot view views self environment raw).committed=(environmentCommit environment raw.1,raw.2) := by
  have serverEq : {raw.1.server.world.world.1 with server:=some (AdapterPublicOrdinaryServerReifier.server view views self (rawAttempts raw.1))}=raw.1.server.world.world.1 := by
    rw [←matched]
  simp only [snapshot,RegistrationNativePlatformExtractedSdkCarrier.SourceSnapshot.committed]
  rw [serverEq]
  cases environment <;> rfl

/-- The source Server row is computed from the actual returned object and raw counter. -/
theorem accept_project {R : Type}
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (before raw after : Native) (receipt : AdapterPublicServerReservationReceipt.Receipt R)
    (word : AdapterPublicServerAgreementReceipt.Word R) (reply : RustM (Option Nat))
    (projected : AdapterPublicServerReservationNative.project view before ((receipt,.ok word),raw)=.ok (reply,after))
    (poolEq : raw.pool=before.pool)
    (held : AdapterPublicWrapperState.Server view views created credential word.2.1 after.server)
    (previous : Platform) :
    persistent (snapshot view views word.2.1 (acceptEnvironment view before receipt) (raw,previous)).committed=
      persistent (after,previous) := by
  have restored:=accept_restored view before raw after receipt word reply projected poolEq
  obtain ⟨records,present,matched⟩:=AdapterPublicOrdinaryServerReifier.related view views created credential word.2.1 after.server held
  have rawPresent : raw.server.world.world.1.server=some records:=restored.2.symm.trans present
  have attempts : rawAttempts raw=records.records.rawAttempts := by
    simp only [rawAttempts,rawPresent,Option.map_some,Option.getD_some]
  have exactRecord : raw.server.world.world.1.server=some (AdapterPublicOrdinaryServerReifier.server view views word.2.1 (rawAttempts raw)) := by
    rw [attempts,matched]
    exact rawPresent
  rw [snapshot_commit view views word.2.1 _ (raw,previous) exactRecord]
  exact Prod.ext restored.1 rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerReification

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerReification.accept_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerReification.accept_project
