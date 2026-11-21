-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedServerPrefix
import BeaconcryptCore.Computational.RegistrationNativePairedBirthPrefix
import BeaconcryptCore.Computational.RegistrationNativePairedBeacon

/-! The actual frontend cannot issue Server installation attempts from coins, records, creation, bundle publication or accept. A Server build's whole chronological attempt bill is funded only by its actual moved Ready, including cancellation and every failed completion. The Beacon finish opposite-role leaf is supplied by the separate concrete Beacon controller module. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedOther
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (Role)
open RegistrationNativePublicFrontend (State)
open RegistrationNativeSecretWordAtomOwnerInstallPrefix renaming NativeInstall → LocalInstall
open RegistrationNativePairedSafe (GlobalInstall)
open RegistrationNativePublicFrontend (liftLocal)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem server_free (role : Role) (selected : Bool)
    (work : RegistrationServerOpenReferenceCompiler.M n KemSK Value) (before : State source)
    (bounded : ((work.run before.server).run before.environment).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0) :
    ((RegistrationNativePublicFrontend.serverOpen selected work).run before).IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationNativePublicFrontend.serverOpen, StateT.run, isQueryBoundP_map_iff]
  exact RegistrationNativePairedSafe.local_bound role selected _ 0 bounded

private theorem beacon_free (role : Role)
    (work : RegistrationNativePublicOwners.M n KemSK RegistrationServerRoleBackend.State source Value) (before : State source)
    (bounded : ((work.run before.beacons).run before.environment).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0) :
    ((RegistrationNativePublicFrontend.beacon work).run before).IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationNativePublicFrontend.beacon, StateT.run, isQueryBoundP_map_iff]
  exact RegistrationNativePairedSafe.local_bound role false _ 0 bounded

private theorem record_free (role : Role) (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source) :
    ((RegistrationNativePublicFrontend.record (n := n) (KemSK := KemSK) query).run before).IsQueryBoundP
      (GlobalInstall (KemSK := KemSK) role) 0 := by
  rcases query with (_ | _) | ⟨owner, _ | _⟩
  all_goals simp only [RegistrationNativePublicFrontend.record, StateT.run]
  all_goals try split
  all_goals simp [GlobalInstall, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

attribute [local irreducible] RegistrationServerOpenReferenceCompiler.accept RegistrationServerOpenReferenceCompiler.build

/-- Every original command except the two material-completion commands has zero actual installation callbacks of either role. -/
theorem other_free (role : Role) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (quiet : RegistrationNativeRawAdapter.kind query ≠ 4 ∧ RegistrationNativeRawAdapter.kind query ≠ 5)
    (before : State source) :
    ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before).IsQueryBoundP
      (GlobalInstall (KemSK := KemSK) role) 0 := by
  cases query with
  | inl coin => simp [RegistrationNativePublicFrontend.handler, StateT.run_lift, bind_pure_comp,
      RegistrationNativePublicFrontend.effect, RegistrationNativePublicFrontend.liftLocal, GlobalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install,
      RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  | inr query => cases query with
    | create edPin mlPin keyId =>
        exact beacon_free role _ before
          (RegistrationNativePairedBirthPrefix.create_free role setup selectedOwner publicPrekey edPin mlPin keyId before.beacons before.environment)
    | bundle index =>
        exact beacon_free role _ before
          (RegistrationNativePairedBirthPrefix.bundle_free role setup wire selectedOwner publicPrekey index before.beacons before.environment)
    | accept packet =>
        simp only [RegistrationNativePublicFrontend.handler, StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind]
        exact server_free role _ _ { before with parsedAccepts := before.parsedAccepts + 1 }
          (RegistrationNativePairedServerPrefix.accept_free role setup checks source.verify packet before.server before.environment)
    | build handle application => exact False.elim (quiet.1 rfl)
    | finish index packet => exact False.elim (quiet.2 rfl)
    | hmac key bytes => trivial
    | hash bytes => simp [RegistrationNativePublicFrontend.handler, StateT.run_lift, bind_pure_comp,
        RegistrationNativePublicFrontend.effect, RegistrationNativePublicFrontend.liftLocal, GlobalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install,
        RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    | serverSend keyId plaintext => exact record_free role (.inl (.inl (plaintext, keyId))) before
    | serverRaw raw => exact record_free role (.inl (.inr raw)) before
    | beaconSend index plaintext => exact record_free role (.inr (index, .inl plaintext)) before
    | beaconRaw index raw => exact record_free role (.inr (index, .inr raw)) before

end BeaconcryptCore.Computational.RegistrationNativePairedOther

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedOther.other_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedOther.other_free
