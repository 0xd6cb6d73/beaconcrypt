-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerInstallCaps
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerTrace
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBirthInstallCaps

/-! The actual frontend cannot issue Server installation attempts from coins, records, creation, bundle publication or accept. A Server build's whole chronological attempt bill is funded only by its actual moved Ready, including cancellation and every failed completion. The Beacon finish opposite-role leaf is supplied by the separate concrete Beacon controller module. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerFrontend
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeSecretWordMessage (State)
open RegistrationNativeSecretWordAtomInstallPredicate (LocalInstall GlobalInstall)
open RegistrationNativeSecretWordInterface (liftLocal)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem server_free (role : Role) (selected : Bool)
    (work : RegistrationNativeSecretWordServerCompiler.M n KemSK Value) (before : State source)
    (bounded : ((work.run before.server).run before.environment).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0) :
    ((RegistrationNativeSecretWordFrontend.serverOpen selected work).run before).IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationNativeSecretWordFrontend.serverOpen, StateT.run, isQueryBoundP_map_iff]
  exact RegistrationNativeSecretWordAtomInstallPredicate.local_bound role selected _ 0 bounded

private theorem beacon_free (role : Role)
    (work : RegistrationNativeSecretWordOwners.M n KemSK RegistrationServerRoleBackend.State source Value) (before : State source)
    (bounded : ((work.run before.beacons).run before.environment).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0) :
    ((RegistrationNativeSecretWordFrontend.beacon work).run before).IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationNativeSecretWordFrontend.beacon, StateT.run, isQueryBoundP_map_iff]
  exact RegistrationNativeSecretWordAtomInstallPredicate.local_bound role false _ 0 bounded

private theorem record_free (role : Role) (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source) :
    ((RegistrationNativeSecretWordFrontend.record (n := n) (KemSK := KemSK) query).run before).IsQueryBoundP
      (GlobalInstall (KemSK := KemSK) role) 0 := by
  rcases query with (_ | _) | ⟨owner, _ | _⟩
  all_goals simp only [RegistrationNativeSecretWordFrontend.record, StateT.run]
  all_goals try split
  all_goals simp [GlobalInstall, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

attribute [local irreducible] RegistrationNativeSecretWordServerCompiler.accept RegistrationNativeSecretWordServerCompiler.build

/-- Every original command except the two material-completion commands has zero actual installation callbacks of either role. -/
theorem other_free (role : Role) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (quiet : RegistrationNativeRawAdapter.kind query ≠ 4 ∧ RegistrationNativeRawAdapter.kind query ≠ 5)
    (before : State source) :
    ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before).IsQueryBoundP
      (GlobalInstall (KemSK := KemSK) role) 0 := by
  cases query with
  | inl coin => simp [RegistrationNativeSecretWordFrontend.handler, StateT.run_lift, bind_pure_comp,
      RegistrationNativeSecretWordFrontend.effect, GlobalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install,
      RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  | inr query => cases query with
    | create edPin mlPin keyId =>
        exact beacon_free role _ before
          (RegistrationNativeSecretWordBirthInstallCaps.create_free role setup selectedOwner publicPrekey edPin mlPin keyId before.beacons before.environment)
    | bundle index =>
        exact beacon_free role _ before
          (RegistrationNativeSecretWordBirthInstallCaps.bundle_free role setup wire selectedOwner publicPrekey index before.beacons before.environment)
    | accept packet =>
        simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind]
        exact server_free role _ _ { before with parsedAccepts := before.parsedAccepts + 1 }
          (RegistrationNativeSecretWordAtomServerInstallCaps.accept_bound role setup checks source.verify packet before.server before.environment)
    | build handle application => exact False.elim (quiet.1 rfl)
    | finish index packet => exact False.elim (quiet.2 rfl)
    | hmac key bytes => trivial
    | hash bytes => simp [RegistrationNativeSecretWordFrontend.handler, StateT.run_lift, bind_pure_comp,
        RegistrationNativeSecretWordFrontend.effect, GlobalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install,
        RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    | serverSend keyId plaintext => exact record_free role (.inl (.inl (plaintext, keyId))) before
    | serverRaw raw => exact record_free role (.inl (.inr raw)) before
    | beaconSend index plaintext => exact record_free role (.inr (index, .inl plaintext)) before
    | beaconRaw index raw => exact record_free role (.inr (index, .inr raw)) before

/-- The original whole build callback records at most the atom weight of the exact Ready moved from its native session handle. -/
theorem build_count (role : Role) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (handle : Nat) (application : Option (Slice U8)) (before : State source)
    (trace : RegistrationNativeSecretWordFrontendTrace.State)
    (result : (RegistrationNativeSecretWordServerMaterial.Result × State source) × RegistrationNativeSecretWordFrontendTrace.State)
    (supported : result ∈ support ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.build handle application))).run before)).run trace)) :
    RegistrationNativeSecretWordAtomInstallTrace.count role result.2 ≤ RegistrationNativeSecretWordAtomInstallTrace.count role trace +
      (if role = .server then 1 else 0) * RegistrationNativeSecretWordAtomSessionCredit.weight
        (RegistrationNativeSecretWordServerMaterial.take handle before.server).1 := by
  have exactProgram : (RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.build handle application))).run before =
      (fun reached => (reached.1.1, { before with server := reached.1.2, environment := reached.2 })) <$>
        RegistrationNativeSecretWordAtomServerTrace.compile false setup.source wire sign
          ((RegistrationNativeSecretWordServerMaterial.build wire checks.reservePeer handle application).run before.server) before.environment := by
    simp only [RegistrationNativeSecretWordFrontend.handler, RegistrationNativeSecretWordFrontend.serverOpen,
      RegistrationNativeSecretWordServerCompiler.build, StateT.run, RegistrationNativeSecretWordAtomServerTrace.compile]
    rfl
  rw [exactProgram, simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨reached, material, equal⟩ := supported
  cases equal
  exact RegistrationNativeSecretWordAtomServerTrace.build role false setup.source wire sign checks.reservePeer handle application
    before.server before.environment trace reached material

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerFrontend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerFrontend.other_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerFrontend.other_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerFrontend.build_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerFrontend.build_count
