-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerInstallPrefix

/-! Actual selected and ordinary incoming owner commands cannot install the Server record role. Their current environment, optional authentication, root/material choices and all publication/opening failures remain in the structural query bill. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerOpposite
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordInterface (LocalSpec paired)
open RegistrationNativeSecretWordAtomInstallCaps (Install InstallEnv)
open RegistrationNativeSecretWordAtomInstallPredicate (LocalInstall)
open RegistrationNativeSecretWordMessage (BeaconReady)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}

private def PairServerInstall : (RegistrationNativeSecretWordBeaconMaterial.Spec n).Domain → Prop
  | .inr common => Install .server common
  | _ => False
private instance : DecidablePred (PairServerInstall (n := n)) := fun query => by
  cases query with
  | inl message => exact isFalse id
  | inr common => exact inferInstanceAs (Decidable (Install .server common))

private theorem common_free (work : OracleComp (RegistrationNativePairedServerService.Common n) Value)
    (bounded : work.IsQueryBoundP (Install .server) 0) :
    (simulateQ RegistrationNativeSecretWordServerMaterial.commonLift work).IsQueryBoundP PairServerInstall 0 := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work 0 bounded
  intro query
  simp [RegistrationNativeSecretWordServerMaterial.commonLift, PairServerInstall, isQueryBoundP_query_iff]
  intro charged
  rw [ite_eq_left charged]
  decide

private theorem admitted_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (message : RegistrationNativeSecretWordMessage.Message) :
    (RegistrationNativeSecretWordBeaconMaterial.admitted (n := n) source owner sender descriptor message).IsQueryBoundP PairServerInstall 0 := by
  unfold RegistrationNativeSecretWordBeaconMaterial.admitted
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (by exact id), ?_⟩
  intro choice
  cases choice with
  | none => trivial
  | some choice =>
      apply common_free
      simpa only [reduceCtorEq, ite_false] using
        RegistrationNativeSecretWordAtomInstallCaps.beacon_branch .server source owner sender descriptor choice

private theorem material_abort_free {source : RegistrationNativeMldsa.Source}
    (owner current : SelectedOwner source) (before : EnvState Auxiliary) :
    (((RegistrationNativeSecretWordBeaconMaterial.abort (n := n) owner).run current).run before).IsQueryBoundP PairServerInstall 0 := by
  simp only [RegistrationNativeSecretWordBeaconMaterial.abort, bind_pure_comp]
  simp [RegistrationNativeSecretWordBeaconMaterial.effect, PairServerInstall, Install, InstallEnv, isQueryBoundP_query_iff]

private theorem map_apply {State Value Result : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : Value → Result) (work : StateT State m Value) (before : State) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem material_complete_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (ready : BeaconReady) (before : EnvState Auxiliary) :
    (((RegistrationNativeSecretWordBeaconMaterial.complete (n := n) source owner ready).run current).run before).IsQueryBoundP PairServerInstall 0 := by
  simp only [RegistrationNativeSecretWordBeaconMaterial.complete, StateT.run_bind, StateT.run_lift,
    bind_map_left, bind_pure_comp]
  apply isQueryBoundP_bind (n := 0) (m := 0) (admitted_free source owner.worldOwner owner.pin.binding.identity_key_id ready.descriptor ready.reference)
  intro completed _
  cases completed with
  | fail error | div =>
      simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, map_apply,
        isQueryBoundP_map_iff] using material_abort_free owner current before
  | ok completed => cases completed with
    | Err rejected =>
        simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, map_apply,
          isQueryBoundP_map_iff] using material_abort_free owner current before
    | Ok completed => trivial

/-- The actual incoming material/opening controller never installs the Server role, for any returned material choice. -/
theorem complete_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (ready : BeaconReady) (before : EnvState Auxiliary) :
    (((RegistrationNativeSecretWordBeaconCompiler.complete (n := n) (KemSK := KemSK) source owner ready).run current).run before).IsQueryBoundP
      (LocalInstall (KemSK := KemSK) .server) 0 := by
  change (simulateQ paired _).IsQueryBoundP _ 0
  apply RawCtxSourceOpen.simulate_bound _ PairServerInstall _ _ 0 (material_complete_free source owner current ready before)
  intro query
  cases query with
  | inl message => simp [paired, PairServerInstall, LocalInstall, isQueryBoundP_query_iff]
  | inr common =>
      simp [paired, PairServerInstall, LocalInstall, isQueryBoundP_query_iff]
      intro charged
      rw [ite_eq_left charged]
      decide

/-- Every native terminal, authentication, failure and completion branch of an incoming owner call is Server-installation-free. -/
theorem finish_free (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (before : EnvState Auxiliary) :
    (((RegistrationNativeSecretWordBeaconCompiler.finish (n := n) setup source packet).run owner).run before).IsQueryBoundP
      (LocalInstall (KemSK := KemSK) .server) 0 := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.finish, StateT.run_bind, StateT.run_get, pure_bind]
  cases phase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ => trivial
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error | div => simp only [moved, StateT.run_pure]; trivial
      | ok aborted =>
          simp only [moved]
          apply isQueryBoundP_bind (n := 0) (m := 0)
            (RegistrationNativeSecretWordAtomOwnerInstallPrefix.preparation_free .server setup source packet owner before)
          intro result _
          rcases result with ⟨⟨prepared, current⟩, env⟩
          cases prepared with
          | fail error | div =>
              simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                (RegistrationNativeSecretWordAtomOwnerInstallPrefix.abort_free .server (KemSK := KemSK) owner current env)
          | ok prepared => cases prepared with
            | none =>
                simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                  (RegistrationNativeSecretWordAtomOwnerInstallPrefix.abort_free .server (KemSK := KemSK) owner current env)
            | some ready => exact complete_free setup.source owner current ready env

private theorem ordinary_bound (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (LocalSpec n KemSK) Value) (bounded : work.IsQueryBoundP (LocalInstall (KemSK := KemSK) .server) 0) :
    (simulateQ (RegistrationNativeSecretWordOwners.ordinary setup scalar) work).IsQueryBoundP
      (LocalInstall (KemSK := KemSK) .server) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work 0 bounded
  intro query
  cases query with
  | inl message =>
      simp only [RegistrationNativeSecretWordOwners.ordinary, LocalInstall]
      split <;> simp [LocalInstall, isQueryBoundP_query_iff]
  | inr query =>
      simp only [RegistrationNativeSecretWordOwners.ordinary, isQueryBoundP_query_iff]
      intro charged
      rw [ite_eq_left charged]
      decide

/-- The actual mixed local-owner finish, including absent and ordinary owners, emits no Server installation query. -/
theorem owners_free (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (before : EnvState Auxiliary) :
    (((RegistrationNativeSecretWordOwners.finish (n := n) setup source index packet).run owners).run before).IsQueryBoundP
      (LocalInstall (KemSK := KemSK) .server) 0 := by
  simp only [RegistrationNativeSecretWordOwners.finish, StateT.run]
  cases found : owners[index]? with
  | none => trivial
  | some owner =>
      rw [isQueryBoundP_map_iff]
      cases chosen : owner.scalar with
      | none => exact finish_free setup source packet owner.view before
      | some scalar => exact ordinary_bound setup scalar _ (finish_free setup source packet owner.view before)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerOpposite
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerOpposite.complete_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerOpposite.complete_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerOpposite.finish_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerOpposite.finish_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerOpposite.owners_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerOpposite.owners_free
