-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedMaterialSource
import BeaconcryptCore.Computational.RegistrationNativePairedBeaconPrefix
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedBeacon

/-! The actual native Beacon material program inherits the paired-slot certificate from its open Word material AST while preserving every arbitrary hidden Choice reply. Literalizing the descriptor is only a proof inverse; the executing native controller, owner, current environment and terminal failures are unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedBeacon
open RegistrationNativePairedTrace (Safe)
open RegistrationNativePairedMaterialSource (nativeLift wordLift)
open RegistrationNativePublicFrontend (liftLocal)
open RegistrationNativeSecretWordMessage (BeaconReady)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
variable {n : Nat} {KemSK Auxiliary Value : Type}

private def literalReady (ready : RegistrationBeaconReferenceRoot.Ready) : BeaconReady :=
  ⟨ready.descriptor, RegistrationNativeSecretWordMessage.literal ready.reference⟩
private theorem eval_literal (candidate : PqxdhKemIndCca.MlKemSharedSecret) (ready : RegistrationBeaconReferenceRoot.Ready) :
    (literalReady ready).eval candidate = ready := by
  cases ready
  simp only [literalReady, RegistrationNativeSecretWordMessage.BeaconReady.eval, RegistrationNativeSecretWordMessage.eval_literal]

private theorem service : (liftLocal (n := n) (KemSK := KemSK) false) ∘ₛ (RegistrationBeaconReferenceFinish.service (n := n) (KemSK := KemSK)) = (nativeLift (n := n) (KemSK := KemSK)) := by
  funext query
  simp only [QueryImpl.compose, RegistrationBeaconReferenceFinish.service, simulateQ_spec_query, liftLocal, nativeLift]

/-- The actual complete native Beacon material continuation preserves the paired monitor for arbitrary source material choices. -/
theorem complete (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (ready : RegistrationBeaconReferenceRoot.Ready) (env : EnvState Auxiliary) :
    Safe (simulateQ (liftLocal (n := n) (KemSK := KemSK) false)
      (((RegistrationBeaconReferenceFinish.complete (n := n) (KemSK := KemSK) source owner ready).run current).run env)) := by
  have certificate := RegistrationNativeSecretWordPairedBeacon.complete (n := n) (KemSK := KemSK) source owner current (literalReady ready) env
  have raw : RegistrationNativeSecretWordPairedTrace.Safe (simulateQ (wordLift (n := n) (KemSK := KemSK))
      (((RegistrationNativeSecretWordBeaconMaterial.complete (n := n) source owner (literalReady ready)).run current).run env)) := by
    simpa only [RegistrationNativeSecretWordPairedBeacon.compile, wordLift, QueryImpl.simulateQ_compose] using certificate
  have checked := RegistrationNativePairedMaterialSource.safe RegistrationNativeSecretWordMessage.zero _ raw
  have original := congrArg (simulateQ (liftLocal (n := n) (KemSK := KemSK) false))
    (RegistrationNativeSecretWordBeaconMaterial.complete_source (KemSK := KemSK) RegistrationNativeSecretWordMessage.zero
      source owner current (literalReady ready) env)
  rw [eval_literal] at original
  simp only [QueryImpl.simulateQ_compose] at original
  have closed : simulateQ (liftLocal (n := n) (KemSK := KemSK) false)
      (simulateQ RegistrationBeaconReferenceFinish.service
        (simulateQ (RegistrationNativeSecretWordServerMaterial.realize RegistrationNativeSecretWordMessage.zero)
          (((RegistrationNativeSecretWordBeaconMaterial.complete (n := n) source owner (literalReady ready)).run current).run env))) =
      simulateQ (nativeLift (n := n) (KemSK := KemSK))
        (simulateQ (RegistrationNativeSecretWordServerMaterial.realize RegistrationNativeSecretWordMessage.zero)
          (((RegistrationNativeSecretWordBeaconMaterial.complete (n := n) source owner (literalReady ready)).run current).run env)) := by
    rw [← QueryImpl.simulateQ_compose, service]
  rw [closed] at original
  rw [← original]
  exact checked
private def routing {ι : Type} {base : OracleSpec ι} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (scalar : Option PqxdhJointGapDh.ScalarBytes) :
    QueryImpl (RegistrationNativePublicFrontend.LocalSpec n KemSK) (OracleComp (RegistrationNativePublicFrontend.Spec n KemSK)) :=
  match scalar with
  | none => liftLocal false
  | some scalar => (liftLocal false) ∘ₛ RegistrationNativePublicOwners.ordinary setup scalar

private theorem routed_service {ι : Type} {base : OracleSpec ι} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (scalar : Option PqxdhJointGapDh.ScalarBytes) :
    (routing (n := n) setup scalar) ∘ₛ RegistrationBeaconReferenceFinish.service = (nativeLift (n := n) (KemSK := KemSK)) := by
  cases scalar with
  | none => exact service
  | some scalar =>
      funext query
      simp only [routing, QueryImpl.compose, RegistrationBeaconReferenceFinish.service,
        simulateQ_spec_query, RegistrationNativePublicOwners.ordinary, liftLocal, nativeLift]

private theorem routing_bound {ι : Type} {base : OracleSpec ι} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (role : PqxdhRecordLiftInterface.Role) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativePublicFrontend.LocalSpec n KemSK) Value)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordAtomOwnerInstallPrefix.NativeInstall (KemSK := KemSK) role) 0) :
    (simulateQ (routing setup scalar) work).IsQueryBoundP (RegistrationNativePairedSafe.GlobalInstall (KemSK := KemSK) role) 0 := by
  cases scalar with
  | none => exact RegistrationNativePairedSafe.local_bound role false work 0 bounded
  | some scalar =>
      simp only [routing, QueryImpl.simulateQ_compose]
      apply RegistrationNativePairedSafe.local_bound role false _ 0
      apply RawCtxSourceOpen.simulate_bound _ _ _ work 0 bounded
      intro query
      cases query with
      | inl message =>
          simp only [RegistrationNativePublicOwners.ordinary, RegistrationNativeSecretWordAtomOwnerInstallPrefix.NativeInstall]
          split <;> simp [RegistrationNativeSecretWordAtomOwnerInstallPrefix.NativeInstall, isQueryBoundP_query_iff]
      | inr query =>
          simp only [RegistrationNativePublicOwners.ordinary, isQueryBoundP_query_iff]
          intro counted
          rw [ite_eq_left counted]
          decide

/-- The actual complete native Beacon material continuation preserves the paired monitor for arbitrary source material choices. -/
theorem routed_complete {ι : Type} {base : OracleSpec ι} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (scalar : Option PqxdhJointGapDh.ScalarBytes) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (ready : RegistrationBeaconReferenceRoot.Ready) (env : EnvState Auxiliary) :
    Safe (simulateQ (routing (n := n) setup scalar)
      (((RegistrationBeaconReferenceFinish.complete (n := n) (KemSK := KemSK) source owner ready).run current).run env)) := by
  have certificate := RegistrationNativeSecretWordPairedBeacon.complete (n := n) (KemSK := KemSK) source owner current (literalReady ready) env
  have raw : RegistrationNativeSecretWordPairedTrace.Safe (simulateQ (wordLift (n := n) (KemSK := KemSK))
      (((RegistrationNativeSecretWordBeaconMaterial.complete (n := n) source owner (literalReady ready)).run current).run env)) := by
    simpa only [RegistrationNativeSecretWordPairedBeacon.compile, wordLift, QueryImpl.simulateQ_compose] using certificate
  have checked := RegistrationNativePairedMaterialSource.safe RegistrationNativeSecretWordMessage.zero _ raw
  have original := congrArg (simulateQ (routing (n := n) setup scalar))
    (RegistrationNativeSecretWordBeaconMaterial.complete_source (KemSK := KemSK) RegistrationNativeSecretWordMessage.zero
      source owner current (literalReady ready) env)
  rw [eval_literal] at original
  simp only [QueryImpl.simulateQ_compose] at original
  have closed : simulateQ (routing (n := n) setup scalar)
      (simulateQ RegistrationBeaconReferenceFinish.service
        (simulateQ (RegistrationNativeSecretWordServerMaterial.realize RegistrationNativeSecretWordMessage.zero)
          (((RegistrationNativeSecretWordBeaconMaterial.complete (n := n) source owner (literalReady ready)).run current).run env))) =
      simulateQ (nativeLift (n := n) (KemSK := KemSK))
        (simulateQ (RegistrationNativeSecretWordServerMaterial.realize RegistrationNativeSecretWordMessage.zero)
          (((RegistrationNativeSecretWordBeaconMaterial.complete (n := n) source owner (literalReady ready)).run current).run env)) := by
    rw [← QueryImpl.simulateQ_compose, routed_service setup scalar]
  rw [closed] at original
  rw [← original]
  exact checked
private theorem mapped {Result : Type} (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (observe : Value → Result)
    (safe : Safe work) : Safe (observe <$> work) := by
  rw [map_eq_bind_pure_comp]
  exact RegistrationNativePairedTrace.bind_safe work _ safe (fun value => RegistrationNativePairedTrace.pure_safe (observe value))

private theorem map_apply {Private Value Result : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : Value → Result) (work : StateT Private m Value) (before : Private) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

/-- Both selected and ordinary actual incoming finish programs preserve the same paired monitor, including all terminal and authentication failures. -/
theorem local_finish {ι : Type} {base : OracleSpec ι} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (source : RegistrationNativeMldsa.Source) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (packet : Option registration.ResponsePacket) (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Safe (simulateQ (routing setup scalar)
      (((RegistrationBeaconReferenceFinish.finish (n := n) setup source packet).run owner).run env)) := by
  simp only [RegistrationBeaconReferenceFinish.finish, StateT.run_bind, StateT.run_get, pure_bind]
  cases phase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ =>
      exact RegistrationNativePairedTrace.pure_safe _
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error | div =>
          simp only [moved, StateT.run_pure, simulateQ_pure]
          exact RegistrationNativePairedTrace.pure_safe _
      | ok aborted =>
          simp only [moved, StateT.run_bind, simulateQ_bind]
          apply RegistrationNativePairedTrace.bind_safe _ _
            (RegistrationNativePairedSafe.free _ (fun role =>
              routing_bound setup role scalar _
                (RegistrationNativePairedBeaconPrefix.preparation_free role setup source packet owner env)))
          rintro ⟨⟨prepared, current⟩, reachedEnv⟩
          cases prepared with
          | fail error | div =>
              apply RegistrationNativePairedSafe.free
              intro role
              apply routing_bound setup role scalar _
              simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                (RegistrationNativePairedBeaconPrefix.abort_free role (KemSK := KemSK) owner current reachedEnv)
          | ok prepared => cases prepared with
            | none =>
                apply RegistrationNativePairedSafe.free
                intro role
                apply routing_bound setup role scalar _
                simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                  (RegistrationNativePairedBeaconPrefix.abort_free role (KemSK := KemSK) owner current reachedEnv)
            | some ready =>
                exact routed_complete setup scalar setup.source owner current ready reachedEnv

/-- The actual mixed owner-roster finish keeps every attempted hidden installation attached to its own just-demanded slot. -/
theorem owners {ι : Type} {base : OracleSpec ι} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (source : RegistrationNativeMldsa.Source) (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Safe (simulateQ (liftLocal false)
      (((RegistrationNativePublicOwners.finish (n := n) setup source index packet).run owners).run env)) := by
  simp only [RegistrationNativePublicOwners.finish, StateT.run]
  cases found : owners[index]? with
  | none =>
      simp only [simulateQ_pure]
      exact RegistrationNativePairedTrace.pure_safe _
  | some owner =>
      simp only [simulateQ_map]
      apply mapped
      cases scalarState : owner.scalar with
      | none => exact local_finish setup source none packet owner.view env
      | some scalar =>
          simpa only [routing, QueryImpl.simulateQ_compose, StateT.run] using
            local_finish setup source (some scalar) packet owner.view env

end BeaconcryptCore.Computational.RegistrationNativePairedBeacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedBeacon.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedBeacon.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedBeacon.routed_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedBeacon.routed_complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedBeacon.local_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedBeacon.local_finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedBeacon.owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedBeacon.owners
