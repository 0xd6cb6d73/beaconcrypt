-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedSafe
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconMaterial
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerInstallPrefix
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerSource

/-! The actual Beacon material stage emits raw Common callbacks. Its own demand establishes the exact descriptor before any installation attempt; publication/opening failures and stale prior trace metadata remain present. No Common-compiler environment is substituted for this direct paired controller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedBeacon
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeSecretWordMessage (Message BeaconReady)
open RegistrationNativeSecretWordInterface (Spec LocalSpec liftLocal paired common)
open RegistrationNativeSecretWordPairedTrace (State handler Safe step)
open RegistrationNativeSecretWordFrontendTrace (begin finish)
open RegistrationNativeSecretWordAtomInstallTrace (RootFree atom count)
open RegistrationNativeSecretWordAtomInstallPredicate (GlobalInstall)
open RegistrationNativeSecretWordAtomInstallCaps (Install)
variable {n : Nat} {KemSK Value Auxiliary : Type}

noncomputable def compile (work : OracleComp (RegistrationNativeSecretWordBeaconMaterial.Spec n) Value) : OracleComp (Spec n KemSK) Value :=
  simulateQ (liftLocal false) (simulateQ paired work)

private def rawCommon : QueryImpl (RegistrationNativePairedServerService.Common n) (OracleComp (Spec n KemSK)) :=
  (liftLocal false) ∘ₛ (common (KemSK := KemSK))

private theorem common_bound (role : Role) (work : OracleComp (RegistrationNativePairedServerService.Common n) Value)
    (cap : Nat) (bounded : work.IsQueryBoundP (Install role) cap) :
    (simulateQ (rawCommon (KemSK := KemSK)) work).IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work cap bounded
  intro query
  simp [rawCommon, QueryImpl.compose, common, liftLocal, GlobalInstall, isQueryBoundP_query_iff]
  intro counted
  rw [ite_eq_left counted]
  decide

private theorem common_quiet (work : OracleComp (RegistrationNativePairedServerService.Common n) Value) :
    (simulateQ (rawCommon (KemSK := KemSK)) work).IsQueryBoundP (fun query => ¬RootFree (KemSK := KemSK) query) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [rawCommon, QueryImpl.compose, common, liftLocal, RootFree, isQueryBoundP_query_iff]

private theorem common_allowed (role : Role) (choice : RegistrationNativePairedChoice.Choice n)
    (work : OracleComp (RegistrationNativePairedServerService.Common n) Value)
    (allowed : AllQueriesSatisfy work (RegistrationNativePairedProvenance.Allowed role choice)) :
    AllQueriesSatisfy (simulateQ (rawCommon (KemSK := KemSK)) work)
      (RegistrationNativeSecretWordPairedSafe.Allowed (KemSK := KemSK) role choice) := by
  apply RegistrationNativeHiddenAllocationCore.simulation _ _ _ _ work allowed
  intro query valid
  cases query with
  | inl publication => exact (allQueriesSatisfy_query_iff _ _).mpr trivial
  | inr environment => exact (allQueriesSatisfy_query_iff _ _).mpr valid

private theorem common_compile (work : OracleComp (RegistrationNativePairedServerService.Common n) Value) :
    compile (KemSK := KemSK) (simulateQ RegistrationNativeSecretWordServerMaterial.commonLift work) =
      simulateQ (rawCommon (KemSK := KemSK)) work := by
  unfold compile
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  rfl

private theorem admitted_run (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (message : Message) :
    compile (KemSK := KemSK) (RegistrationNativeSecretWordBeaconMaterial.admitted (n := n) source owner sender descriptor message) = (do
      let chosen ← ((Spec n KemSK).query (.inl (.inr (.inl (.inl message)))) : OracleComp (Spec n KemSK) (Option (RegistrationNativePairedChoice.Choice n)))
      match chosen with
      | none => pure (.ok (.Err ⟨sender⟩))
      | some choice => simulateQ rawCommon (RegistrationNativePairedBeaconService.publicBranch source owner sender descriptor choice)) := by
  simp only [compile, RegistrationNativeSecretWordBeaconMaterial.admitted, simulateQ_bind, simulateQ_spec_query,
    paired, liftLocal]
  apply bind_congr
  intro chosen
  cases chosen with
  | none => rfl
  | some choice => exact common_compile _

/-- The actual Beacon demand records its returned choice before its sole possible matching-role installation. -/
theorem admitted (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (reference : Message) :
    Safe (compile (n := n) (KemSK := KemSK)
      (RegistrationNativeSecretWordBeaconMaterial.admitted source owner sender descriptor reference)) := by
  intro trace result clean supported
  rw [admitted_run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
  simp only [handler, StateT.run, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨chosen, _possible, continued⟩ := supported
  cases chosen with
  | none =>
      exact RegistrationNativeSecretWordPairedTrace.pure_safe _ _ result
        (by simp only [step, RegistrationNativeSecretWordPairedTrace.Fits, decide_true, Bool.not_true, Bool.or_false, clean]) continued
  | some choice =>
      apply RegistrationNativeSecretWordPairedSafe.suffix .beacon choice reference _ 1 (by omega)
        ((common_bound .beacon _ _ (RegistrationNativeSecretWordAtomInstallCaps.beacon_branch .beacon source owner sender descriptor choice)).mono (by simp))
        (common_quiet _) (common_allowed .beacon choice _ (RegistrationNativePairedProvenance.beacon_branch source owner sender descriptor choice))
        (step (.inl (.inr (.inl (.inl reference)))) (some choice) trace)
        ⟨by simp only [step, RegistrationNativeSecretWordPairedTrace.Fits, decide_true, Bool.not_true, Bool.or_false, clean], Or.inr ⟨rfl, rfl⟩⟩ result continued

private theorem compile_pure (value : Value) : compile (n := n) (KemSK := KemSK) (pure value) = pure value := by
  simp only [compile, simulateQ_pure]

private theorem compile_bind {Result : Type}
    (work : OracleComp (RegistrationNativeSecretWordBeaconMaterial.Spec n) Value)
    (next : Value → OracleComp (RegistrationNativeSecretWordBeaconMaterial.Spec n) Result) :
    compile (KemSK := KemSK) (work >>= next) = (compile work >>= fun value => compile (next value)) := by
  simp only [compile, simulateQ_bind]

private theorem map_apply {Private Value Result : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : Value → Result) (work : StateT Private m Value) (before : Private) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private noncomputable def after {source : RegistrationNativeMldsa.Source}
    (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (published : RustM RegistrationNativePairedBeaconService.Result) :
    OracleComp (RegistrationNativeSecretWordBeaconMaterial.Spec n)
      ((RustM (Option Pqxdh.Bytes) × RegistrationBeaconReferenceCompiler.SelectedOwner source) × RegistrationWorldAgreementCompiler.EnvState Auxiliary) :=
  match published with
  | .fail error => (((RegistrationNativeSecretWordBeaconMaterial.abort owner *> pure (.fail error)).run current).run env)
  | .div => (((RegistrationNativeSecretWordBeaconMaterial.abort owner *> pure .div).run current).run env)
  | .ok (.Err _) => (((RegistrationNativeSecretWordBeaconMaterial.abort owner *> pure (.ok none)).run current).run env)
  | .ok (.Ok completed) => pure ((.ok (some (TranscriptAuthParts.absSlice completed.application)),
      { current with phase := .established completed }), env)

private theorem complete_run (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner mlSource)
    (ready : BeaconReady) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    (((RegistrationNativeSecretWordBeaconMaterial.complete (n := n) source owner ready).run current).run env) = (do
      let published ← RegistrationNativeSecretWordBeaconMaterial.admitted source owner.worldOwner owner.pin.binding.identity_key_id ready.descriptor ready.reference
      after owner current env published) := by
  simp only [RegistrationNativeSecretWordBeaconMaterial.complete, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, bind_map_left]
  apply bind_congr
  intro published
  cases published with
  | fail error | div => rfl
  | ok published => cases published <;> rfl

private theorem abort_free (role : Role) {source : RegistrationNativeMldsa.Source}
    (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    (compile (n := n) (KemSK := KemSK)
      (((RegistrationNativeSecretWordBeaconMaterial.abort owner).run current).run env)).IsQueryBoundP
      (GlobalInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationNativeSecretWordBeaconMaterial.abort, bind_pure_comp]
  simp [compile, RegistrationNativeSecretWordBeaconMaterial.effect, paired, liftLocal,
    GlobalInstall, Install, RegistrationNativeSecretWordAtomInstallCaps.InstallEnv,
    isQueryBoundP_query_iff, isQueryBoundP_map_iff]

private theorem after_free (role : Role) {source : RegistrationNativeMldsa.Source}
    (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (published : RustM RegistrationNativePairedBeaconService.Result) :
    (compile (n := n) (KemSK := KemSK) (after owner current env published)).IsQueryBoundP
      (GlobalInstall (KemSK := KemSK) role) 0 := by
  cases published with
  | fail error | div =>
      simpa only [after, seqRight_eq_bind, bind_pure_comp, StateT.run_map, StateT.run, map_apply,
        compile, simulateQ_map, isQueryBoundP_map_iff] using abort_free role (n := n) (KemSK := KemSK) owner current env
  | ok published => cases published with
    | Err rejected =>
        simpa only [after, seqRight_eq_bind, bind_pure_comp, StateT.run_map, StateT.run, map_apply,
          compile, simulateQ_map, isQueryBoundP_map_iff] using abort_free role (n := n) (KemSK := KemSK) owner current env
    | Ok completed => trivial

/-- Every actual Beacon material completion installs only its own last returned paired hidden slot. -/
theorem complete (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner mlSource)
    (ready : BeaconReady) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Safe (compile (n := n) (KemSK := KemSK)
      (((RegistrationNativeSecretWordBeaconMaterial.complete source owner ready).run current).run env)) := by
  rw [complete_run, compile_bind]
  apply RegistrationNativeSecretWordPairedTrace.bind_safe _ _
    (admitted source owner.worldOwner owner.pin.binding.identity_key_id ready.descriptor ready.reference)
  intro published
  exact RegistrationNativeSecretWordPairedSafe.free _ (fun role => after_free role owner current env published)

private theorem mapped {Result : Type} (work : OracleComp (Spec n KemSK) Value) (observe : Value → Result)
    (safe : Safe work) : Safe (observe <$> work) := by
  rw [map_eq_bind_pure_comp]
  exact RegistrationNativeSecretWordPairedTrace.bind_safe work _ safe (fun value => RegistrationNativeSecretWordPairedTrace.pure_safe (observe value))

private theorem routing_paired {ι : Type} {base : OracleSpec ι} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (scalar : Option PqxdhJointGapDh.ScalarBytes) (work : OracleComp (RegistrationNativeSecretWordBeaconMaterial.Spec n) Value) :
    simulateQ (RegistrationNativeSecretWordAtomOwnerSource.routing setup scalar) (simulateQ paired work) = compile (KemSK := KemSK) work := by
  unfold compile
  cases scalar with
  | none => rfl
  | some scalar =>
      simp only [RegistrationNativeSecretWordAtomOwnerSource.routing, QueryImpl.simulateQ_compose]
      congr 1
      rw [← QueryImpl.simulateQ_compose]
      rfl

/-- Both selected and ordinary actual incoming finish programs preserve the same paired monitor, including all terminal and authentication failures. -/
theorem local_finish {ι : Type} {base : OracleSpec ι} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (source : RegistrationNativeMldsa.Source) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (packet : Option registration.ResponsePacket) (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Safe (simulateQ (RegistrationNativeSecretWordAtomOwnerSource.routing setup scalar)
      (((RegistrationNativeSecretWordBeaconCompiler.finish (n := n) setup source packet).run owner).run env)) := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.finish, StateT.run_bind, StateT.run_get, pure_bind]
  cases phase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ =>
      exact RegistrationNativeSecretWordPairedTrace.pure_safe _
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error | div =>
          simp only [moved, StateT.run_pure, simulateQ_pure]
          exact RegistrationNativeSecretWordPairedTrace.pure_safe _
      | ok aborted =>
          simp only [moved, StateT.run_bind, simulateQ_bind]
          apply RegistrationNativeSecretWordPairedTrace.bind_safe _ _
            (RegistrationNativeSecretWordPairedSafe.free _ (fun role =>
              RegistrationNativeSecretWordAtomOwnerSource.routing_bound setup role scalar _ 0
                (RegistrationNativeSecretWordAtomOwnerInstallPrefix.preparation_free role setup source packet owner env)))
          rintro ⟨⟨prepared, current⟩, reachedEnv⟩
          cases prepared with
          | fail error | div =>
              apply RegistrationNativeSecretWordPairedSafe.free
              intro role
              apply RegistrationNativeSecretWordAtomOwnerSource.routing_bound setup role scalar _ 0
              simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                (RegistrationNativeSecretWordAtomOwnerInstallPrefix.abort_free role (KemSK := KemSK) owner current reachedEnv)
          | ok prepared => cases prepared with
            | none =>
                apply RegistrationNativeSecretWordPairedSafe.free
                intro role
                apply RegistrationNativeSecretWordAtomOwnerSource.routing_bound setup role scalar _ 0
                simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                  (RegistrationNativeSecretWordAtomOwnerInstallPrefix.abort_free role (KemSK := KemSK) owner current reachedEnv)
            | some ready =>
                simp only [RegistrationNativeSecretWordBeaconCompiler.complete, StateT.run, routing_paired]
                exact complete setup.source owner current ready reachedEnv

/-- The actual mixed owner-roster finish keeps every attempted hidden installation attached to its own just-demanded slot. -/
theorem owners {ι : Type} {base : OracleSpec ι} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (source : RegistrationNativeMldsa.Source) (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Safe (simulateQ (liftLocal false)
      (((RegistrationNativeSecretWordOwners.finish (n := n) setup source index packet).run owners).run env)) := by
  simp only [RegistrationNativeSecretWordOwners.finish, StateT.run]
  cases found : owners[index]? with
  | none =>
      simp only [simulateQ_pure]
      exact RegistrationNativeSecretWordPairedTrace.pure_safe _
  | some owner =>
      simp only [simulateQ_map]
      apply mapped
      cases scalarState : owner.scalar with
      | none => exact local_finish setup source none packet owner.view env
      | some scalar =>
          simpa only [RegistrationNativeSecretWordAtomOwnerSource.routing, QueryImpl.simulateQ_compose, StateT.run] using
            local_finish setup source (some scalar) packet owner.view env

end BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedBeacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedBeacon.admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedBeacon.admitted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedBeacon.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedBeacon.complete
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedBeacon.local_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedBeacon.local_finish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedBeacon.owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedBeacon.owners
