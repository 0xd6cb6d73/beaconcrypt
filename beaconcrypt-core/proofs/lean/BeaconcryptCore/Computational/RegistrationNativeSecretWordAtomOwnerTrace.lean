-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallTrace
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconMaterial

/-! The actual Beacon material stage emits raw Common callbacks. Its own demand establishes the exact descriptor before any installation attempt; publication/opening failures and stale prior trace metadata remain present. No Common-compiler environment is substituted for this direct paired controller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerTrace
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeSecretWordMessage (Message BeaconReady)
open RegistrationNativeSecretWordInterface (Spec LocalSpec liftLocal paired common)
open RegistrationNativeSecretWordFrontendTrace (State handler begin finish)
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

private theorem common_trace (role : Role) (work : OracleComp (RegistrationNativePairedServerService.Common n) Value)
    (cap : Nat) (bounded : work.IsQueryBoundP (Install role) cap)
    (trace : State) (result : Value × State)
    (supported : result ∈ support ((simulateQ handler (simulateQ (rawCommon (KemSK := KemSK)) work)).run trace)) :
    count role result.2 ≤ count role trace + cap * atom trace.current :=
  (RegistrationNativeSecretWordAtomInstallTrace.program role _ cap (common_bound role work cap bounded)
    (common_quiet work) trace result supported).2

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

/-- The same actual incoming descriptor funds at most one own-role attempt after its demand, irrespective of the prior current descriptor. -/
theorem admitted (role : Role) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (reference : Message) (trace : State) (result : RustM RegistrationNativePairedBeaconService.Result × State)
    (supported : result ∈ support ((simulateQ handler
      (compile (n := n) (KemSK := KemSK) (RegistrationNativeSecretWordBeaconMaterial.admitted source owner sender descriptor reference))).run trace)) :
    count role result.2 ≤ count role trace + (if role = .beacon then 1 else 0) * atom (some reference) := by
  rw [admitted_run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
  simp only [handler, StateT.run, begin, finish, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨chosen, _possible, continued⟩ := supported
  cases chosen with
  | none =>
      change result ∈ support (pure (.ok (.Err ⟨sender⟩), ⟨some reference, trace.events ++ [.demand reference]⟩) : OracleComp (Spec n KemSK) _) at continued
      rw [mem_support_pure_iff] at continued
      cases continued
      simp only [count, List.countP_append, List.countP_singleton,
        RegistrationNativeSecretWordAtomInstallTrace.attempt, Bool.false_eq_true, ite_false, Nat.add_zero]
      omega
  | some choice =>
      change result ∈ support ((simulateQ handler
        (simulateQ rawCommon (RegistrationNativePairedBeaconService.publicBranch source owner sender descriptor choice))).run
          ⟨some reference, trace.events ++ [.demand reference]⟩) at continued
      have bounded := common_trace role _ _
        (RegistrationNativeSecretWordAtomInstallCaps.beacon_branch role source owner sender descriptor choice)
        ⟨some reference, trace.events ++ [RegistrationNativeSecretWordFrontendTrace.Event.demand reference]⟩ result continued
      simpa only [count, List.countP_append, List.countP_singleton,
        RegistrationNativeSecretWordAtomInstallTrace.attempt, Bool.false_eq_true, ite_false, Nat.add_zero] using bounded

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

/-- Actual direct paired completion can add only its one Beacon attempt, funded by the same newly demanded descriptor. -/
theorem complete (role : Role) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner mlSource)
    (ready : BeaconReady) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (trace : State)
    (result : ((RustM (Option Pqxdh.Bytes) × RegistrationBeaconReferenceCompiler.SelectedOwner mlSource) × RegistrationWorldAgreementCompiler.EnvState Auxiliary) × State)
    (supported : result ∈ support ((simulateQ handler (compile (n := n) (KemSK := KemSK)
      (((RegistrationNativeSecretWordBeaconMaterial.complete source owner ready).run current).run env))).run trace)) :
    count role result.2 ≤ count role trace + (if role = .beacon then 1 else 0) * atom (some ready.reference) := by
  rw [complete_run, compile_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨published, material, settled⟩ := supported
  have first := admitted role source owner.worldOwner owner.pin.binding.identity_key_id ready.descriptor ready.reference trace published material
  have last := RegistrationNativeSecretWordAtomInstallTrace.free role _
    (after_free role owner current env published.1) published.2 result settled
  exact last.trans first

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerTrace.admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerTrace.admitted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerTrace.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerTrace.complete
