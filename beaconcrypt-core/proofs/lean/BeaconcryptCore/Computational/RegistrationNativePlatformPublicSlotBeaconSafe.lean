-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconRawFree
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotEnvSuffix
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotEffects
/-! The actual corrected Beacon material continuation has one possible install using its actual returned material slot. Raw opening, source journals, abort updates and failed insertion replies remain on the same tree. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBeaconSafe
open PqxdhRecordLiftInterface (Role EnvEffects KernelRef)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativePlatformPublicSlotKind (Effect Kernel)
open RegistrationNativeSecretWordAtomInstallCaps (InstallEnv)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
variable {n : Nat} {Auxiliary A B : Type} {source : RegistrationNativeMldsa.Source}

private theorem mapped {I A B : Type} {spec : OracleSpec I} (work : OracleComp spec A) (observe : A → B)
    (predicate : I → Prop) (prior : work.AllQueriesSatisfy predicate) :
    (observe <$> work).AllQueriesSatisfy predicate := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind prior (fun _ => trivial)

private theorem free_allowed (choice : Choice n) (work : OracleComp (EnvEffects n) A)
    (free : ∀ role, work.IsQueryBoundP (InstallEnv role) 0) : work.AllQueriesSatisfy (Effect .beacon choice) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    have head := fun role => (isQueryBoundP_query_bind_iff _ _ _ _).mp (free role)
    refine ⟨?_, fun reply => ih reply (fun role => by simpa only [Nat.zero_sub, ite_self] using (head role).2 reply)⟩
    have absent : ∀ role, ¬ InstallEnv role query := fun role => (head role).1.resolve_right (by omega)
    cases query with
    | inl coin => trivial
    | inr capability => cases capability with
      | installServer keyId binding kernel => exact (absent .server rfl).elim
      | installBeacon owner shell kernel => exact (absent .beacon rfl).elim
      | _ => trivial

private theorem map_apply {S V W : Type} {m : Type → Type} [Monad m] [LawfulMonad m] (change : V → W) (work : StateT S m V) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before
private theorem lift_apply {S V : Type} {m : Type → Type} [Monad m] [LawfulMonad m] (work : m V) (before : S) :
    (StateT.lift work : StateT S m V) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

private theorem pure_apply {S V : Type} (value : V) (before : S) :
    (pure value : StateT S (OracleComp (EnvEffects n)) V) before = pure (value, before) := rfl

private theorem after_run (owner : Nat) (kernel : registration.CompletedBeacon → KernelRef n)
    (result : RustM RegistrationBeaconRecordExecutor.Result) (before : EnvState Auxiliary) :
    (RegistrationNativePlatformPairedBeaconService.after (fun query => StateT.lift ((EnvEffects n).query query : OracleComp (EnvEffects n) _)) owner kernel result).run before =
      (fun reply => (reply, before)) <$> RegistrationNativePlatformPairedBeaconService.after (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner kernel result := by
  cases result with
  | fail error | div => simp only [RegistrationNativePlatformPairedBeaconService.after, StateT.run_pure, map_pure]
  | ok result => cases result with
    | Err previous => simp only [RegistrationNativePlatformPairedBeaconService.after, StateT.run_pure, map_pure]
    | Ok completed =>
      simp only [RegistrationNativePlatformPairedBeaconService.after, StateT.run, QueryImpl.ofLift]
      rfl


variable (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)

private theorem beacon_allowed (owner : Nat) (choice : Choice n)
    (kernel : beaconcrypt_core.registration.CompletedBeacon → PqxdhRecordLiftInterface.KernelRef n)
    (compatible : ∀ completed, Kernel choice (kernel completed))
    (result : RustM RegistrationBeaconRecordExecutor.Result) :
    (RegistrationNativePlatformPairedBeaconService.after (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner kernel result).AllQueriesSatisfy
      (Effect .beacon choice) := by
  cases result with
  | fail error | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok completed =>
      simp only [RegistrationNativePlatformPairedBeaconService.after, QueryImpl.ofLift]
      rw [allQueriesSatisfy_query_bind_iff]
      exact ⟨⟨rfl, compatible completed⟩, fun _ => by trivial⟩

private theorem branch_facts (owner : Nat) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (choice : Choice n) (before : EnvState Auxiliary) :
    let work := (RegistrationNativePlatformPairedBeaconOwner.publicBranch crypto
      (RegistrationBeaconChargedSource.primitive
        (RegistrationBeaconMaterialRead.read (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) crypto writer))
      (fun query => StateT.lift ((EnvEffects n).query query : OracleComp (EnvEffects n) _)) owner descriptor choice).run before
    work.IsQueryBoundP (InstallEnv .beacon) 1 ∧ work.AllQueriesSatisfy (Effect .beacon choice) := by
  cases choice with
  | known output =>
    simp only [RegistrationNativePlatformPairedBeaconOwner.publicBranch, RegistrationNativePlatformPairedBeaconOwner.knownStage, StateT.run_bind]
    constructor
    · apply isQueryBoundP_bind (n := 0) (m := 1) (RegistrationNativePlatformPairedBeaconRawFree.program_free crypto writer .beacon _ before)
      intro reached _
      rw [after_run, isQueryBoundP_map_iff]
      exact RegistrationNativePlatformPairedInstallFacts.beacon_bound .beacon owner _ reached.1
    · apply allQueriesSatisfy_bind (free_allowed (.known output) _ (fun role => RegistrationNativePlatformPairedBeaconRawFree.program_free crypto writer role _ before))
      intro reached
      rw [after_run]
      exact mapped _ _ _ (beacon_allowed owner (.known output) (fun completed => .known completed.kernel) (fun _ => rfl) reached.1)
  | hidden reference =>
    simp only [RegistrationNativePlatformPairedBeaconOwner.publicBranch, RegistrationNativePlatformPairedBeaconOwner.publicHidden, RegistrationNativePlatformPairedBeaconOwner.hiddenStage, StateT.run_bind]
    constructor
    · apply isQueryBoundP_bind (n := 0) (m := 1) (RegistrationNativePlatformPairedBeaconRawFree.program_free crypto writer .beacon _ before)
      intro reached _
      rw [after_run, isQueryBoundP_map_iff]
      exact RegistrationNativePlatformPairedInstallFacts.beacon_bound .beacon owner _ reached.1
    · apply allQueriesSatisfy_bind (free_allowed (.hidden reference) _ (fun role => RegistrationNativePlatformPairedBeaconRawFree.program_free crypto writer role _ before))
      intro reached
      rw [after_run]
      exact mapped _ _ _ (beacon_allowed owner (.hidden reference) (fun _ => .hidden reference.slot) (fun _ => rfl) reached.1)

private theorem after_facts (choice : Choice n) (owner current : SelectedOwner source)
    (result : RustM RegistrationNativePairedBeaconService.Result) (before : EnvState Auxiliary) :
    let work := ((RegistrationNativePlatformBeaconMaterialFrontend.after (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner result).run current).run before
    work.IsQueryBoundP (InstallEnv .beacon) 0 ∧ work.AllQueriesSatisfy (Effect .beacon choice) := by
  cases result with
  | fail error | div =>
    simp only [RegistrationNativePlatformBeaconMaterialFrontend.after, RegistrationNativePlatformBeaconMaterialFrontend.abort,
      seqRight_eq_bind, StateT.run_lift, StateT.run_map, bind_pure_comp, QueryImpl.ofLift]
    constructor
    · simp [InstallEnv]
    · exact ⟨trivial, fun _ => trivial⟩
  | ok result => cases result with
    | Err previous =>
      simp only [RegistrationNativePlatformBeaconMaterialFrontend.after, RegistrationNativePlatformBeaconMaterialFrontend.abort,
        seqRight_eq_bind, StateT.run_lift, StateT.run_map, bind_pure_comp, QueryImpl.ofLift]
      constructor
      · simp [InstallEnv]
      · exact ⟨trivial, fun _ => trivial⟩
    | Ok completed =>
      simp only [RegistrationNativePlatformBeaconMaterialFrontend.after, StateT.run_bind,
        StateT.run_modify, pure_bind, StateT.run_pure]
      exact ⟨by trivial, by trivial⟩

/-- The actual whole material program has one possible Beacon install and uses the exact selected reference. -/
theorem program_facts (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (choice : Choice n) (before : EnvState Auxiliary) :
    let work := ((RegistrationNativePlatformBeaconMaterialFrontend.program crypto writer owner ready choice).run current).run before
    work.IsQueryBoundP (InstallEnv .beacon) 1 ∧ work.AllQueriesSatisfy (Effect .beacon choice) := by
  by_cases valid : RawCtxReceive.ValidFrame ready.descriptor.candidate.server_binding.identity_key_id
    (PqxdhRefinement.absBytes ready.descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame ready.descriptor)
  all_goals
    simp only [RegistrationNativePlatformBeaconMaterialFrontend.program, valid, ite_true, ite_false,
      StateT.run_bind, StateT.run_lift, RegistrationBeaconMaterialRead.charge,
      StateT.run_modify, pure_bind, bind_pure_comp, bind_map_left]
    constructor
    · exact isQueryBoundP_bind (n := 1) (m := 0) (branch_facts crypto writer owner.worldOwner ready.descriptor choice _).1
        (fun reached _ => (after_facts choice owner current reached.1 reached.2).1)
    · exact allQueriesSatisfy_bind (branch_facts crypto writer owner.worldOwner ready.descriptor choice _).2
        (fun reached => (after_facts choice owner current reached.1 reached.2).2)

variable {KemSK : Type}
/-- The literal chosen source program installs only against its own current material reply. -/
theorem chosen (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (choice : Choice n) (env : EnvState Auxiliary) (before : RegistrationNativePlatformPublicSlotKind.State n)
    (active : RegistrationNativePlatformPublicSlotSuffix.Ready choice 1 before)
    (result : ((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary) × RegistrationNativePlatformPublicSlotKind.State n)
    (supported : result ∈ support ((simulateQ RegistrationNativePlatformPublicSlotKind.handler
      (((RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer (RegistrationNativePairedCompile.effects (n := n) (KemSK := KemSK)) owner ready choice).run current).run env)).run before)) :
    result.2.bad = false := by
  change result ∈ support ((simulateQ RegistrationNativePlatformPublicSlotKind.handler
    (simulateQ RegistrationNativePairedCompile.effects
      (((RegistrationNativePlatformBeaconMaterialFrontend.program crypto writer owner ready choice).run current).run env))).run before) at supported
  exact RegistrationNativePlatformPublicSlotEnvSuffix.continuation .beacon choice _
    (program_facts crypto writer owner current ready choice env).1
    (program_facts crypto writer owner current ready choice env).2 before active result supported

/-- The actual new Beacon material demand and all its continuation outcomes are paired-safe. -/
theorem complete (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (env : EnvState Auxiliary) :
    RegistrationNativePlatformPublicSlotKind.Safe
      (((RegistrationNativePlatformBeaconMaterialFrontend.complete crypto writer
        (RegistrationNativePairedCompile.effects (n := n) (KemSK := KemSK))
        (RegistrationNativePlatformPublicSlotEffects.demand (n := n) (KemSK := KemSK)) owner ready).run current).run env) := by
  intro before result clean supported
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.complete, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, bind_map_left, simulateQ_bind] at supported
  simp only [RegistrationNativePlatformPublicSlotEffects.demand, simulateQ_spec_query,
    RegistrationNativePlatformPublicSlotKind.handler, StateT.run, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨selected, _actual, continued⟩ := supported
  have stored := RegistrationNativePlatformPublicSlotEffects.demand_step (KemSK := KemSK) ready.reference selected before
  cases selected with
  | none =>
    apply RegistrationNativePlatformPublicSlotKind.free_safe _ _ _ result (stored.1.trans clean) continued
    intro role
    simp [RegistrationNativePlatformBeaconMaterialFrontend.abort, seqRight_eq_bind,
      bind_pure_comp, map_apply, lift_apply, Functor.map_map, isQueryBoundP_map_iff,
      RegistrationNativePairedCompile.effects, RegistrationNativePairedSafe.GlobalInstall,
      RegistrationNativeSecretWordAtomInstallCaps.Install, InstallEnv]
  | some choice =>
    exact chosen crypto writer owner current ready choice env _
      ⟨stored.1.trans clean, Or.inr stored.2⟩ result continued
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBeaconSafe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBeaconSafe.program_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBeaconSafe.program_facts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBeaconSafe.chosen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBeaconSafe.chosen

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBeaconSafe.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBeaconSafe.complete
