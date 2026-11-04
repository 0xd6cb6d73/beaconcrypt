-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomEffects
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconSafe
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinish
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerSource
/-! The actual corrected Beacon material completion retains its real first-record program, assigned identifier, record journal and failure states. Its same material demand funds at most one chronological attempt of the Beacon role, including either optional scalar route. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomBeaconTrace
open PqxdhRecordLiftInterface (EnvEffects Role)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativePlatformBoundCompiler (PublicState)
open RegistrationNativeSecretWordFrontendTrace (State handler)
open RegistrationNativeSecretWordAtomInstallTrace (count atom)
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeSecretWordMessage (BeaconReady)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {I KemSK Auxiliary A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem effect_route (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes) :
    RegistrationNativeSecretWordAtomOwnerSource.routing (n := n) setup scalar ∘ₛ
      RegistrationNativeSecretWordInterface.effect = RegistrationNativePlatformSecretWordAtomEffects.env := by
  cases scalar with
  | none => rfl
  | some scalar =>
    funext query
    simp only [RegistrationNativeSecretWordAtomOwnerSource.routing, QueryImpl.apply_compose,
      RegistrationNativeSecretWordInterface.effect, simulateQ_spec_query, RegistrationNativeSecretWordOwners.ordinary,
      RegistrationNativePlatformSecretWordAtomEffects.env]

private theorem env_program (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (EnvEffects n) A) :
    simulateQ (RegistrationNativeSecretWordAtomOwnerSource.routing setup scalar)
      (simulateQ RegistrationNativeSecretWordInterface.effect work) =
      simulateQ RegistrationNativePlatformSecretWordAtomEffects.env work := by
  rw [← QueryImpl.simulateQ_compose, effect_route]

noncomputable def compile (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : StateT (EnvState Auxiliary) (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)) A)
    (before : EnvState Auxiliary) : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) (A × EnvState Auxiliary) :=
  simulateQ (RegistrationNativeSecretWordAtomOwnerSource.routing setup scalar) (work.run before)

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map _ _ _
private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (StateT.lift work : StateT S m X) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

private theorem demand_run (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (message : RegistrationNativeSecretWordMessage.Message) :
    RegistrationNativeSecretWordAtomOwnerSource.routing (n := n) setup scalar (.inr (.inl (.inl message))) =
      (RegistrationNativeSecretWordInterface.Spec n KemSK).query (.inl (.inr (.inl (.inl message)))) := by
  cases scalar with
  | none => rfl
  | some scalar => rfl

private theorem program_bound (role : Role) (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready) (choice : Choice n) (before : EnvState Auxiliary) :
    (((RegistrationNativePlatformBeaconMaterialFrontend.program crypto writer owner ready choice).run current).run before).IsQueryBoundP
      (RegistrationNativeSecretWordAtomInstallCaps.InstallEnv role) (if role = .beacon then 1 else 0) := by
  have facts := RegistrationNativePlatformPairedBeaconSafe.program_facts crypto writer owner current ready choice before
  cases role with
  | beacon => simpa using facts.1
  | server =>
    classical
    have rejected := (isQueryBoundP_zero_iff _ (RegistrationNativePairedProvenance.Effect .beacon choice)).2 facts.2
    apply rejected.of_imp
    intro query installed good
    cases query with
    | inl coin => cases installed
    | inr capability => cases capability <;> simp_all [RegistrationNativeSecretWordAtomInstallCaps.InstallEnv,
      RegistrationNativePairedProvenance.Effect]

private theorem chosen_run (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready) (choice : Choice n) (before : EnvState Auxiliary) :
    compile setup scalar ((RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer
      RegistrationNativeSecretWordInterface.effect owner ready choice).run current) before =
    simulateQ RegistrationNativePlatformSecretWordAtomEffects.env
      (((RegistrationNativePlatformBeaconMaterialFrontend.program crypto writer owner ready choice).run current).run before) :=
  env_program setup scalar _

private theorem abort_bound (role : Role) (owner current : SelectedOwner source) (before : EnvState Auxiliary) :
    (((RegistrationNativePlatformBeaconMaterialFrontend.abort (RegistrationNativeSecretWordInterface.effect (n := n) (KemSK := KemSK)) owner).run current).run before).IsQueryBoundP
      (RegistrationNativeSecretWordAtomInstallPredicate.LocalInstall (KemSK := KemSK) role) 0 := by
  simp [RegistrationNativePlatformBeaconMaterialFrontend.abort, StateT.run_lift, bind_pure_comp,
    RegistrationNativeSecretWordInterface.effect, RegistrationNativeSecretWordAtomInstallPredicate.LocalInstall,
    RegistrationNativeSecretWordAtomInstallCaps.Install, RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, isQueryBoundP_query_iff]

private theorem abort_count (role : Role) (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (owner current : SelectedOwner source) (before : EnvState Auxiliary) (trace : State)
    (result : ((Unit × SelectedOwner source) × EnvState Auxiliary) × State)
    (supported : result ∈ support ((simulateQ handler (compile (n := n) setup scalar
      ((RegistrationNativePlatformBeaconMaterialFrontend.abort RegistrationNativeSecretWordInterface.effect owner).run current) before)).run trace)) :
    count role result.2 ≤ count role trace :=
  RegistrationNativeSecretWordAtomInstallTrace.free role _
    (RegistrationNativeSecretWordAtomOwnerSource.routing_bound setup role scalar _ 0 (abort_bound role owner current before)) trace result supported

/-- The literal corrected material completion spends at most one atom attempt of its own role after its same actual demand. -/
theorem complete_count (role : Role) (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (ready : BeaconReady) (before : EnvState Auxiliary) (trace : State)
    (result : ((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary) × State)
    (supported : result ∈ support ((simulateQ handler (compile (n := n) setup scalar
      ((RegistrationNativePlatformSecretWordFinish.complete crypto writer owner ready).run current) before)).run trace)) :
    count role result.2 ≤ count role trace + (if role = .beacon then 1 else 0) * atom (some ready.reference) := by
  simp only [compile, RegistrationNativePlatformSecretWordFinish.complete, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, bind_map_left, RegistrationNativeSecretWordInterface.demand,
    simulateQ_bind, simulateQ_spec_query, demand_run, StateT.run_bind] at supported
  simp only [handler, StateT.run, RegistrationNativeSecretWordFrontendTrace.begin,
    RegistrationNativeSecretWordFrontendTrace.finish, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨choice, _actual, supported⟩ := supported
  cases choice with
  | none =>
    simp only [seqRight_eq_bind, bind_pure_comp, map_apply, simulateQ_map] at supported
    rw [support_map] at supported
    obtain ⟨finished, called, equal⟩ := supported
    cases equal
    let afterDemand : State := ⟨some ready.reference, trace.events ++ [RegistrationNativeSecretWordFrontendTrace.Event.demand ready.reference]⟩
    have actual : finished ∈ support ((simulateQ handler (compile (n := n) setup scalar
        ((RegistrationNativePlatformBeaconMaterialFrontend.abort RegistrationNativeSecretWordInterface.effect owner).run current) before)).run afterDemand) := by
      simpa only [compile, StateT.run, afterDemand] using called
    have last := abort_count role setup scalar owner current before afterDemand finished actual
    simp only [afterDemand, count, List.countP_append, List.countP_singleton,
      RegistrationNativeSecretWordAtomInstallTrace.attempt, Bool.false_eq_true, ite_false, Nat.add_zero] at last
    dsimp only [Prod.map, count, id]
    omega
  | some choice =>
    change result ∈ support ((simulateQ handler (compile setup scalar
      ((RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer RegistrationNativeSecretWordInterface.effect
        owner (ready.eval RegistrationNativeSecretWordMessage.zero) choice).run current) before)).run
          ⟨some ready.reference, trace.events ++ [.demand ready.reference]⟩) at supported
    rw [chosen_run] at supported
    have bounded := RegistrationNativePlatformSecretWordAtomEffects.continuation role _
      (if role = .beacon then 1 else 0) (program_bound role crypto writer owner current (ready.eval RegistrationNativeSecretWordMessage.zero) choice before)
      ⟨some ready.reference, trace.events ++ [.demand ready.reference]⟩ result supported
    simpa only [count, List.countP_append, List.countP_singleton,
      RegistrationNativeSecretWordAtomInstallTrace.attempt, Bool.false_eq_true, ite_false, Nat.add_zero] using bounded.2

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomBeaconTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomBeaconTrace.complete_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomBeaconTrace.complete_count
