-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePreparation

/-! The scalar-free native Beacon collection and prepare phase reconstructs the actual agreement controller on the same full source World. Reconstruction projects only the private root memo/family and a redundant cache frame. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAgreement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationBeaconReferenceNativeStage (Local lower primitive liftCache)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

abbrev Plain (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativeRelatedFamily.State × Local n KemSK source

def dropCache : RegistrationNativeBeaconRootSource.State (Local n KemSK mlSource) → Plain n KemSK mlSource :=
  fun state => (state.1, state.2.1)

noncomputable def prefixHandler (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) :
    QueryImpl (PqxdhPhase2GapDhSource.PrefixSpec Unit Unit Unit Unit registration.AuthenticatedResponse)
      (StateT (Plain n KemSK mlSource) ProbComp) := fun query before =>
  (fun result => (result.1, (before.1, result.2))) <$>
    (lower setup checks representation created
      (PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain
        (RegistrationBeaconRootInterpreter.auxImpl (RegistrationBeaconReferenceCompiler.trustedBackend setup owner oneTime) authenticated)
        RegistrationBeaconReferenceCompiler.trustedVisit query)).run before.2

private theorem lifted_run {Auxiliary : Type}
    (work : StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Value)
    (before : RegistrationNativeBeaconRootSource.State Auxiliary) :
    (RegistrationNativeBeaconRootSource.lift work).run before =
      (fun result => (result.1, (before.1, result.2))) <$> work.run before.2 := rfl

private theorem cache_run {Auxiliary : Type} (work : StateT Auxiliary ProbComp Value)
    (before : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (liftCache work).run before = (fun result => (result.1, (result.2, before.2))) <$> work.run before.1 := rfl

private theorem lower_run (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : StateT (RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
      (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) Value)
    (before : Local n KemSK mlSource) :
    (lower setup checks representation created work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
          (work.run before.1)).run before.2 := rfl

private theorem prefix_query (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (query : (PqxdhPhase2GapDhSource.PrefixSpec Unit Unit Unit Unit registration.AuthenticatedResponse).Domain)
    (before : RegistrationNativeBeaconRootSource.State (Local n KemSK mlSource)) :
    Prod.map id dropCache <$>
      (PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain
        (RegistrationBeaconRootInterpreter.auxImpl
          (fun request => RegistrationNativeBeaconRootSource.lift
            (RegistrationAgreementShared.implementation setup.source
              (primitive setup checks representation created owner oneTime) request)) authenticated)
        (fun point => RegistrationNativeBeaconRootSource.lift
          (liftCache (lower setup checks representation created (RegistrationBeaconReferenceSource.visit point)))) query).run before =
      (prefixHandler setup checks representation created owner oneTime authenticated query).run (dropCache before) := by
  unfold prefixHandler
  cases query <;>
    simp only [PqxdhPhase2GapDhSource.prefixImpl, RegistrationBeaconRootInterpreter.auxImpl,
      RegistrationBeaconAgreementRoot.callbacks, simulateQ_pure, simulateQ_map, simulateQ_spec_query,
      ← RegistrationBeaconReferenceNativeStage.backend_shared,
      lifted_run, cache_run, lower_run,
    RegistrationBeaconReferenceSource.backend, RegistrationBeaconReferenceSource.visit,
    RegistrationBeaconReferenceCompiler.trustedVisit, StateT.run_map,
    StateT.run_pure, StateT.run_modify, simulateQ_map, simulateQ_pure,
      bind_pure_comp, map_pure, Functor.map_map, Prod.map_def, id_eq, dropCache]
  all_goals rfl

def family (implementation : QueryImpl RegistrationNativeRelatedRoot.RootSpec
    (StateT RegistrationNativeRelatedFamily.State ProbComp)) :
    QueryImpl RegistrationNativeRelatedRoot.RootSpec (StateT (Plain n KemSK mlSource) ProbComp) :=
  fun query before => (fun result => (result.1, (result.2, before.2))) <$> (implementation query).run before.1

private theorem family_program
    (implementation : QueryImpl RegistrationNativeRelatedRoot.RootSpec
      (StateT RegistrationNativeRelatedFamily.State ProbComp))
    (work : OracleComp RegistrationNativeRelatedRoot.RootSpec Value)
    (before : RegistrationNativeBeaconRootSource.State (Local n KemSK mlSource)) :
    Prod.map id dropCache <$>
      (simulateQ (RegistrationNativeBeaconRootSource.familyImpl implementation) work).run before =
      (simulateQ (family implementation) work).run (dropCache before) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  simp only [RegistrationNativeBeaconRootSource.familyImpl, family, StateT.run,
    Functor.map_map, Prod.map_def, id_eq, dropCache]

noncomputable def stage (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (implementation : QueryImpl RegistrationNativeRelatedRoot.RootSpec
      (StateT RegistrationNativeRelatedFamily.State ProbComp))
    (authenticated : registration.AuthenticatedResponse) :
    StateT (Plain n KemSK mlSource) ProbComp (RustM agreement.AgreementEffect) := do
  let pending ← simulateQ (prefixHandler setup checks representation created owner oneTime authenticated)
    (PqxdhPhase2DhMetadata.prepare (completedBinding := authenticated.binding) authenticated.control () () () [])
  match pending with
  | none => pure (.ok (RegistrationBeaconAgreementRoot.rejected authenticated))
  | some pending => simulateQ (family implementation) (RegistrationNativeBeaconRootSource.client authenticated pending)

/-- Removing the unused cache frame commutes with the complete actual public collection and private root step. -/
theorem stage_project (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (implementation : QueryImpl RegistrationNativeRelatedRoot.RootSpec
      (StateT RegistrationNativeRelatedFamily.State ProbComp))
    (authenticated : registration.AuthenticatedResponse)
    (before : RegistrationNativeBeaconRootSource.State (Local n KemSK mlSource)) :
    Prod.map id dropCache <$>
      (RegistrationNativeBeaconRootStage.stage setup.beaconDomain
        (RegistrationAgreementShared.implementation setup.source (primitive setup checks representation created owner oneTime))
        (fun point => liftCache (lower setup checks representation created (RegistrationBeaconReferenceSource.visit point)))
        implementation authenticated).run before =
      (stage setup checks representation created owner oneTime implementation authenticated).run (dropCache before) := by
  have collected := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ dropCache
    (prefix_query setup checks representation created owner oneTime authenticated)
    (PqxdhPhase2DhMetadata.prepare (completedBinding := authenticated.binding) authenticated.control () () () []) before
  simp only [RegistrationNativeBeaconRootStage.stage, stage, StateT.run_bind, map_bind]
  rw [← collected, bind_map_left]
  apply bind_congr
  rintro ⟨pending, reached⟩
  cases pending with
  | none => simp only [StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | some pending => exact family_program implementation _ reached

/-- The native arbitrary-pin descriptor phase reconstructs the complete actual agreement controller on the full reached World and private KEM pool. -/
theorem stage_native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
    (before : Plain n KemSK mlSource) :
    Prod.map id Prod.snd <$>
      (stage setup checks representation created owner oneTime
        (RegistrationNativeRelatedRoot.sourceImpl setup.source setup.hmac setup.joint setup.dh created.seed scalar)
        authenticated).run before =
      (simulateQ (RegistrationBeaconReferenceNativeStage.native setup checks representation created scalar owner oneTime)
        (RegistrationAgreementExecutor.beacon authenticated)).run before.2 := by
  have projected := congrArg (fun work => Prod.map id Prod.snd <$> work)
    (stage_project setup checks representation created owner oneTime
      (RegistrationNativeRelatedRoot.sourceImpl setup.source setup.hmac setup.joint setup.dh created.seed scalar)
      authenticated (before.1, (before.2, ∅)))
  have actual := RegistrationBeaconReferenceNativeStage.stage_native setup checks representation created scalar
    owner oneTime authenticated coherent (before.1, (before.2, ∅))
  simp only [Functor.map_map, Prod.map_def, id_eq, Function.comp_def, dropCache] at projected actual ⊢
  exact projected.symm.trans actual

private theorem framed_collect (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : Plain n KemSK mlSource) :
    (simulateQ (prefixHandler setup checks representation created owner oneTime authenticated)
      (PqxdhPhase2DhMetadata.prepare (completedBinding := authenticated.binding) authenticated.control () () () [])).run before =
      (fun result => (result.1, (before.1, result.2))) <$>
        (lower setup checks representation created
          (RegistrationBeaconReferenceCompiler.trustedCollect setup owner oneTime authenticated)).run before.2 := by
  let embed : Local n KemSK mlSource → Plain n KemSK mlSource := fun current => (before.1, current)
  have framed := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (fun query => lower setup checks representation created
      (PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain
        (RegistrationBeaconRootInterpreter.auxImpl (RegistrationBeaconReferenceCompiler.trustedBackend setup owner oneTime) authenticated)
        RegistrationBeaconReferenceCompiler.trustedVisit query))
    (prefixHandler setup checks representation created owner oneTime authenticated) embed
    (fun _ _ => rfl) (PqxdhPhase2DhMetadata.prepare (completedBinding := authenticated.binding) authenticated.control () () () []) before.2
  rw [← RegistrationBeaconReferenceNativeStage.lower_program] at framed
  simpa only [RegistrationBeaconReferenceCompiler.trustedCollect, embed, Prod.map_def, id_eq] using framed.symm

private theorem family_only
    (implementation : QueryImpl RegistrationNativeRelatedRoot.RootSpec
      (StateT RegistrationNativeRelatedFamily.State ProbComp))
    (work : OracleComp RegistrationNativeRelatedRoot.RootSpec Value) (before : Plain n KemSK mlSource) :
    (simulateQ (family implementation) work).run before =
      (fun result => (result.1, (result.2, before.2))) <$> (simulateQ implementation work).run before.1 := by
  let embed : RegistrationNativeRelatedFamily.State → Plain n KemSK mlSource := fun current => (current, before.2)
  simpa only [embed, Prod.map_def, id_eq] using
    (OracleComp.map_run_simulateQ_eq_of_query_map_eq implementation (family implementation) embed
      (fun _ _ => rfl) work before.1).symm

/-- The executable ready value and its private returned root reconstruct the actual complete native descriptor stage, including every reached collection effect. -/
theorem agreement_stage (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (before : RegistrationBeaconReferenceNativeInterpreter.State n KemSK mlSource) :
    (fun result => (RegistrationBeaconReferenceNativePreparation.restored result.2.1 authenticated result.1.1,
      (result.1.2, result.2.2.2))) <$>
      (simulateQ (RegistrationBeaconReferenceNativeInterpreter.implementation setup checks wire representation created scalar credential)
        ((RegistrationBeaconReferenceCompiler.agreement setup owner oneTime authenticated).run env)).run before =
      Prod.map id Prod.snd <$>
        (stage setup checks representation created owner oneTime
          (RegistrationNativeRelatedRoot.sourceImpl setup.source setup.hmac setup.joint setup.dh created.seed scalar)
          authenticated).run (before.2.1, (env, before.2.2)) := by
  simp only [RegistrationBeaconReferenceCompiler.agreement, StateT.run_bind, simulateQ_bind,
    map_bind, stage]
  rw [RegistrationBeaconReferenceNativePreparation.collect_source, framed_collect]
  simp only [bind_map_left, lower_run]
  apply bind_congr
  rintro ⟨⟨pending, afterEnv⟩, afterNative⟩
  cases pending with
  | none =>
      simp only [StateT.run_pure, simulateQ_pure, map_pure, Prod.map_def, id_eq,
        RegistrationBeaconReferenceNativePreparation.restored, RegistrationBeaconReferenceRoot.restored]
  | some pending =>
      change _ = Prod.map id Prod.snd <$>
        (simulateQ (family
          (RegistrationNativeRelatedRoot.sourceImpl setup.source setup.hmac setup.joint setup.dh created.seed scalar))
          (RegistrationNativeBeaconRootSource.client authenticated pending)).run
            (before.2.1, (afterEnv, afterNative))
      rw [family_only]
      simp only [StateT.run_lift, bind_pure_comp, simulateQ_map, StateT.run_map,
        bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]
      have actual := congrArg (fun work => (fun result => (result.1, (afterEnv, result.2))) <$> work)
        (RegistrationBeaconReferenceNativePreparation.client_source setup checks wire representation created scalar credential
          authenticated pending (before.1, (before.2.1, afterNative)))
      simpa only [Functor.map_map] using actual

/-- Complete native source agreement is recovered from the executable reference and private root memo on the same reached World and private KEM pool. -/
theorem agreement_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (before : RegistrationBeaconReferenceNativeInterpreter.State n KemSK mlSource) :
    (fun result => (RegistrationBeaconReferenceNativePreparation.restored result.2.1 authenticated result.1.1,
      (result.1.2, result.2.2.2))) <$>
      (simulateQ (RegistrationBeaconReferenceNativeInterpreter.implementation setup checks wire representation created scalar credential)
        ((RegistrationBeaconReferenceCompiler.agreement setup owner oneTime authenticated).run env)).run before =
      (simulateQ (RegistrationBeaconReferenceNativeStage.native setup checks representation created scalar owner oneTime)
        (RegistrationAgreementExecutor.beacon authenticated)).run (env, before.2.2) := by
  rw [agreement_stage]
  exact stage_native setup checks representation created scalar owner oneTime authenticated coherent _

end BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAgreement.stage_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAgreement.stage_project

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAgreement.stage_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAgreement.stage_native

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAgreement.agreement_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAgreement.agreement_stage

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAgreement.agreement_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAgreement.agreement_source
