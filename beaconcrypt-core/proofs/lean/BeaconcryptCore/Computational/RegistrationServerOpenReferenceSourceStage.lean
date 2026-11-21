-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemReferencePrefix
import BeaconcryptCore.Computational.RegistrationServerReferenceSourceStage
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceCompiler

/-! The real public Server reference compiler is closed with the literal native root evaluator and the actual indexed KEM pool. Preparation may retain its private root memo through an arbitrary deterministic private update. That memo is erased only from this phase's source projection; it remains in the actual result for later material demand. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceStage
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhSecretInputKdf (RootOutput)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeKemReferenceEffects (Callbacks implementation)
open RegistrationNativeKemReferenceWorld (Private)
open RegistrationNativeKemReferenceBackend (State project)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {ι KemSK Extra Value : Type} {base : OracleSpec ι}

noncomputable def prepare (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (remember : Extra → Message → Option RootOutput → Extra) :
    QueryImpl RegistrationServerReferenceRoot.PrepareSpec (StateT (Private n KemSK Extra) ProbComp) := fun message before =>
  let root := RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar message
  pure (root.map (fun _ => message), { before with extra := remember before.extra message root })

noncomputable def callbacks (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (remember : Extra → Message → Option RootOutput → Extra)
    (services : Callbacks n KemSK Extra) : Callbacks n KemSK Extra :=
  { services with prepare := prepare setup seed scalar remember }

/-- Closing the actual reference preparation returns the same capability as the literal source evaluator and preserves the complete World; the actual private memo update is retained before projection. -/
theorem client_world (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (remember : Extra → Message → Option RootOutput → Extra)
    (services : Callbacks n KemSK Extra) (binding : session.RegistrationBinding)
    (input : PqxdhServerRootPreparation.Inputs registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding)
    (before : Private n KemSK Extra) :
    (fun result => (result.1, result.2.world)) <$>
      (simulateQ (implementation setup (callbacks setup seed scalar remember services))
        (simulateQ RegistrationBeaconReferenceCompiler.prepare
          (RegistrationServerReferenceRoot.client binding input))).run before =
      (fun reply => (reply, before.world)) <$>
        simulateQ (RegistrationServerReferenceSourceClient.prepare setup.source setup.joint setup.dh seed scalar)
          (RegistrationServerReferenceRoot.client binding input) := by
  classical
  by_cases admitted : PqxdhServerRelatedRootInput.localNonzero input
  · simp only [RegistrationServerReferenceRoot.client, admitted, not_true_eq_false, ite_false,
      simulateQ_bind, simulateQ_spec_query, RegistrationBeaconReferenceCompiler.prepare,
      implementation, RegistrationNativeKemReferenceWorld.handler,
      callbacks, StateT.run, simulateQ_pure, pure_bind, map_pure,
      RegistrationServerReferenceSourceClient.prepare]
    simp only [StateT.monad_bind_def, StateT.bind, prepare, StateT.monad_pure_def, StateT.pure, pure_bind, map_pure]
  · simp only [RegistrationServerReferenceRoot.client, admitted, not_false_eq_true, ite_true,
      simulateQ_pure, StateT.run_pure, map_pure]

noncomputable def agreement (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT (State n KemSK Extra) ProbComp (RustM (Option RegistrationServerReferenceRoot.Ready)) :=
  RegistrationNativeKemReferencePrefix.lower setup (callbacks setup seed scalar remember services) (do
    let input ← RegistrationNativeKemReferenceCompiler.collect setup checks packet authenticated
    match input with
    | none => pure (.ok none)
    | some input => StateT.lift (simulateQ RegistrationBeaconReferenceCompiler.prepare
        (RegistrationServerReferenceRoot.client authenticated.binding input)))

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := by
  change (work before >>= fun result => pure (observe result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

theorem agreement_run (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : State n KemSK Extra) :
    (agreement setup checks seed scalar remember services packet authenticated).run before = (do
      let collected ← (RegistrationNativeKemReferencePrefix.lower setup (callbacks setup seed scalar remember services)
        (RegistrationNativeKemReferenceCompiler.collect setup checks packet authenticated)).run before
      match collected.1 with
      | none => pure (.ok none, collected.2)
      | some input =>
          (fun result => (result.1, (collected.2.1, result.2))) <$>
            (simulateQ (implementation setup (callbacks setup seed scalar remember services))
              (simulateQ RegistrationBeaconReferenceCompiler.prepare
                (RegistrationServerReferenceRoot.client authenticated.binding input))).run collected.2.2) := by
  simp only [agreement, RegistrationNativeKemReferencePrefix.lower, StateT.run, simulateQ_bind,
    StateT.monad_bind_def, StateT.bind, StateT.monad_pure_def, bind_map_left, map_bind]
  apply bind_congr
  rintro ⟨⟨input, env⟩, current⟩
  cases input <;> simp only [StateT.pure, StateT.lift, bind_pure_comp,
    simulateQ_pure, simulateQ_map, state_pure_apply, state_map_apply, map_pure, Functor.map_map]
  all_goals rfl

/-- The actual open collector and private preparation have the literal complete native reference-stage reply and World. -/
theorem agreement_project (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : State n KemSK Extra) :
    Prod.map id project <$> (agreement setup checks seed scalar remember services packet authenticated).run before =
      (RegistrationServerReferenceSourceStage.referenceStage setup checks seed scalar packet authenticated).run (project before) := by
  rw [agreement_run]
  simp only [RegistrationServerReferenceSourceStage.referenceStage, StateT.run_bind, map_bind]
  rw [← RegistrationNativeKemReferencePrefix.collect_project setup checks
    (callbacks setup seed scalar remember services) packet authenticated before, bind_map_left]
  apply bind_congr
  rintro ⟨input, current⟩
  cases input with
  | none => simp only [map_pure]; rfl
  | some input =>
      have source := congrArg (fun distribution => (fun result => (result.1,
        RegistrationWorldAgreementProgramCompiler.project (current.1, result.2))) <$> distribution)
        (client_world setup seed scalar remember services authenticated.binding input current.2)
      simpa only [Functor.map_map, Prod.map, id_eq, project, StateT.run_lift, bind_pure_comp] using source

end BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceStage

/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceStage.client_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceStage.client_world
/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceStage.agreement_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceStage.agreement_project

/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceStage.agreement_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceStage.agreement_run
