-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconFrontend
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeAgreementJournal
open RegistrationNativeBeaconFrontend (M Owner Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {I KemSK Auxiliary A : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
def lift (work : OracleComp (Trusted n KemSK) A) : M n KemSK source Auxiliary A :=
  StateT.lift (StateT.lift work)

theorem lift_run (work : OracleComp (Trusted n KemSK) A)
    (owners : List (Owner source)) (env : EnvState Auxiliary) :
    ((lift work).run owners).run env = (fun value => ((value, owners), env)) <$> work := by
  simp only [lift, StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map]

theorem simulate_lift {J : Type} {spec : OracleSpec J}
    (handler : QueryImpl spec (OracleComp (Trusted n KemSK))) (work : OracleComp spec A) :
    simulateQ (fun query => lift (source := source) (Auxiliary := Auxiliary) (handler query)) work =
      lift (simulateQ handler work) := by
  induction work using OracleComp.inductionOn with
  | pure value =>
      funext owners env
      change ((pure value : M n KemSK source Auxiliary A).run owners).run env = ((lift (pure value)).run owners).run env
      simp only [lift_run, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      funext owners env
      change (((lift (handler query) >>= fun reply => simulateQ (fun nextQuery => lift (handler nextQuery)) (next reply)) : M n KemSK source Auxiliary A).run owners).run env = ((lift (handler query >>= fun reply => simulateQ handler (next reply))).run owners).run env
      simp only [StateT.run_bind, lift_run, bind_map_left, map_bind]
      apply bind_congr
      intro reply
      rw [ih reply, lift_run]

def coins (work : ProbComp A) : OracleComp (Trusted n KemSK) A :=
  simulateQ (fun query => (Trusted n KemSK).query (.inl (.inl query))) work

theorem sample (work : ProbComp A) :
    RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) work = lift (coins work) :=
  simulate_lift _ work

noncomputable def primitive (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    QueryImpl RegistrationAgreementShared.PrimitiveSpec (OracleComp (Trusted n KemSK)) := fun query =>
  simulateQ (fun lower => match lower with
    | .inl other => coins (Prod.fst <$>
        (RegistrationNativeKemBackend.beaconOther setup owner.prekeyScalar other).run
          ⟨owner.identitySeed, some oneTime, some owner.kemHandle⟩)
    | .inr other => (Trusted n KemSK).query (.inr (.inr other)))
    (RegistrationNativeKemInterface.beacon (some owner.kemHandle) query)

noncomputable def core (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    QueryImpl RegistrationAgreementExecutor.Spec (OracleComp (Trusted n KemSK))
  | .convertPublic key => primitive setup owner oneTime (.convertPublic key)
  | .convertSecret role => primitive setup owner oneTime (.convertSecret role)
  | .generate role => primitive setup owner oneTime (.generate role)
  | .encapsulate key => primitive setup owner oneTime (.encapsulate key)
  | .decapsulate ciphertext => primitive setup owner oneTime (.decapsulate ciphertext)
  | .dh request => primitive setup owner oneTime (.dh request)
  | .root request => pure (.Some (RegistrationAgreementShared.rootResponse setup.source.crypto request))

theorem primitive_lift (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementShared.PrimitiveRequest) :
    RegistrationNativeBeaconFrontend.primitive (n := n) (Auxiliary := Auxiliary) setup owner oneTime query =
      lift (primitive setup owner oneTime query) := by
  unfold RegistrationNativeBeaconFrontend.primitive primitive
  rw [← simulate_lift]
  congr 1
  funext lower
  cases lower with
  | inl other => exact sample _
  | inr other => rfl

theorem core_lift (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Request) :
    RegistrationNativeBeaconFrontend.agreementCore (n := n) (Auxiliary := Auxiliary) setup owner oneTime query =
      lift (core setup owner oneTime query) := by
  cases query with
  | root request =>
      funext owners env
      change ((pure _ : M n KemSK source Auxiliary _).run owners).run env = ((lift (pure _)).run owners).run env
      simp only [lift_run, StateT.run_pure, map_pure]
  | _ => exact primitive_lift setup owner oneTime _
abbrev Journal := List RegistrationAgreementExecutor.Request

def traced (handler : QueryImpl RegistrationAgreementExecutor.Spec (OracleComp (Trusted n KemSK))) :
    QueryImpl RegistrationAgreementExecutor.Spec (StateT Journal (OracleComp (Trusted n KemSK))) :=
  fun query previous => (fun reply => (reply, previous ++ RegistrationWorldAgreement.recorded query)) <$> handler query

theorem traced_run (handler : QueryImpl RegistrationAgreementExecutor.Spec (OracleComp (Trusted n KemSK)))
    (query : RegistrationAgreementExecutor.Request) (journal : Journal) :
    (traced handler query).run journal =
      (fun reply => (reply, journal ++ RegistrationWorldAgreement.recorded query)) <$> handler query := rfl

def logged (handler : QueryImpl RegistrationAgreementExecutor.Spec (OracleComp (Trusted n KemSK))) :
    QueryImpl RegistrationAgreementExecutor.Spec (M n KemSK source Auxiliary) := fun query => do
  RegistrationNativeBeaconFrontend.updateEnv fun env => {env with requests := env.requests ++ RegistrationWorldAgreement.recorded query}
  lift (handler query)

theorem logged_run (handler : QueryImpl RegistrationAgreementExecutor.Spec (OracleComp (Trusted n KemSK)))
    (query : RegistrationAgreementExecutor.Request) (owners : List (Owner source)) (env : EnvState Auxiliary) :
    (((logged handler query : M n KemSK source Auxiliary _).run owners).run env) =
      (fun reply => ((reply, owners), {env with requests := env.requests ++ RegistrationWorldAgreement.recorded query})) <$> handler query := by
  change ((lift (handler query)).run owners).run {env with requests := env.requests ++ RegistrationWorldAgreement.recorded query} = _
  exact lift_run _ _ _

theorem program (handler : QueryImpl RegistrationAgreementExecutor.Spec (OracleComp (Trusted n KemSK)))
    (work : OracleComp RegistrationAgreementExecutor.Spec A) (owners : List (Owner source)) (env : EnvState Auxiliary) :
    (((simulateQ (logged handler) work : M n KemSK source Auxiliary A).run owners).run env) =
      (fun result => ((result.1, owners), {env with requests := result.2})) <$>
        (simulateQ (traced handler) work).run env.requests := by
  induction work using OracleComp.inductionOn generalizing env with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, logged_run, traced_run,
        bind_map_left, map_bind]
      apply bind_congr
      intro reply
      exact ih reply {env with requests := env.requests ++ RegistrationWorldAgreement.recorded query}

theorem traced_erasure (handler : QueryImpl RegistrationAgreementExecutor.Spec (OracleComp (Trusted n KemSK)))
    (work : OracleComp RegistrationAgreementExecutor.Spec A) (journal : Journal) :
    Prod.fst <$> (simulateQ (traced handler) work).run journal = simulateQ handler work := by
  induction work using OracleComp.inductionOn generalizing journal with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, traced_run,
        bind_map_left, map_bind]
      apply bind_congr
      intro reply
      exact ih reply _

theorem agreement_logged (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    RegistrationNativeBeaconFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup owner oneTime =
      logged (core setup owner oneTime) := by
  funext query
  unfold RegistrationNativeBeaconFrontend.agreement logged
  rw [core_lift]

theorem native_program (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp RegistrationAgreementExecutor.Spec A)
    (owners : List (Owner source)) (env : EnvState Auxiliary) :
    (((simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner oneTime) work : M n KemSK source Auxiliary A).run owners).run env) =
      (fun result => ((result.1, owners), {env with requests := result.2})) <$>
        (simulateQ (traced (core setup owner oneTime)) work).run env.requests := by
  rw [agreement_logged]
  exact program _ work owners env

theorem core_program (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp RegistrationAgreementExecutor.Spec A)
    (owners : List (Owner source)) (env : EnvState Auxiliary) :
    (((simulateQ (RegistrationNativeBeaconFrontend.agreementCore setup owner oneTime) work : M n KemSK source Auxiliary A).run owners).run env) =
      (fun reply => ((reply, owners), env)) <$> simulateQ (core setup owner oneTime) work := by
  have leaves : RegistrationNativeBeaconFrontend.agreementCore (n := n) (Auxiliary := Auxiliary) setup owner oneTime =
      (fun query => lift (core setup owner oneTime query)) := funext (core_lift setup owner oneTime)
  rw [leaves, simulate_lift, lift_run]

theorem native_erasure (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp RegistrationAgreementExecutor.Spec A)
    (owners : List (Owner source)) (env : EnvState Auxiliary) :
    (fun result => (result.1, {result.2 with requests := env.requests})) <$>
      (((simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner oneTime) work : M n KemSK source Auxiliary A).run owners).run env) =
      (((simulateQ (RegistrationNativeBeaconFrontend.agreementCore setup owner oneTime) work : M n KemSK source Auxiliary A).run owners).run env) := by
  rw [native_program, core_program]
  have erased := congrArg (fun computation : OracleComp (Trusted n KemSK) A => (fun value => ((value, owners), env)) <$> computation)
    (traced_erasure (core setup owner oneTime) work env.requests)
  simpa only [Functor.map_map] using erased

end BeaconcryptCore.Computational.RegistrationNativeAgreementJournal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.lift_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.lift_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.simulate_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.simulate_lift
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.sample
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.primitive_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.primitive_lift
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.core_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.core_lift
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.logged_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.logged_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.traced_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.traced_erasure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.agreement_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.agreement_logged
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.native_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.core_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.core_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.traced_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.traced_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.native_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAgreementJournal.native_erasure
