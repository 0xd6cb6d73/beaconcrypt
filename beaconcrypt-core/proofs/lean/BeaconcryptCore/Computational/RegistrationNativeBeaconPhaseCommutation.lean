-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeAgreementJournal
import BeaconcryptCore.Computational.RegistrationNativeRecordJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinish
/-! Actual authentication, agreement and first-record programs are independent of the outer owner list. This follows from their actual lifted leaves with full mutable Env journals retained. Therefore the source early-Aborted owner write commutes through every adaptive primitive continuation without reading private state through a read-only assumption. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation
open RegistrationNativeBeaconFrontend (M Owner Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {I KemSK Auxiliary A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

abbrev Lower (n : Nat) (KemSK Auxiliary : Type) := StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK))

def lift (work : Lower n KemSK Auxiliary A) : M n KemSK source Auxiliary A := StateT.lift work

theorem lift_run (work : Lower n KemSK Auxiliary A) (owners : List (Owner source)) (env : EnvState Auxiliary) :
    (((lift work : M n KemSK source Auxiliary A).run owners).run env) =
      (fun result => ((result.1, owners), result.2)) <$> work.run env := by
  simp only [lift, StateT.run_lift, bind_pure_comp, StateT.run_map]

theorem lift_pure (value : A) : lift (pure value : Lower n KemSK Auxiliary A) = (pure value : M n KemSK source Auxiliary A) := by
  funext owners env
  change (((lift (pure value) : M n KemSK source Auxiliary A).run owners).run env) = (((pure value : M n KemSK source Auxiliary A).run owners).run env)
  simp only [lift_run, StateT.run_pure, map_pure]

theorem lift_bind (work : Lower n KemSK Auxiliary A) (next : A → Lower n KemSK Auxiliary B) :
    lift (work >>= next) = (lift work >>= fun value => lift (next value) : M n KemSK source Auxiliary B) := by
  funext owners env
  change (((lift (work >>= next) : M n KemSK source Auxiliary B).run owners).run env) = (((lift work >>= fun value => lift (next value) : M n KemSK source Auxiliary B).run owners).run env)
  simp only [lift_run, StateT.run_bind, bind_map_left, map_bind]

theorem simulate_lift {J : Type} {queries : OracleSpec J}
    (handler : QueryImpl queries (Lower n KemSK Auxiliary)) (work : OracleComp queries A) :
    simulateQ (fun query => lift (source := source) (handler query)) work = lift (simulateQ handler work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, lift_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, ih, lift_bind]

theorem phase_commutes (index : Nat) (phase : RegistrationNativeBeaconFrontend.Phase) (work : Lower n KemSK Auxiliary A) :
    (RegistrationNativeBeaconFrontend.updatePhase index phase *> lift work : M n KemSK source Auxiliary A) = (do
      let result ← lift work
      RegistrationNativeBeaconFrontend.updatePhase index phase
      pure result) := by
  funext owners env
  change (((RegistrationNativeBeaconFrontend.updatePhase index phase *> lift work : M n KemSK source Auxiliary A).run owners).run env) = (((do
    let result ← lift work
    RegistrationNativeBeaconFrontend.updatePhase index phase
    pure result : M n KemSK source Auxiliary A).run owners).run env)
  simp only [seqRight_eq_bind, RegistrationNativeBeaconFrontend.updatePhase, StateT.run_bind, StateT.run_modify,
    StateT.run_map, lift_run, pure_bind, map_pure, bind_pure_comp, Functor.map_map]

noncomputable def authentication (setup : PqxdhServerAuthExperiment.Setup base KemSK) :
    QueryImpl RegistrationAuthenticationExecutor.Spec (Lower n KemSK Auxiliary)
  | .hash request => do
      let digest ← StateT.lift ((Trusted n KemSK).query (.inl (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request)))))
      pure (.Some (RegistrationAuthenticationShared.digestArray digest))
  | .mldsa request => pure (RegistrationAuthenticationShared.verifyMldsa source.verify request)
  | .ed25519 request => pure (RegistrationAuthenticationShared.verifyEd25519 setup.source.crypto request)

theorem authentication_lift (setup : PqxdhServerAuthExperiment.Setup base KemSK) (query : RegistrationAuthenticationExecutor.Request) :
    RegistrationNativeBeaconFrontend.authentication (n := n) (Auxiliary := Auxiliary) setup source query = lift (authentication (source := source) setup query) := by
  cases query with
  | hash request =>
      funext owners env
      change (((RegistrationNativeBeaconFrontend.authentication setup source (.hash request) : M n KemSK source Auxiliary _).run owners).run env) = (((lift (authentication (source := source) setup (.hash request)) : M n KemSK source Auxiliary _).run owners).run env)
      simp only [RegistrationNativeBeaconFrontend.authentication, RegistrationNativeBeaconFrontend.hash,
        RegistrationNativeBeaconFrontend.effect, authentication, lift, StateT.run_lift,
        bind_pure_comp, StateT.run_map, Functor.map_map]
      rfl
  | mldsa request | ed25519 request => exact (lift_pure _).symm

noncomputable def agreement (setup : PqxdhServerAuthExperiment.Setup base KemSK) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) : QueryImpl RegistrationAgreementExecutor.Spec (Lower n KemSK Auxiliary) :=
  fun query env => (fun reply => (reply, {env with requests := env.requests ++ RegistrationWorldAgreement.recorded query})) <$>
    RegistrationNativeAgreementJournal.core setup owner oneTime query

theorem agreement_lift (setup : PqxdhServerAuthExperiment.Setup base KemSK) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Request) :
    RegistrationNativeBeaconFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup owner oneTime query = lift (agreement setup owner oneTime query) := by
  rw [RegistrationNativeAgreementJournal.agreement_logged]
  funext owners env
  change (((RegistrationNativeAgreementJournal.logged (RegistrationNativeAgreementJournal.core setup owner oneTime) query : M n KemSK source Auxiliary _).run owners).run env) =
    (((lift (agreement setup owner oneTime query) : M n KemSK source Auxiliary _).run owners).run env)
  rw [RegistrationNativeAgreementJournal.logged_run, lift_run]
  simp only [agreement, StateT.run, Functor.map_map]

noncomputable def record (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire) :
    QueryImpl RegistrationRecordPrimitives.Spec (Lower n KemSK Auxiliary) :=
  fun query env => (fun reply => (reply, {env with recordRequests := env.recordRequests ++ [RegistrationWorldAgreement.recordCall query]})) <$>
    RegistrationNativeRecordJournal.core setup wire query

theorem record_lift (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (query : RegistrationRecordPrimitives.Request) :
    RegistrationNativeBeaconFrontend.record (n := n) (mldsaSource := source) (Auxiliary := Auxiliary) setup wire query = lift (record setup wire query) := by
  rw [RegistrationNativeRecordJournal.record_eq, RegistrationNativeRecordJournal.core_lift]
  funext owners env
  change (((RegistrationNativeBeaconFrontend.updateEnv (fun env => {env with recordRequests := env.recordRequests ++ [RegistrationWorldAgreement.recordCall query]}) *>
    RegistrationNativeAgreementJournal.lift (RegistrationNativeRecordJournal.core setup wire query) : M n KemSK source Auxiliary _).run owners).run env) =
    (((lift (record setup wire query) : M n KemSK source Auxiliary _).run owners).run env)
  rw [lift_run]
  change ((RegistrationNativeAgreementJournal.lift (RegistrationNativeRecordJournal.core setup wire query)).run owners).run
      {env with recordRequests := env.recordRequests ++ [RegistrationWorldAgreement.recordCall query]} = _
  rw [RegistrationNativeAgreementJournal.lift_run]
  simp only [record, StateT.run, Functor.map_map]

theorem authentication_phase (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (index : Nat) (phase : RegistrationNativeBeaconFrontend.Phase) (work : OracleComp RegistrationAuthenticationExecutor.Spec A) :
    (RegistrationNativeBeaconFrontend.updatePhase index phase *> simulateQ (RegistrationNativeBeaconFrontend.authentication setup source) work : M n KemSK source Auxiliary A) = (do
      let result ← simulateQ (RegistrationNativeBeaconFrontend.authentication setup source) work
      RegistrationNativeBeaconFrontend.updatePhase index phase
      pure result) := by
  have handlers := funext (authentication_lift (n := n) (Auxiliary := Auxiliary) (source := source) setup)
  rw [handlers, simulate_lift]
  exact phase_commutes index phase _

theorem agreement_phase (setup : PqxdhServerAuthExperiment.Setup base KemSK) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (index : Nat) (phase : RegistrationNativeBeaconFrontend.Phase)
    (work : OracleComp RegistrationAgreementExecutor.Spec A) :
    (RegistrationNativeBeaconFrontend.updatePhase index phase *> simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner oneTime) work : M n KemSK source Auxiliary A) = (do
      let result ← simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner oneTime) work
      RegistrationNativeBeaconFrontend.updatePhase index phase
      pure result) := by
  have handlers := funext (agreement_lift (n := n) (Auxiliary := Auxiliary) setup owner oneTime)
  rw [handlers, simulate_lift]
  exact phase_commutes index phase _

theorem record_phase (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (phase : RegistrationNativeBeaconFrontend.Phase) (work : OracleComp RegistrationRecordPrimitives.Spec A) :
    (RegistrationNativeBeaconFrontend.updatePhase index phase *> simulateQ (RegistrationNativeBeaconFrontend.record setup wire) work : M n KemSK source Auxiliary A) = (do
      let result ← simulateQ (RegistrationNativeBeaconFrontend.record setup wire) work
      RegistrationNativeBeaconFrontend.updatePhase index phase
      pure result) := by
  have handlers := funext (record_lift (n := n) (Auxiliary := Auxiliary) (source := source) setup wire)
  rw [handlers, simulate_lift]
  exact phase_commutes index phase _

end BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.lift_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.lift_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.lift_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.lift_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.lift_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.lift_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.simulate_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.simulate_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.phase_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.phase_commutes

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.authentication_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.authentication_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.agreement_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.agreement_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.record_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.record_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.authentication_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.authentication_phase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.agreement_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.agreement_phase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.record_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation.record_phase
