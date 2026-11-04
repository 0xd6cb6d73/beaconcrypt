-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeAgreementJournal
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRecordJournal
open RegistrationNativeBeaconFrontend (M Owner Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeAgreementJournal (lift_run simulate_lift coins)
variable {n : Nat} {I KemSK Auxiliary A : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

noncomputable def unlogged (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire) :
    QueryImpl RegistrationRecordPrimitives.Spec (M n KemSK source Auxiliary)
  | .hash transcript => do
      let digest ← RegistrationNativeBeaconFrontend.hash (.Single (Std.Array.to_slice transcript.bytes))
      pure (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest))
  | other => RegistrationNativeBeaconFrontend.sample (Prod.fst <$>
      (RegistrationRecordPrimitives.implementation setup.source wire.frameWrite other).run ((), ∅))

theorem record_eq (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (query : RegistrationRecordPrimitives.Request) :
    RegistrationNativeBeaconFrontend.record (n := n) (mldsaSource := source) (Auxiliary := Auxiliary) setup wire query = (do
      RegistrationNativeBeaconFrontend.updateEnv fun env => {env with recordRequests := env.recordRequests ++ [RegistrationWorldAgreement.recordCall query]}
      unlogged setup wire query) := by
  cases query <;> rfl

noncomputable def core (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire) :
    QueryImpl RegistrationRecordPrimitives.Spec (OracleComp (Trusted n KemSK))
  | .hash transcript => do
      let digest ← (Trusted n KemSK).query (.inl (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes (.Single (Std.Array.to_slice transcript.bytes))))))
      pure (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest))
  | other => coins (Prod.fst <$>
      (RegistrationRecordPrimitives.implementation setup.source wire.frameWrite other).run ((), ∅))

theorem core_lift (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (query : RegistrationRecordPrimitives.Request) :
    unlogged (n := n) (source := source) (Auxiliary := Auxiliary) setup wire query = RegistrationNativeAgreementJournal.lift (core setup wire query) := by
  cases query with
  | hash transcript =>
      funext owners env
      let request : registration.HashRequest := .Single (Std.Array.to_slice transcript.bytes)
      let query : OracleComp (Trusted n KemSK) CtxRomAuth.CtxDigest :=
        (Trusted n KemSK).query (.inl (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request))))
      change (((RegistrationNativeAgreementJournal.lift query >>= fun digest =>
        pure (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest)) : M n KemSK source Auxiliary (core.option.Option (Std.Array U8 64#usize))).run owners).run env) = _
      rw [StateT.run_bind, StateT.run_bind, lift_run]
      simp only [StateT.run_pure, bind_map_left]
      change (query >>= fun digest => pure ((core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest), owners), env)) =
        ((RegistrationNativeAgreementJournal.lift (n := n) (source := source) (Auxiliary := Auxiliary) (core setup wire (.hash transcript))).run owners).run env
      rw [lift_run]
      change (query >>= fun digest => pure ((core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest), owners), env)) =
        (fun value => ((value, owners), env)) <$> (query >>= fun digest => pure (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest)))
      simp only [map_bind, map_pure]
  | _ => exact RegistrationNativeAgreementJournal.sample _

abbrev Journal := List RegistrationWorldAgreement.RecordCall

def traced (handler : QueryImpl RegistrationRecordPrimitives.Spec (OracleComp (Trusted n KemSK))) :
    QueryImpl RegistrationRecordPrimitives.Spec (StateT Journal (OracleComp (Trusted n KemSK))) :=
  fun query previous => (fun reply => (reply, previous ++ [RegistrationWorldAgreement.recordCall query])) <$> handler query

theorem traced_run (handler : QueryImpl RegistrationRecordPrimitives.Spec (OracleComp (Trusted n KemSK)))
    (query : RegistrationRecordPrimitives.Request) (journal : Journal) :
    (traced handler query).run journal =
      (fun reply => (reply, journal ++ [RegistrationWorldAgreement.recordCall query])) <$> handler query := rfl

def logged (handler : QueryImpl RegistrationRecordPrimitives.Spec (OracleComp (Trusted n KemSK))) :
    QueryImpl RegistrationRecordPrimitives.Spec (M n KemSK source Auxiliary) := fun query => do
  RegistrationNativeBeaconFrontend.updateEnv fun env => {env with recordRequests := env.recordRequests ++ [RegistrationWorldAgreement.recordCall query]}
  RegistrationNativeAgreementJournal.lift (handler query)

theorem logged_run (handler : QueryImpl RegistrationRecordPrimitives.Spec (OracleComp (Trusted n KemSK)))
    (query : RegistrationRecordPrimitives.Request) (owners : List (Owner source)) (env : EnvState Auxiliary) :
    (((logged handler query : M n KemSK source Auxiliary _).run owners).run env) =
      (fun reply => ((reply, owners), {env with recordRequests := env.recordRequests ++ [RegistrationWorldAgreement.recordCall query]})) <$> handler query := by
  change ((RegistrationNativeAgreementJournal.lift (handler query)).run owners).run {env with recordRequests := env.recordRequests ++ [RegistrationWorldAgreement.recordCall query]} = _
  exact lift_run _ _ _

theorem program (handler : QueryImpl RegistrationRecordPrimitives.Spec (OracleComp (Trusted n KemSK)))
    (work : OracleComp RegistrationRecordPrimitives.Spec A) (owners : List (Owner source)) (env : EnvState Auxiliary) :
    (((simulateQ (logged handler) work : M n KemSK source Auxiliary A).run owners).run env) =
      (fun result => ((result.1, owners), {env with recordRequests := result.2})) <$>
        (simulateQ (traced handler) work).run env.recordRequests := by
  induction work using OracleComp.inductionOn generalizing env with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, logged_run, traced_run,
        bind_map_left, map_bind]
      apply bind_congr
      intro reply
      exact ih reply {env with recordRequests := env.recordRequests ++ [RegistrationWorldAgreement.recordCall query]}

theorem traced_erasure (handler : QueryImpl RegistrationRecordPrimitives.Spec (OracleComp (Trusted n KemSK)))
    (work : OracleComp RegistrationRecordPrimitives.Spec A) (journal : Journal) :
    Prod.fst <$> (simulateQ (traced handler) work).run journal = simulateQ handler work := by
  induction work using OracleComp.inductionOn generalizing journal with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, traced_run,
        bind_map_left, map_bind]
      apply bind_congr
      intro reply
      exact ih reply _

theorem native_program (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (work : OracleComp RegistrationRecordPrimitives.Spec A) (owners : List (Owner source)) (env : EnvState Auxiliary) :
    (((simulateQ (RegistrationNativeBeaconFrontend.record setup wire) work : M n KemSK source Auxiliary A).run owners).run env) =
      (fun result => ((result.1, owners), {env with recordRequests := result.2})) <$>
        (simulateQ (traced (core setup wire)) work).run env.recordRequests := by
  have leaves : RegistrationNativeBeaconFrontend.record (n := n) (mldsaSource := source) (Auxiliary := Auxiliary) setup wire = logged (core setup wire) := by
    funext query
    rw [record_eq, core_lift]
    rfl
  rw [leaves]
  exact program _ work owners env
end BeaconcryptCore.Computational.RegistrationNativeRecordJournal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordJournal.record_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordJournal.record_eq

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordJournal.core_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordJournal.core_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordJournal.traced_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordJournal.traced_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordJournal.logged_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordJournal.logged_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordJournal.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordJournal.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordJournal.traced_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordJournal.traced_erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordJournal.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordJournal.native_program
