-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree
import BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation
import BeaconcryptCore.Computational.RegistrationNativeFinishFactor
/-! The complete logged finish cryptographic body and its unlogged source tree are projections of the same adaptive request execution. Erasure is derived per actual authentication, agreement and first-record handler and composed through every branch. It erases only callback metadata; all native effects, private KEM replies and primitive draw costs remain in the free tree. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure
open RegistrationNativeBeaconFrontend (Trusted Owner)
open RegistrationNativeBeaconPhaseCommutation (Lower)
open BeaconcryptCore.Refinement
variable {n : Nat} {I J KemSK Auxiliary A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

theorem simulation {queries : OracleSpec J}
    (handler : QueryImpl queries (Lower n KemSK Auxiliary)) (raw : QueryImpl queries (OracleComp (Trusted n KemSK)))
    (leaves : ∀ query env, Prod.fst <$> (handler query).run env = raw query)
    (work : OracleComp queries A) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Prod.fst <$> (simulateQ handler work).run env = simulateQ raw work := by
  induction work using OracleComp.inductionOn generalizing env with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, ih]
      have reduced := congrArg (fun call => call >>= fun reply => simulateQ raw (next reply)) (leaves query env)
      simpa only [bind_map_left] using reduced

theorem authentication_leaf (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (query : RegistrationAuthenticationExecutor.Request) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Prod.fst <$> (RegistrationNativeBeaconPhaseCommutation.authentication (n := n) (source := source) setup query).run env =
      AdapterPublicFinishFreeTree.authentication (source := source) setup query := by
  cases query with
  | hash request =>
      simp only [RegistrationNativeBeaconPhaseCommutation.authentication, AdapterPublicFinishFreeTree.authentication,
        StateT.run_map, StateT.run_lift, bind_pure_comp, Functor.map_map]
  | _ => simp only [RegistrationNativeBeaconPhaseCommutation.authentication, AdapterPublicFinishFreeTree.authentication,
      StateT.run_pure, map_pure]

theorem agreement_leaf (setup : PqxdhServerAuthExperiment.Setup base KemSK) (owner : Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Request)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Prod.fst <$> (RegistrationNativeBeaconPhaseCommutation.agreement (n := n) setup owner scalar query).run env =
      RegistrationNativeAgreementJournal.core setup owner scalar query := by
  simp only [RegistrationNativeBeaconPhaseCommutation.agreement, StateT.run, Functor.map_map]
  exact id_map _

theorem record_leaf (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (query : RegistrationRecordPrimitives.Request) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Prod.fst <$> (RegistrationNativeBeaconPhaseCommutation.record (n := n) setup wire query).run env =
      RegistrationNativeRecordJournal.core setup wire query := by
  simp only [RegistrationNativeBeaconPhaseCommutation.record, StateT.run, Functor.map_map]
  exact id_map _

theorem bind_erasure (work : Lower n KemSK Auxiliary A) (next : A → Lower n KemSK Auxiliary B)
    (raw : OracleComp (Trusted n KemSK) A) (later : A → OracleComp (Trusted n KemSK) B)
    (first : ∀ env, Prod.fst <$> work.run env = raw)
    (rest : ∀ value env, Prod.fst <$> (next value).run env = later value)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Prod.fst <$> (work >>= next).run env = raw >>= later := by
  simp only [StateT.run_bind, map_bind, rest]
  have reduced := congrArg (fun call => call >>= later) (first env)
  simpa only [bind_map_left] using reduced

noncomputable def afterAgreement (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (result : RustM agreement.AgreementEffect) : OracleComp (Trusted n KemSK) (RustM (Option registration.CompletedBeacon)) :=
  match result with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.BeaconComplete agreed) => RegistrationNativeFinishFactor.collapse <$>
      simulateQ (RegistrationNativeRecordJournal.core setup wire) (RegistrationBeaconRecordExecutor.begin agreed)
  | .ok _ => pure (.ok none)

noncomputable def accepted (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    OracleComp (Trusted n KemSK) (RustM (Option registration.CompletedBeacon)) := do
  let agreed ← simulateQ (RegistrationNativeAgreementJournal.core setup owner scalar) (RegistrationAgreementExecutor.beacon authenticated)
  afterAgreement setup wire agreed

noncomputable def afterAuthentication (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (result : RustM RegistrationResponseExecutor.ResponseResult) :
    OracleComp (Trusted n KemSK) (RustM (Option registration.CompletedBeacon)) :=
  match result with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok authenticated) => accepted setup wire owner scalar authenticated

noncomputable def body (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) : OracleComp (Trusted n KemSK) (RustM (Option registration.CompletedBeacon)) := do
  let authenticated ← simulateQ (AdapterPublicFinishFreeTree.authentication (source := source) setup)
    (RegistrationResponseExecutor.begin pending packet)
  afterAuthentication setup wire owner scalar authenticated

theorem after_agreement_erasure (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (result : RustM agreement.AgreementEffect) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Prod.fst <$> (RegistrationNativeFinishFactor.afterAgreement (n := n) setup wire result).run env = afterAgreement setup wire result := by
  cases result with
  | fail error | div => simp only [RegistrationNativeFinishFactor.afterAgreement, afterAgreement, StateT.run_pure, map_pure]
  | ok phase => cases phase with
    | BeaconComplete agreed =>
        have erased := simulation (RegistrationNativeBeaconPhaseCommutation.record (n := n) setup wire)
          (RegistrationNativeRecordJournal.core setup wire) (record_leaf setup wire) (RegistrationBeaconRecordExecutor.begin agreed) env
        have projected := congrArg (fun work => RegistrationNativeFinishFactor.collapse <$> work) erased
        simpa only [RegistrationNativeFinishFactor.afterAgreement, afterAgreement, StateT.run_map, Functor.map_map] using projected
    | _ => simp only [RegistrationNativeFinishFactor.afterAgreement, afterAgreement, StateT.run_pure, map_pure]

theorem accepted_erasure (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Prod.fst <$> (RegistrationNativeFinishFactor.accepted (n := n) setup wire owner scalar authenticated).run env = accepted setup wire owner scalar authenticated := by
  unfold RegistrationNativeFinishFactor.accepted accepted
  exact bind_erasure _ _ _ _
    (simulation _ _ (agreement_leaf setup owner scalar) _) (after_agreement_erasure setup wire) env

theorem after_authentication_erasure (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (reply : RustM RegistrationResponseExecutor.ResponseResult)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Prod.fst <$> (RegistrationNativeFinishFactor.afterAuthentication (n := n) setup wire owner scalar reply).run env = afterAuthentication setup wire owner scalar reply := by
  cases reply with
  | fail error | div => simp only [RegistrationNativeFinishFactor.afterAuthentication, afterAuthentication, StateT.run_pure, map_pure]
  | ok result => cases result with
    | Err control => simp only [RegistrationNativeFinishFactor.afterAuthentication, afterAuthentication, StateT.run_pure, map_pure]
    | Ok authenticated => exact accepted_erasure setup wire owner scalar authenticated env

theorem body_erasure (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Prod.fst <$> (RegistrationNativeFinishFactor.body (n := n) setup wire pending packet owner scalar).run env = body setup wire pending packet owner scalar := by
  unfold RegistrationNativeFinishFactor.body body
  exact bind_erasure _ _ _ _
    (simulation _ _ (authentication_leaf (source := source) setup) _) (after_authentication_erasure setup wire owner scalar) env


end BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure.simulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure.simulation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure.authentication_leaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure.authentication_leaf

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure.agreement_leaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure.agreement_leaf

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure.record_leaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure.record_leaf

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure.bind_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure.bind_erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure.after_agreement_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure.after_agreement_erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure.accepted_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure.accepted_erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure.after_authentication_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure.after_authentication_erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure.body_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure.body_erasure
