-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression
import BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule

/-! Suppression's original selected-block interpreter with the successfully written Init retained for later transcript hashing. Suppressed signing and writing blocks remain unexecuted. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionLogged
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhEd25519EufCma
open PqxdhBeaconPhase1Publication
open PqxdhDeploymentPublicationSuppression
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A : Type}

def afterLogged (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes)
    (pool : PqxdhDynamicIdentityPool.SourceState) (selection : Selection)
    (logged : Option Phase1Candidate) : (NativeResult KemSK × Selection) × Option Phase1Candidate :=
  let prepared := nativeCurrent setup index owner generated
  let next := selection.next prepared
  if next.blocks prepared then ((((none, owner), pool), next), logged)
  else ((PqxdhRegistrationJointBundle.after setup codec index owner generated pool, next),
    PqxdhRegistrationJointBundle.afterLog setup codec owner generated logged)

def traceLogged (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState)
    (selection : Selection) (logged : Option Phase1Candidate) :
    ProbComp ((NativeResult KemSK × Selection) × Option Phase1Candidate) :=
  match owner.beacon.phase with
  | .fresh _ _ _ => (fun scalar => afterLogged setup codec index owner (some scalar) pool selection logged) <$> sampleScalar
  | _ => pure (afterLogged setup codec index owner none pool selection logged)

theorem afterLogged_fst (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes)
    (pool : PqxdhDynamicIdentityPool.SourceState) (selection : Selection) (logged : Option Phase1Candidate) :
    (afterLogged setup codec index owner generated pool selection logged).1 =
      after setup codec index owner generated pool selection := by
  unfold afterLogged after
  dsimp only
  split <;> rfl

theorem traceLogged_fst (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState)
    (selection : Selection) (logged : Option Phase1Candidate) :
    Prod.fst <$> traceLogged setup codec index owner pool selection logged =
      trace setup codec index owner pool selection := by
  cases phase : owner.beacon.phase <;>
    simp only [traceLogged, trace, phase, Functor.map_map, map_pure, afterLogged_fst]

def interpreted (auxiliary : A) (result : (NativeResult KemSK × Selection) × Option Phase1Candidate) :=
  ((result.1.1.1, result.1.2), (result.1.1.2, (auxiliary, result.2)))

/-- The unchanged indexed signer executes only the nonsuppressed block and logs exactly its successful writer input. -/
theorem afterGenerated_logged (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes)
    (pool : PqxdhDynamicIdentityPool.SourceState) (auxiliary : A) (selection : Selection)
    (logged : Option Phase1Candidate) (created : pool.seeds[index]? = some owner.beacon.identity) :
    (simulateQ (PqxdhLiveJointSigning.impl setup.joint
      (PqxdhRegistrationJointBundle.generate (A := A × Option Phase1Candidate))
      (PqxdhRegistrationJointServiceSchedule.writerLog codec))
      (afterGenerated (PqxdhRegistrationSchedule.projection setup index) generated owner selection)).run
        (pool, (auxiliary, logged)) =
      pure (interpreted auxiliary (afterLogged setup codec index owner generated pool selection logged)) := by
  simp only [afterGenerated]
  by_cases blocked : (selection.next (current (PqxdhRegistrationSchedule.projection setup index) owner generated)).blocks
      (current (PqxdhRegistrationSchedule.projection setup index) owner generated) = true
  · simp only [blocked, ite_true, simulateQ_pure, StateT.run_pure, afterLogged, nativeCurrent, interpreted]
  · simp only [blocked, Bool.false_eq_true, ite_false]
    rw [simulateQ_map, StateT.run_map, PqxdhLiveJointSigning.afterGenerated_source setup.joint
      (PqxdhRegistrationJointBundle.generate (A := A × Option Phase1Candidate))
      (PqxdhRegistrationJointServiceSchedule.writerLog codec)
      (PqxdhRegistrationSchedule.projection setup index) generated owner (pool, (auxiliary, logged))
      owner.beacon.identity created]
    unfold PqxdhLiveJointSigning.sourceAfter
    cases prepared : prepare owner generated with
    | none => simp [prepared, afterLogged, interpreted, nativeCurrent, blocked,
        PqxdhRegistrationJointBundle.after, PqxdhRegistrationJointBundle.afterLog]
    | some prepared =>
      simp only [prepared, PqxdhRegistrationSchedule.projection,
        afterSigning, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      simp only [StateT.run, PqxdhRegistrationJointServiceSchedule.writerLog, pure_bind]
      split <;> simp_all [afterLogged, interpreted, nativeCurrent, PqxdhRegistrationJointBundle.after,
        PqxdhRegistrationJointBundle.afterLog, simulateQ_pure]
      all_goals rfl

/-- The complete suppressed bundle keeps its one-time draw, signing state, selection and retained Init together. -/
theorem source_client_logged (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState)
    (auxiliary : A) (selection : Selection) (logged : Option Phase1Candidate)
    (created : pool.seeds[index]? = some owner.beacon.identity) :
    (simulateQ (PqxdhLiveJointSigning.impl setup.joint
      (PqxdhRegistrationJointBundle.generate (A := A × Option Phase1Candidate))
      (PqxdhRegistrationJointServiceSchedule.writerLog codec))
      (client (PqxdhRegistrationSchedule.projection setup index) owner selection)).run (pool, (auxiliary, logged)) =
      interpreted auxiliary <$> traceLogged setup codec index owner pool selection logged := by
  cases phase : owner.beacon.phase <;> simp only [client, traceLogged, phase]
  case fresh =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, Functor.map_map]
    have generation : (PqxdhLiveJointSigning.impl setup.joint
        (PqxdhRegistrationJointBundle.generate (A := A × Option Phase1Candidate))
        (PqxdhRegistrationJointServiceSchedule.writerLog codec) (.inl ())).run (pool, (auxiliary, logged)) =
        (fun scalar => (some scalar, (pool, (auxiliary, logged)))) <$> sampleScalar := by
      rw [PqxdhLiveJointSigning.generation_complete]
      simp only [PqxdhRegistrationJointBundle.generate, StateT.run_lift, bind_pure_comp, Functor.map_map]
    rw [generation, bind_map_left]
    conv_rhs => rw [map_eq_bind_pure_comp]
    apply bind_congr
    intro scalar
    exact afterGenerated_logged setup codec index owner (some scalar) pool auxiliary selection logged created
  case freshWithCoins =>
    simpa only [map_pure] using afterGenerated_logged setup codec index owner none pool auxiliary selection logged created
  all_goals simp [afterLogged, interpreted, nativeCurrent, current, prepare, phase, Selection.blocks,
    PqxdhRegistrationJointBundle.after, PqxdhRegistrationJointBundle.afterLog]

/-- Handle erasure preserves the complete logged suppression client and actual indexed signer state. -/
theorem client_logged (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index kemIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (pool : PqxdhDynamicIdentityPool.SourceState) (auxiliary : A) (selection : Selection)
    (logged : Option Phase1Candidate) (created : pool.seeds[index]? = some owner.beacon.identity) :
    (simulateQ (PqxdhLiveJointSigning.impl setup.joint
      (PqxdhRegistrationJointBundle.generate (A := A × Option Phase1Candidate))
      (PqxdhRegistrationJointServiceSchedule.writerLog codec))
      (client (PqxdhRegistrationJointBundle.projection setup)
        (PqxdhRegistrationJointBundle.encode setup index kemIndex owner) selection)).run (pool, (auxiliary, logged)) =
      (fun result => (((result.1.1.1.1, PqxdhRegistrationJointBundle.encode setup index kemIndex result.1.1.1.2),
        result.1.2), (result.1.1.2, (auxiliary, result.2)))) <$>
        traceLogged setup codec index owner pool selection logged := by
  rw [show PqxdhRegistrationJointBundle.encode setup index kemIndex owner =
      mapState (PqxdhRegistrationJointBundle.identityMap setup index)
        (PqxdhRegistrationJointBundle.keyMap kemIndex) owner from rfl,
    ← client_map (PqxdhRegistrationJointBundle.identityMap setup index)
      (PqxdhRegistrationJointBundle.keyMap kemIndex) (PqxdhRegistrationSchedule.projection setup index)
      (PqxdhRegistrationJointBundle.projection setup) (fun _ => rfl) (fun _ => rfl) rfl (fun _ => rfl)]
  rw [simulateQ_map, StateT.run_map, source_client_logged setup codec index owner pool auxiliary selection logged created,
    Functor.map_map]
  rfl

/-- Logging leaves the private service compiler's complete selection and KEM pool semantics unchanged. -/
theorem compiled_logged (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index kemIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (pool : PqxdhLiveKemBirth.State KemSK) (selection : Selection) (logged : Option Phase1Candidate)
    (created : pool.1.seeds[index]? = some owner.beacon.identity) :
    (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
      ((simulateQ (PqxdhRegistrationJointServiceSchedule.logCompiler codec)
        (client (PqxdhRegistrationJointBundle.projection setup)
          (PqxdhRegistrationJointBundle.encode setup index kemIndex owner) selection)).run logged)).run pool =
      (fun result => ((((result.1.1.1.1, PqxdhRegistrationJointBundle.encode setup index kemIndex result.1.1.1.2),
        result.1.2), result.2), (result.1.1.2, pool.2))) <$>
        traceLogged setup codec index owner pool.1 selection logged := by
  rw [PqxdhRegistrationJointServiceSchedule.log_interpreted setup codec _ logged pool,
    client_logged setup codec index kemIndex owner pool.1 pool.2 selection logged created,
    Functor.map_map]

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionLogged

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionLogged.afterLogged_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionLogged.afterLogged_fst

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionLogged.traceLogged_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionLogged.traceLogged_fst

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionLogged.afterGenerated_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionLogged.afterGenerated_logged

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionLogged.source_client_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionLogged.source_client_logged

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionLogged.client_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionLogged.client_logged

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionLogged.compiled_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionLogged.compiled_logged
