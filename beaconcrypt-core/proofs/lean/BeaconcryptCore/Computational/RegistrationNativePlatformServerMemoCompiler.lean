-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerPrepared
import BeaconcryptCore.Computational.RegistrationNativePlatformServerCompilerJoint
/-! The concrete corrected build compiler preserves its actual optional private memo lookup. Its literal moved-token query property justifies replacing that lookup by the total earlier-root table, while the same effectful platform and private World continue on every reply. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerMemoCompiler
open RegistrationNativeRetainedRoots (Memo)
open RegistrationServerReferenceRestore (Roots)
open RegistrationNativePlatformServerPrepared (Backed)
open RegistrationNativePlatformServerFrontendCompiler (Spec target liftEffects embed implementation)
open RegistrationNativePlatformBoundCompiler (PublicState)
variable {n : Nat} {E Platform A : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]

omit primitive in
def DemandBacked (memo : Memo) (roots : Roots) : (Spec n).Domain → Prop
  | .inl message => memo message = some (roots message)
  | .inr _ => True

omit primitive in
noncomputable def optional (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (memo : Memo) :
    QueryImpl (Spec n) (StateT (PqxdhRecordLiftWorld.State n) ProbComp)
  | .inl message => pure ((memo message).map fun root =>
      RegistrationNativePairedChoice.Choice.known (PqxdhServerAuthKeySchedule.fromRoot source root))
  | .inr query => RegistrationNativePlatformWorldEffectView.implementation query

omit primitive in
private theorem effects_all (memo : Memo) (roots : Roots)
    (work : StateT (PublicState Platform) (OracleComp (RegistrationNativePlatformEffectCompiler.Spec n)) A)
    (before : PublicState Platform) :
    ((liftEffects work).run before).AllQueriesSatisfy (DemandBacked (n := n) memo roots) := by
  change (simulateQ embed (work.run before)).AllQueriesSatisfy (DemandBacked (n := n) memo roots)
  induction work.run before using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, embed, allQueriesSatisfy_query_bind_iff]
      exact ⟨trivial, ih⟩

section Leaves
variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (memo : Memo) (roots : Roots)

private theorem target_all (query : RegistrationNativePlatformServerFrontendProgram.Spec.Domain)
    (backed : Backed memo roots query) (before : PublicState Platform) :
    ((target (n := n) source view failure allocation erased helper sign writer reserve query).run before).AllQueriesSatisfy
      (DemandBacked (n := n) memo roots) := by
  cases query with
  | pin current => exact effects_all memo roots _ before
  | adHash pending => exact effects_all memo roots _ before
  | reserve => exact effects_all memo roots _ before
  | present keyId => exact effects_all memo roots _ before
  | service control initial message =>
      simp only [target, RegistrationNativePlatformServerFrontendCompiler.service, StateT.run_bind,
        StateT.run_lift, bind_pure_comp, bind_map_left, allQueriesSatisfy_query_bind_iff]
      refine ⟨backed, ?_⟩
      intro selected
      cases selected with
      | none => trivial
      | some choice => exact effects_all memo roots _ before

/-- Only actual earlier prepared descriptors reach a material query in the compiled dynamic build. -/
theorem compiled_backed (work : OracleComp RegistrationNativePlatformServerFrontendProgram.Spec A)
    (backed : work.AllQueriesSatisfy (Backed memo roots)) (before : PublicState Platform) :
    ((simulateQ (target (n := n) source view failure allocation erased helper sign writer reserve) work).run before).AllQueriesSatisfy
      (DemandBacked (n := n) memo roots) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at backed
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact allQueriesSatisfy_bind
        (target_all (n := n) source view failure allocation erased helper sign writer reserve memo roots query backed.1 before)
        (fun result => ih result.1 (backed.2 result.1) result.2)

end Leaves

omit primitive in
private theorem query_equal (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (memo : Memo) (roots : Roots)
    (query : (Spec n).Domain) (backed : DemandBacked (n := n) memo roots query) :
    optional source memo query = implementation source roots query := by
  cases query with
  | inl message =>
      change memo message = some (roots message) at backed
      simp only [optional, implementation, backed, Option.map_some]
  | inr query => rfl

omit primitive in
private theorem simulate_equal (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (memo : Memo) (roots : Roots)
    (work : OracleComp (Spec n) A) (backed : work.AllQueriesSatisfy (DemandBacked (n := n) memo roots)) :
    simulateQ (optional source memo) work = simulateQ (implementation source roots) work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at backed
      simp only [simulateQ_bind, simulateQ_spec_query]
      rw [query_equal source memo roots query backed.1]
      apply bind_congr
      intro reply
      exact ih reply (backed.2 reply)

/-- The literal corrected one-use build has its actual optional-memo interpretation, without presuming that arbitrary material requests were prepared. -/
theorem build (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (memo : Memo) (roots : Roots)
    (handle : Nat) (application : Option (Slice U8)) (front : RegistrationServerMaterialFrontend.State)
    (before : PublicState Platform) (world : PqxdhRecordLiftWorld.State n)
    (live : RegistrationServerMaterialRoots.Live front memo)
    (consistent : ∀ message root, memo message = some root → roots message = root) :
    (simulateQ (optional source memo)
      ((simulateQ (target (n := n) source view failure allocation erased helper sign writer reserve)
        ((RegistrationNativePlatformServerFrontendProgram.program handle application).run front)).run before)).run world =
    (simulateQ (implementation source roots)
      ((simulateQ (target (n := n) source view failure allocation erased helper sign writer reserve)
        ((RegistrationNativePlatformServerFrontendProgram.program handle application).run front)).run before)).run world := by
  rw [simulate_equal source memo roots _ (compiled_backed (n := n) source view failure allocation erased helper sign writer reserve memo roots _
    (RegistrationNativePlatformServerPrepared.build_backed memo roots handle application front live consistent) before)]

/-- The same literal source build has the real optional-memo free-client marginal. Its complete Native/cost marginal remains the separate exact source receipt. -/
theorem source_marginal {ι KemSK Reader Response : Type} {base : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (memo : Memo) (roots : Roots)
    (handle : Nat) (application : Option (Slice U8)) (front : RegistrationServerMaterialFrontend.State)
    (before : RegistrationServerRootCompiler.Local n) (previous : Platform)
    (live : RegistrationServerMaterialRoots.Live front memo)
    (consistent : ∀ message root, memo message = some root → roots message = root) :
    RegistrationNativePlatformServerCompilerJoint.clientView <$>
      RegistrationNativePlatformServerCompilerJoint.joint setup codec view failure allocation erased helper sign writer reserve roots
        handle application front before previous =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (optional setup.source memo)
          ((simulateQ (target (n := n) setup.source view failure allocation erased helper sign writer reserve)
            ((RegistrationNativePlatformServerFrontendProgram.program handle application).run front)).run
              (RegistrationNativePlatformBoundCompiler.strip (before, previous)).1)).run
                (RegistrationNativePlatformBoundCompiler.strip (before, previous)).2 := by
  rw [RegistrationNativePlatformServerCompilerJoint.client_marginal,
    RegistrationNativePlatformServerFrontendCompiler.interpret]
  rw [← build setup.source view failure allocation erased helper sign writer reserve memo roots handle application front
    (RegistrationNativePlatformBoundCompiler.strip (before, previous)).1
    (RegistrationNativePlatformBoundCompiler.strip (before, previous)).2 live consistent]

end BeaconcryptCore.Computational.RegistrationNativePlatformServerMemoCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerMemoCompiler.compiled_backed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerMemoCompiler.compiled_backed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerMemoCompiler.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerMemoCompiler.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerMemoCompiler.source_marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerMemoCompiler.source_marginal
