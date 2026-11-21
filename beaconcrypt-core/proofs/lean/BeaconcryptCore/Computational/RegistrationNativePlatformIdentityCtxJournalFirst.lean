-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstBundleCut

/-! Every issued message before an actual acceptance has a strict earlier bundle cut at a bounded public all-attempt ordinal. The original full compiler supplies the complete source path and budget internally. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxJournalFirst
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxKeyJournal (Whole drop owners)
open RegistrationNativeStageTrace (Call Path Executed)
open RegistrationNativePlatformIdentityCtxFirstBundleCut (messages)
variable {V : Type}
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "actual" => RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint frontend


private theorem query_counter (query : TypedSpec.Domain) (before : Whole n KemSK Platform source)
    (result : TypedSpec.Range query × Whole n KemSK Platform source)
    (supported : result ∈ support ((actual query).run before)) :
    result.2.1.2.nextBundle = before.1.2.nextBundle +
      if RegistrationNativePlatformIdentityCtxSigningTrace.IsBundle query then 1 else 0 := by
  rw [RegistrationNativePlatformIdentityCtxSigningSource.typedHandler, QueryImpl.Stateful.link_impl_apply_run, support_map] at supported
  obtain ⟨inner, called, rfl⟩ := supported
  apply RegistrationNativePlatformIdentityCtxSigningTrace.query_counter frontend query before.1 inner.1
  apply support_simulateQ_run'_subset (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint) _ before.2
  rw [StateT.run'_eq, support_map]
  exact ⟨inner, called, rfl⟩

private theorem path_counter {first last : Whole n KemSK Platform source} {calls : List (Call TypedSpec (Whole n KemSK Platform source))}
    (path : Path actual first calls last) : first.1.2.nextBundle ≤ last.1.2.nextBundle := by
  induction path with
  | nil => exact Nat.le_refl _
  | cons call called rest last following ih =>
    have step := query_counter setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer call.query call.before (call.reply, call.after) called
    exact (by rw [step]; omega : call.before.1.2.nextBundle ≤ call.after.1.2.nextBundle).trans ih

/-- The complete original raw budget bounds the same run's all-attempt source bundle counter. -/
theorem full_counter (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : Whole n KemSK Platform source)
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (before, []))) :
    result.2.2.1.1.2.nextBundle ≤ before.1.2.nextBundle + budget.bundle := by
  rw [RegistrationNativeFullCompiler.compile_run, support_map] at reached
  obtain ⟨inner, called, rfl⟩ := reached
  have original := Set.mem_image_of_mem (Prod.map id Prod.fst) called
  rw [← support_map, RegistrationNativeStageTrace.erase] at original
  exact RegistrationNativePlatformIdentityCtxFirstBundleCut.budget setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work) budget.bundle
    (RegistrationNativeFullRegistrationJournal.bundle_bound setup.source.crypto wire serverKeyId bounds mode work budget bounded)
    before (inner.1, inner.2.1) original

/-- A message issued before an actual successful acceptance was first issued in a strict earlier source bundle, including failed publications. -/
theorem first_before (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (physical : RegistrationNativePlatformCtxBackend.State)
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (((before, {}), (PqxdhDynamicIdentityPool.initialState, physical)), [])))
    (earlier later : List (Call TypedSpec (Whole n KemSK Platform source)))
    (accepted : Call TypedSpec (Whole n KemSK Platform source)) (split : result.2.2.2 = earlier ++ accepted :: later)
    (identity : Nat) (message : Pqxdh.Bytes) (signed : message ∈ messages identity accepted.before) :
    ∃ leading chosen trailing index,
      earlier = leading ++ chosen :: trailing ∧
      Path actual ((before, {}), (PqxdhDynamicIdentityPool.initialState, physical)) leading chosen.before ∧
      Executed actual chosen ∧ Path actual chosen.after trailing accepted.before ∧
      chosen.query = .inr (.bundle index) ∧
      message ∉ messages identity chosen.before ∧ message ∈ messages identity chosen.after ∧
      chosen.before.1.2.nextBundle < budget.bundle := by
  have fullPath := RegistrationNativeFullRegistrationJournal.path setup.source.crypto wire serverKeyId bounds actual mode work _ result reached
  rw [split] at fullPath
  obtain ⟨prefixPath, acceptedCalled, suffixPath⟩ := RegistrationNativeRegistrationJournalCoverage.path_split actual _ _ earlier later accepted fullPath
  have laterBound := path_counter setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer (Path.cons accepted acceptedCalled later result.2.2.1 suffixPath)
  have counted := full_counter setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer serverKeyId bounds mode work budget bounded _ result reached
  have cap : accepted.before.1.2.nextBundle ≤ budget.bundle := by simpa only [Nat.zero_add] using laterBound.trans counted
  have initialCoherent : RegistrationNativePlatformIdentityCtxFirstBundleCut.coherent
      (((before, {}), (PqxdhDynamicIdentityPool.initialState, physical)) : Whole n KemSK Platform source) := rfl
  have fresh : message ∉ messages identity (((before, {}), (PqxdhDynamicIdentityPool.initialState, physical)) : Whole n KemSK Platform source) := List.not_mem_nil
  obtain ⟨leading, chosen, trailing, index, historySplit, previous, called, following, queryEq, _coherent, freshAt, signedAt, finite⟩ :=
    RegistrationNativePlatformIdentityCtxFirstBundleCut.first setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer prefixPath initialCoherent identity message fresh signed budget.bundle cap
  exact ⟨leading, chosen, trailing, index, historySplit, previous, called, following, queryEq, freshAt, signedAt, finite⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxJournalFirst

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxJournalFirst.full_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxJournalFirst.full_counter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxJournalFirst.first_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxJournalFirst.first_before
