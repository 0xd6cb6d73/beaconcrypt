-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleReceipt
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover
/-! The original issued event retains its actual before-b state and complete original suffix under a fixed public bundle cutoff. The finite guesses are analysis event coordinates; stopping observes only the public bundle ordinal. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCutProbability
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxKeyJournal (Whole)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeIdentityCensorBundlePrefix (Cut stop resume)
open RegistrationNativePlatformIdentityCtxFiniteCover (Issued acceptanceOrdinal bundleOrdinal)
variable {n : Nat} {KemSK Platform A : Type} {source : RegistrationNativeMldsa.Source}
abbrev State := Whole n KemSK Platform source
abbrev Result := A × (State (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) ×
  List (Call TypedSpec (State (n := n) (KemSK := KemSK) (Platform := Platform) (source := source))))
abbrev Stopped := Cut A × (State (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) ×
  List (Call TypedSpec (State (n := n) (KemSK := KemSK) (Platform := Platform) (source := source))))

noncomputable def coupled (joint : PqxdhJointIdentity.Primitives)
    (frontend : QueryImpl TypedSpec (StateT (RegistrationNativeIdentityMain.State n KemSK source × Platform)
      (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (bundle : Nat) (work : OracleComp TypedSpec A) (before : State (n := n) (KemSK := KemSK) (Platform := Platform) (source := source)) :
    ProbComp (Stopped (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) (A := A) × Result (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) (A := A)) := do
  let cut ← (simulateQ (RegistrationNativeStageTrace.handler (RegistrationNativePlatformIdentityCtxSigningSource.typedHandler joint frontend))
    (stop bundle work 0)).run (before,[])
  let result ← (simulateQ (RegistrationNativeStageTrace.handler (RegistrationNativePlatformIdentityCtxSigningSource.typedHandler joint frontend))
    (resume cut.1)).run cut.2
  pure (cut,result)

def At (joint : PqxdhJointIdentity.Primitives) (wire : RegistrationNativeWire.Wire) (budget : PqxdhDeploymentInterface.Budget)
    (selected accept bundle : Nat) (result : Result (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) (A := A)) : Prop :=
  ∃ attempt : RegistrationNativePlatformIdentityCtxCausalAttempt.Attempt joint wire budget result.2.2 result.2.1,
    attempt.finalOwner.identity.handle=selected ∧ (acceptanceOrdinal attempt).val=accept ∧
      ∃ issued : Issued attempt,(bundleOrdinal issued.cut).val=bundle

def Matched (joint : PqxdhJointIdentity.Primitives) (wire : RegistrationNativeWire.Wire) (budget : PqxdhDeploymentInterface.Budget)
    (selected accept bundle : Nat) (result : Stopped (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) (A := A) × Result (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) (A := A)) : Prop :=
  ∃ attempt : RegistrationNativePlatformIdentityCtxCausalAttempt.Attempt joint wire budget result.2.2.2 result.2.2.1,
    attempt.finalOwner.identity.handle=selected ∧ (acceptanceOrdinal attempt).val=accept ∧
      ∃ issued : Issued attempt,(bundleOrdinal issued.cut).val=bundle ∧
        ∃ next,result.1.1=Cut.bundle issued.cut.index next ∧ result.1.2.1=issued.cut.call.before

/-- Erasing only the public cutoff receipt returns the literal full original signed execution and its entire chronological private journal. -/
theorem full_marginal (joint : PqxdhJointIdentity.Primitives)
    (frontend : QueryImpl TypedSpec (StateT (RegistrationNativeIdentityMain.State n KemSK source × Platform)
      (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (bundle : Nat) (work : OracleComp TypedSpec A) (before : State (n := n) (KemSK := KemSK) (Platform := Platform) (source := source)) :
    Prod.snd <$> coupled joint frontend bundle work before =
      (simulateQ (RegistrationNativeStageTrace.handler (RegistrationNativePlatformIdentityCtxSigningSource.typedHandler joint frontend)) work).run (before,[]) := by
  simp only [coupled,map_bind,map_pure,bind_pure]
  exact (RegistrationNativeIdentityCensorBundlePrefix.execution bundle 0
    (RegistrationNativeStageTrace.handler (RegistrationNativePlatformIdentityCtxSigningSource.typedHandler joint frontend)) work (before,[])).symm

/-- Every correct original first-signing bundle is the SAME reached cutoff state, not merely some supported state at that ordinal. -/
theorem contains (joint : PqxdhJointIdentity.Primitives)
    (frontend : QueryImpl TypedSpec (StateT (RegistrationNativeIdentityMain.State n KemSK source × Platform)
      (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (bundle : Nat) (work : OracleComp TypedSpec A) (before : State (n := n) (KemSK := KemSK) (Platform := Platform) (source := source))
    (zero : before.1.2.nextBundle=0) (wire : RegistrationNativeWire.Wire) (budget : PqxdhDeploymentInterface.Budget)
    (selected accept : Nat) (result : Stopped (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) (A := A) × Result (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) (A := A))
    (reached : result ∈ support (coupled joint frontend bundle work before))
    (failed : At joint wire budget selected accept bundle result.2) : Matched joint wire budget selected accept bundle result := by
  simp only [coupled,mem_support_bind_iff,mem_support_pure_iff] at reached
  obtain ⟨cut,stopped,final,continued,rfl⟩ := reached
  obtain ⟨attempt,sameHandle,sameAccept,issued,sameBundle⟩ := failed
  have memberLeading : issued.cut.call ∈ attempt.leading :=
    (congrArg (fun calls => issued.cut.call ∈ calls) issued.cut.split).mpr
      (List.mem_append_right _ (List.mem_cons_self))
  have member : issued.cut.call ∈ final.2.2 :=
    (congrArg (fun calls => issued.cut.call ∈ calls) attempt.split).mpr
      (List.mem_append_left _ memberLeading)
  obtain ⟨next,sameCut,sameState⟩ := RegistrationNativeIdentityCensorBundleReceipt.signed_at_cut joint frontend bundle work before zero
    cut stopped final continued issued.cut.call member issued.cut.index issued.cut.queryEq sameBundle
  exact ⟨attempt,sameHandle,sameAccept,issued,sameBundle,next,sameCut,sameState⟩

/-- The unchanged original issued mass at fixed public i/a/b equals its exact before-b/whole-suffix coupling event. No private event controls the stopping code. -/
theorem probability (joint : PqxdhJointIdentity.Primitives)
    (frontend : QueryImpl TypedSpec (StateT (RegistrationNativeIdentityMain.State n KemSK source × Platform)
      (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (bundle : Nat) (work : OracleComp TypedSpec A) (before : State (n := n) (KemSK := KemSK) (Platform := Platform) (source := source))
    (zero : before.1.2.nextBundle=0) (wire : RegistrationNativeWire.Wire) (budget : PqxdhDeploymentInterface.Budget) (selected accept : Nat) :
    Pr{let result ← ((simulateQ (RegistrationNativeStageTrace.handler (RegistrationNativePlatformIdentityCtxSigningSource.typedHandler joint frontend)) work).run (before,[]))}[
      At joint wire budget selected accept bundle result] =
    Pr{let result ← (coupled joint frontend bundle work before)}[Matched joint wire budget selected accept bundle result] := by
  rw [←full_marginal joint frontend bundle work before,prEvent_map]
  apply prEvent_congr_of_support
  intro result reached
  constructor
  · exact contains joint frontend bundle work before zero wire budget selected accept result reached
  · rintro ⟨attempt,handle,accept,issued,bundle,_rest⟩
    exact ⟨attempt,handle,accept,issued,bundle⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCutProbability
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCutProbability.full_marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCutProbability.full_marginal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCutProbability.contains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCutProbability.contains
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCutProbability.probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCutProbability.probability
