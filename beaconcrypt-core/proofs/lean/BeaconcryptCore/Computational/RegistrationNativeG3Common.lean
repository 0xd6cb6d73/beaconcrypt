-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3BeaconInsertion
import BeaconcryptCore.Computational.RegistrationBoundSourceCompiler
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore

/-! The native common service keeps chronological signing receipts beside the actual shared World. Publication uses only hash/coin effects, so every actual prefix retains the entire private seed cache and role-use map before installation. These local source facts supply the cache/use receipts needed by the known-versus-hidden installation coupling. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3Common
open PqxdhRecordLiftInterface (EnvEffects)
variable {n : Nat} {Value : Type}

abbrev State (n : Nat) := List RegistrationSigningShared.Receipt × PqxdhRecordLiftWorld.State n

noncomputable def publication (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationBoundPublication.Spec (StateT (State n) ProbComp) :=
  (PqxdhRecordLiftWorld.effects.mapStateTBase (RegistrationBoundSourceCompiler.compiler source writer sign)).flattenStateT

noncomputable def effect : QueryImpl (EnvEffects n) (StateT (State n) ProbComp) := fun query before =>
  (fun result => (result.1, (before.1, result.2))) <$> (PqxdhRecordLiftWorld.effects query).run before.2

noncomputable def handler (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl (RegistrationNativePairedServerService.Common n) (StateT (State n) ProbComp)
  | .inl query => publication source writer sign query
  | .inr query => effect query

def view (before : State n) : State n := (before.1, RegistrationNativeHiddenWorldInstall.view before.2)

def Primitive : (EnvEffects n).Domain → Prop
  | .inl _ | .inr (.hash _) => True
  | _ => False

private theorem every {Index : Type} {spec : OracleSpec Index} (work : OracleComp spec Value) :
    AllQueriesSatisfy work (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private theorem coins_primitive (work : ProbComp Value) :
    AllQueriesSatisfy (PqxdhDeploymentEnvironment.coins (n := n) work) Primitive := by
  apply RegistrationNativeHiddenAllocationCore.simulation _ (fun _ => True) Primitive _ work (every work)
  intro query _
  exact (allQueriesSatisfy_query_iff _ _).mpr trivial

private theorem shared_primitive (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (query : MldsaSharedNative.Spec.Domain) :
    AllQueriesSatisfy (RegistrationBoundSourceCompiler.sharedCompiler (n := n) source writer query) Primitive := by
  cases query with
  | inl query => exact (allQueriesSatisfy_query_iff _ _).mpr trivial
  | inr query =>
      change AllQueriesSatisfy (simulateQ (PqxdhDeploymentEnvironment.primFwd source.crypto source)
        (RawCtxMixedShared.sharedAdapter source.crypto writer query)) Primitive
      apply RegistrationNativeHiddenAllocationCore.simulation _ (fun _ => True) Primitive _ _ (every _)
      intro request _
      rcases request with request | (bytes | input)
      · trivial
      · exact RegistrationNativeHiddenAllocationCore.mapped _ _ Primitive ((allQueriesSatisfy_query_iff _ _).mpr trivial)
      · trivial

/-- The actual native record/hash/signing compiler emits only World hashes and coins, including failed signatures and optional writing. -/
theorem compiler_primitive (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationBoundPublication.Spec.Domain) (receipts : List RegistrationSigningShared.Receipt) :
    AllQueriesSatisfy ((RegistrationBoundSourceCompiler.compiler (n := n) source writer sign query).run receipts) Primitive := by
  cases query with
  | inl query =>
      apply RegistrationNativeHiddenAllocationCore.mapped _ _ Primitive
      exact RegistrationNativeHiddenAllocationCore.simulation _ (fun _ => True) Primitive
        (fun request _ => shared_primitive source writer request) _ (every _)
  | inr query => cases query with
    | hash request => exact RegistrationNativeHiddenAllocationCore.mapped _ _ Primitive ((allQueriesSatisfy_query_iff _ _).mpr trivial)
    | sign request payload digest => exact RegistrationNativeHiddenAllocationCore.mapped _ _ Primitive (coins_primitive _)

/-- Actual hash/coin effects keep the complete seed table and role-use map, retaining all current primitive counters and CTX updates. -/
theorem effect_keeps (query : (EnvEffects n).Domain) (allowed : Primitive query)
    (before : PqxdhRecordLiftWorld.State n)
    (result : (EnvEffects n).Range query × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.effects query).run before)) :
    result.2.seeds = before.seeds ∧ result.2.used = before.used := by
  cases query with
  | inl coin =>
      simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.sampled,
        StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨reply, _sampled, rfl⟩ := supported
      exact ⟨rfl, rfl⟩
  | inr request => cases request with
    | hash bytes =>
        simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.sampled,
          StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
        obtain ⟨reply, _sampled, rfl⟩ := supported
        exact ⟨rfl, rfl⟩
    | _ => exact allowed.elim

/-- Any adaptive actual hash/coin component preserves the private cache/use coordinates before its caller resumes. -/
theorem effects_keep (work : OracleComp (EnvEffects n) Value) (safe : AllQueriesSatisfy work Primitive)
    (before : PqxdhRecordLiftWorld.State n) (result : Value × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects work).run before)) :
    result.2.seeds = before.seeds ∧ result.2.used = before.used := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact ⟨rfl, rfl⟩
  | query_bind query next ih =>
      obtain ⟨allowed, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, stepped, continued⟩ := supported
      have first := effect_keeps query allowed before middle stepped
      have rest := ih middle.1 (later middle.1) middle.2 continued
      exact ⟨rest.1.trans first.1, rest.2.trans first.2⟩

/-- Every actual publication callback preserves the seed/use inputs required by the subsequent native installation. -/
theorem publication_keeps (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationBoundPublication.Spec.Domain) (before : State n)
    (result : RegistrationBoundPublication.Spec.Range query × State n)
    (supported : result ∈ support ((publication source writer sign query).run before)) :
    result.2.2.seeds = before.2.seeds ∧ result.2.2.used = before.2.used := by
  rcases before with ⟨receipts, world⟩
  simp only [publication, QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨reached, actual, rfl⟩ := supported
  exact effects_keep _ (compiler_primitive source writer sign query receipts) world reached actual

/-- A complete chronological native publication retains the same reached seed cache and all earlier role uses. -/
theorem publication_program_keeps (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationBoundPublication.Spec Value) (before : State n)
    (result : Value × State n)
    (supported : result ∈ support ((simulateQ (publication source writer sign) work).run before)) :
    result.2.2.seeds = before.2.seeds ∧ result.2.2.used = before.2.used := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact ⟨rfl, rfl⟩
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, stepped, continued⟩ := supported
      have first := publication_keeps source writer sign query before middle stepped
      have rest := ih middle.1 middle.2 continued
      exact ⟨rest.1.trans first.1, rest.2.trans first.2⟩

/-- Pure publication embedding uses the same current receipt/World interpreter without a captured outer environment. -/
theorem publication_lift (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationBoundPublication.Spec Value) :
    simulateQ (handler (n := n) source writer sign) (simulateQ RegistrationHiddenInstall.publicationLift work) =
      simulateQ (publication source writer sign) work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : handler (n := n) source writer sign ∘ₛ RegistrationHiddenInstall.publicationLift =
      publication source writer sign := by
    funext query
    simp only [QueryImpl.compose, RegistrationHiddenInstall.publicationLift, simulateQ_spec_query, handler]
  rw [same]

/-- Actual environment suffixes preserve current chronological receipts and run on the reached shared World. -/
theorem effect_program (work : OracleComp (EnvEffects n) Value) (before : State n) :
    (simulateQ effect work).run before =
      (fun result => (result.1, (before.1, result.2))) <$>
        (simulateQ PqxdhRecordLiftWorld.effects work).run before.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      change ((effect query >>= fun reply => simulateQ effect (next reply)).run before) =
        (fun result => (result.1, (before.1, result.2))) <$>
          ((PqxdhRecordLiftWorld.effects query >>= fun reply => simulateQ PqxdhRecordLiftWorld.effects (next reply)).run before.2)
      rw [StateT.run_bind, StateT.run_bind]
      simp only [effect, StateT.run, bind_map_left, map_bind]
      apply bind_congr
      intro result
      exact ih result.1 (before.1, result.2)

/-- Common environment embedding forwards the same exact mutable World program. -/
theorem effect_lift (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (EnvEffects n) Value) :
    simulateQ (handler source writer sign) (simulateQ RegistrationHiddenInstall.effectLift work) =
      simulateQ effect work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : handler source writer sign ∘ₛ RegistrationHiddenInstall.effectLift = effect (n := n) := by
    funext query
    simp only [QueryImpl.compose, RegistrationHiddenInstall.effectLift, simulateQ_spec_query, handler]
  rw [same]

end BeaconcryptCore.Computational.RegistrationNativeG3Common
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3Common.compiler_primitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3Common.compiler_primitive
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3Common.effect_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3Common.effect_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3Common.effects_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3Common.effects_keep
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3Common.publication_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3Common.publication_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3Common.publication_program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3Common.publication_program_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3Common.publication_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3Common.publication_lift
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3Common.effect_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3Common.effect_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3Common.effect_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3Common.effect_lift
