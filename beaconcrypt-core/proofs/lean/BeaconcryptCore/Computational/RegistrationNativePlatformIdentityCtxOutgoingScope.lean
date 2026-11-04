-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEnvPatch
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityPublication

/-! The literal outgoing Init dictionary and full dynamic writer source AST satisfy the syntactic NoKem publication scope on every reply and failure. Independent ML sampling, source Ed signing, all hash calls and mutable writer draws remain present. No primitive security or controller equality is supplied as a premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingScope
open RegistrationNativeIdentityFrontend (M Trusted Ambient Owner)
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {I KemSK Auxiliary Platform Value Next : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

def NativeAllowed : (Trusted n KemSK).Domain → Prop := fun query =>
  RegistrationNativePlatformIdentityCtxEnvPatch.Allowed (n := n) (KemSK := KemSK) (.inr query)

def NativeWork (work : M n KemSK Auxiliary source Value) : Prop :=
  ∀ owners env, ((work.run owners).run env).AllQueriesSatisfy (NativeAllowed (n := n) (KemSK := KemSK))

def Work (work : RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source Value) : Prop :=
  ∀ owners env platform, (((work.run owners).run env).run platform).AllQueriesSatisfy
    (RegistrationNativePlatformIdentityCtxEnvPatch.Allowed (n := n) (KemSK := KemSK))

private theorem mapped {Index : Type} {queries : OracleSpec Index} {A B : Type}
    (work : OracleComp queries A) (change : A → B) (predicate : Index → Prop)
    (allowed : work.AllQueriesSatisfy predicate) : (change <$> work).AllQueriesSatisfy predicate := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind allowed (fun _ => allQueriesSatisfy_pure _ _)

private theorem native_pure (value : Value) : NativeWork (pure value : M n KemSK Auxiliary source Value) := by
  intro owners env
  simp only [StateT.run_pure]
  trivial

private theorem native_bind (work : M n KemSK Auxiliary source Value) (next : Value → M n KemSK Auxiliary source Next)
    (first : NativeWork work) (later : ∀ value, NativeWork (next value)) : NativeWork (work >>= next) := by
  intro owners env
  rw [StateT.run_bind, StateT.run_bind]
  exact allQueriesSatisfy_bind (first owners env) (fun result => later result.1.1 result.1.2 result.2)

private theorem native_program {Index : Type} {queries : OracleSpec Index}
    (handler : QueryImpl queries (M n KemSK Auxiliary source))
    (law : ∀ query, NativeWork (handler query)) (work : OracleComp queries Value) : NativeWork (simulateQ handler work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using native_pure value
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    exact native_bind _ _ (law query) ih

private theorem lifted (work : OracleComp (Trusted n KemSK) Value)
    (allowed : work.AllQueriesSatisfy (NativeAllowed (n := n) (KemSK := KemSK))) :
    NativeWork (StateT.lift (StateT.lift work) : M n KemSK Auxiliary source Value) := by
  intro owners env
  simp only [StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map]
  exact mapped work _ _ allowed

private theorem effect (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    NativeWork (RegistrationNativeIdentityFrontend.effect (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) query) :=
  lifted _ ((allQueriesSatisfy_query_iff _ _).mpr trivial)

private theorem sample (work : ProbComp Value) :
    NativeWork (RegistrationNativeIdentityFrontend.sample (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) work) :=
  native_program (fun query : unifSpec.Domain => RegistrationNativeIdentityFrontend.effect (.inl query))
    (fun _ => effect _) work

private theorem modified (change : RegistrationNativeIdentityFrontend.State source → RegistrationNativeIdentityFrontend.State source) :
    NativeWork (modify change : M n KemSK Auxiliary source Unit) := by
  intro owners env
  simp only [StateT.run_modify, StateT.run_pure]
  trivial

private theorem update (change : RegistrationWorldAgreementCompiler.EnvState Auxiliary → RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    NativeWork (RegistrationNativeIdentityFrontend.updateEnv (n := n) (KemSK := KemSK) (source := source) change) := by
  intro owners env
  simp only [RegistrationNativeIdentityFrontend.updateEnv, StateT.run_lift]
  trivial

/-- Every literal outgoing Init hash/ML/Ed callback belongs to the derived publication scope, including missing Ed/ML replies. -/
theorem native_outgoing (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    NativeWork (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner query) := by
  cases query with
  | inl query => cases query with
    | hash request => exact effect _
    | sign request payload digest =>
      exact native_bind _ _ (sample _) (fun reply => native_bind _ _ (update _) (fun _ => native_pure reply))
  | inr request =>
    simp only [RegistrationNativeIdentityFrontend.outgoing]
    split
    · apply native_bind _ _ (lifted _ ?_)
      · intro signature
        cases signature with
        | none => exact native_pure _
        | some signature => exact native_bind _ _ (modified _) (fun _ => native_pure _)
      · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
    · exact native_pure _

private theorem native_allowed {A : Type} (work : OracleComp (Trusted n KemSK) A)
    (allowed : work.AllQueriesSatisfy (NativeAllowed (n := n) (KemSK := KemSK))) :
    (simulateQ RegistrationNativePlatformIdentityProgram.nativeLift work).AllQueriesSatisfy
      (RegistrationNativePlatformIdentityCtxEnvPatch.Allowed (n := n) (KemSK := KemSK)) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformIdentityProgram.nativeLift]
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨allowed.1, fun reply => ih reply (allowed.2 reply)⟩

private theorem lifted_native (work : M n KemSK Auxiliary source Value) (allowed : NativeWork work) :
    Work (RegistrationNativePlatformIdentityProgram.native work : RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source Value) := by
  intro owners env platform
  simp only [RegistrationNativePlatformIdentityProgram.native, StateT.run]
  exact mapped _ _ _ (native_allowed _ (allowed owners env))

private theorem external_allowed {A : Type} (work : ProbComp A) :
    (simulateQ (RegistrationNativePlatformIdentityProgram.externalLift (n := n) (KemSK := KemSK)) work).AllQueriesSatisfy
      (RegistrationNativePlatformIdentityCtxEnvPatch.Allowed (n := n) (KemSK := KemSK)) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformIdentityProgram.externalLift]
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private theorem external (work : StateT Platform ProbComp Value) :
    Work (RegistrationNativePlatformIdentityProgram.external work : RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source Value) := by
  intro owners env platform
  simp only [RegistrationNativePlatformIdentityProgram.external, StateT.run]
  exact mapped _ _ _ (external_allowed _)

private theorem pure_work (value : Value) :
    Work (pure value : RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source Value) := by
  intro owners env platform
  simp only [StateT.run_pure]
  trivial

private theorem bind_work (work : RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source Value)
    (next : Value → RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source Next)
    (first : Work work) (later : ∀ value, Work (next value)) : Work (work >>= next) := by
  intro owners env platform
  rw [StateT.run_bind, StateT.run_bind, StateT.run_bind]
  exact allQueriesSatisfy_bind (first owners env platform)
    (fun result => later result.1.1.1 result.1.1.2 result.1.2 result.2)

/-- The complete actual dynamic publication source tree, including arbitrary stateful writer replies, satisfies the NoKem scope. -/
theorem publication {E : Type} (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (RegistrationNativePlatformWriter.Spec E) Value) :
    Work (simulateQ (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := Auxiliary) setup index owner writer) work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]; exact pure_work value
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    apply bind_work _ _ ?_ ih
    cases query with
    | inl query => exact lifted_native _ (native_outgoing setup index owner query)
    | inr query => exact external (writer query)

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingScope
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingScope.native_outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingScope.native_outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingScope.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingScope.publication
