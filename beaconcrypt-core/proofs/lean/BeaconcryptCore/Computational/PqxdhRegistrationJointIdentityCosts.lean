-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCompiler

/-! Query accounting for the actual initialized joint-identity reduction. The private signing/DH/create/reveal caps survive source-index routing, while all local KEM/runtime uniform work remains in the complete evaluated bill. No native macro or ambient work is declared free. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCosts
open PqxdhJointIdentity PqxdhDynamicIdentityPool PqxdhServerAuthExperiment
open PqxdhRegistrationJointServiceCosts (Kind poolClass)
open PqxdhRegistrationJointIdentityRouting (Registry Spec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Result Reader Response : Type}

/-- The ordinary joint-game request classes retain the existing source ledger names. -/
def dynamicKind : DynamicSpec.Domain → Kind
  | .inl _ => .uniform
  | .inr request => poolClass (KemSK := Unit) (.inl (.inr request))

/-- Known import emits no generated-identity capability; ambient random queries retain their own explicit class. -/
def sourceKind : Spec.Domain → Option Kind
  | .inl query => some (dynamicKind query)
  | .inr (.inl _) => some .uniform
  | .inr (.inr _) => none

set_option backward.isDefEq.respectTransparency false in
/-- Source-index routing forwards at most one request of the same private class; caller-known services and missing handles add none. This bound covers every typed challenger reply. -/
theorem route_step (joint : Primitives) (query : Spec.Domain) (registry : Registry) (kind : Kind) :
    ((PqxdhRegistrationJointIdentityRouting.route joint query).run registry).IsQueryBoundP
      (fun query => dynamicKind query = kind) (if sourceKind query = some kind then 1 else 0) := by
  rcases query with (coin | request) | (coin | seed)
  case inl.inl =>
    by_cases same : .uniform = kind <;>
      simp [PqxdhRegistrationJointIdentityRouting.route, StateT.run, sourceKind, dynamicKind, poolClass,
        isQueryBoundP_map_iff, isQueryBoundP_query_iff, same]
  case inr.inl =>
    by_cases same : .uniform = kind <;>
      simp [PqxdhRegistrationJointIdentityRouting.route, StateT.run, sourceKind, dynamicKind, poolClass,
        isQueryBoundP_map_iff, isQueryBoundP_query_iff, same]
  case inr.inr => simp [PqxdhRegistrationJointIdentityRouting.route, StateT.run]
  case inl.inr =>
    cases request with
    | create =>
        by_cases same : .identityCreate = kind <;>
          simp [PqxdhRegistrationJointIdentityRouting.route, StateT.run, sourceKind, dynamicKind, poolClass,
            isQueryBoundP_query_bind_iff, same]
        all_goals rintro (_ | generated) <;> simp
    | service index request =>
        cases found : registry.refs[index]? with
        | none => simp [PqxdhRegistrationJointIdentityRouting.route, StateT.run, found]
        | some reference =>
            cases reference with
            | known seed => simp [PqxdhRegistrationJointIdentityRouting.route, StateT.run, found]
            | generated target =>
                cases request <;> cases kind <;>
                  simp [PqxdhRegistrationJointIdentityRouting.route, StateT.run, found, sourceKind, dynamicKind, poolClass,
                    bind_pure_comp, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    | reveal index =>
        cases found : registry.refs[index]? with
        | none => simp [PqxdhRegistrationJointIdentityRouting.route, StateT.run, found]
        | some reference =>
            cases reference with
            | known seed => simp [PqxdhRegistrationJointIdentityRouting.route, StateT.run, found]
            | generated target =>
                cases kind <;>
                  simp [PqxdhRegistrationJointIdentityRouting.route, StateT.run, found, sourceKind, dynamicKind, poolClass,
                    bind_pure_comp, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

/-- The complete adaptive registry router preserves each source-class cap on all typed replies and all starting registries. -/
theorem route_program (joint : Primitives) (program : OracleComp Spec Result) (registry : Registry)
    (kind : Kind) (budget : Nat) (bounded : program.IsQueryBoundP (fun query => sourceKind query = some kind) budget) :
    ((simulateQ (PqxdhRegistrationJointIdentityRouting.route joint) program).run registry).IsQueryBoundP
      (fun query => dynamicKind query = kind) budget :=
  bounded.simulateQ_run_StateT_of_step (fun query before => route_step joint query before kind) registry

/-- Local runtime/KEM computation contains only explicit ambient random queries at this interface; it contributes no nonuniform identity request. Its full evaluated random bill remains separate. -/
theorem coins_nonuniform (work : ProbComp Result) (kind : Kind) (nonuniform : kind ≠ .uniform) :
    (PqxdhRegistrationJointIdentityCompiler.coins work).IsQueryBoundP
      (fun query => sourceKind query = some kind) 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => simp [PqxdhRegistrationJointIdentityCompiler.coins]
  | query_bind query next ih =>
      simp only [PqxdhRegistrationJointIdentityCompiler.coins, simulateQ_bind, simulateQ_spec_query,
        isQueryBoundP_query_bind_iff, sourceKind, Option.some.injEq, Ne.symm nonuniform,
        not_false_eq_true, true_or, ite_false, true_and]
      exact ih

set_option backward.isDefEq.respectTransparency false in
/-- Every actual constructor/backend callback emits at most its existing source-private cap. Local KEM operations are explicitly executed, not counted as external identity queries. -/
theorem compiler_step (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (query : (PqxdhRegistrationJointServerBirth.Spec KemSK).Domain)
    (state : PqxdhRegistrationJointIdentityCompiler.Local KemSK A) (kind : Kind) (nonuniform : kind ≠ .uniform) :
    ((PqxdhRegistrationJointIdentityCompiler.impl setup ensureInit query).run state).IsQueryBoundP
      (fun query => sourceKind query = some kind)
      (if PqxdhRegistrationJointOpenInitializedCosts.classify (KemSK := KemSK) query = some kind then 1 else 0) := by
  rcases query with (query | (coin | query)) | request
  case inl.inl =>
    cases query with
    | inl coin =>
        cases kind <;> simp_all [PqxdhRegistrationJointIdentityCompiler.impl, PqxdhRegistrationJointIdentityCompiler.forward,
          StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff, sourceKind, dynamicKind,
          PqxdhRegistrationJointOpenInitializedCosts.classify, poolClass]
    | inr request =>
        cases request with
        | create => cases kind <;>
          simp [PqxdhRegistrationJointIdentityCompiler.impl, PqxdhRegistrationJointIdentityCompiler.forward,
            StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff, sourceKind, dynamicKind,
            PqxdhRegistrationJointOpenInitializedCosts.classify, poolClass]
        | reveal index => cases kind <;>
          simp [PqxdhRegistrationJointIdentityCompiler.impl, PqxdhRegistrationJointIdentityCompiler.forward,
            StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff, sourceKind, dynamicKind,
            PqxdhRegistrationJointOpenInitializedCosts.classify, poolClass]
        | service index call => cases call <;> cases kind <;>
          simp [PqxdhRegistrationJointIdentityCompiler.impl, PqxdhRegistrationJointIdentityCompiler.forward,
            StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff, sourceKind, dynamicKind,
            PqxdhRegistrationJointOpenInitializedCosts.classify, poolClass]
  case inl.inr.inl =>
    cases kind <;> simp_all [PqxdhRegistrationJointIdentityCompiler.impl, PqxdhRegistrationJointIdentityCompiler.forward,
      StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff, sourceKind,
      PqxdhRegistrationJointOpenInitializedCosts.classify, poolClass]
  case inl.inr.inr =>
    exact (coins_nonuniform _ kind nonuniform).mono (Nat.zero_le _)
  case inr =>
    cases request with
    | «initialize» => exact coins_nonuniform _ kind nonuniform
    | importSeed seed =>
        simp [PqxdhRegistrationJointIdentityCompiler.impl, PqxdhRegistrationJointIdentityCompiler.forward,
          StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff, sourceKind]

/-- Compiling local KEM/runtime work preserves the all-reply nonuniform source-private cap for the entire actual program. -/
theorem compiler_program (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (program : OracleComp (PqxdhRegistrationJointServerBirth.Spec KemSK) Result)
    (state : PqxdhRegistrationJointIdentityCompiler.Local KemSK A) (kind : Kind) (nonuniform : kind ≠ .uniform)
    (budget : Nat) (bounded : program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointOpenInitializedCosts.classify (KemSK := KemSK) query = some kind) budget) :
    ((simulateQ (PqxdhRegistrationJointIdentityCompiler.impl setup ensureInit) program).run state).IsQueryBoundP
      (fun query => sourceKind query = some kind) budget :=
  bounded.simulateQ_run_StateT_of_step (fun query before => compiler_step setup ensureInit query before kind nonuniform) state

/-- The executable ordinary-joint-game reduction retains the source-private cap through both complete compilers, without restrictions on intermediate replies or source indices. -/
theorem reduction_private (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (program : OracleComp (PqxdhRegistrationJointServerBirth.Spec KemSK) Result)
    (state : PqxdhRegistrationJointIdentityCompiler.Local KemSK A) (registry : Registry)
    (kind : Kind) (nonuniform : kind ≠ .uniform) (budget : Nat)
    (bounded : program.IsQueryBoundP (fun query => PqxdhRegistrationJointOpenInitializedCosts.classify (KemSK := KemSK) query = some kind) budget) :
    (PqxdhRegistrationJointIdentityCompiler.reduction setup ensureInit program state registry).IsQueryBoundP
      (fun query => dynamicKind query = kind) budget :=
  route_program setup.joint _ registry kind budget (compiler_program setup ensureInit program state kind nonuniform budget bounded)

/-- Actual initialized source scheduling supplies the ordinary joint game's generated-identity, signing, static-DH and live-read caps. Caller-known Server import never consumes a generated-target allowance. -/
theorem initialized_private (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (kind : Kind) (nonuniform : kind ≠ .uniform) :
    (PqxdhRegistrationJointIdentityCompiler.initialized setup codec checks ensureInit supplied program runtime).IsQueryBoundP
      (fun query => dynamicKind query = kind)
      ((if kind = .identityCreate ∧ supplied.isNone = true then 1 else 0) +
        PqxdhRegistrationJointOpenCosts.privateTotal budget kind) :=
  reduction_private setup ensureInit _ _ _ kind nonuniform _
    (PqxdhRegistrationJointOpenInitializedCosts.initialized_private setup codec checks supplied program budget certified kind nonuniform)

/-- The complete evaluated real ordinary-game execution pays the full original source bill, including identity generation, runtime initialization, KEM/base work and native HMAC/CTX callbacks. This is an evaluated uniform count, not a new uniform guarantee about a replaced challenger. -/
theorem initialized_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (supplied : Option Pqxdh.Bytes) (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    ((simulateQ (lazyImpl setup.joint)
      (PqxdhRegistrationJointIdentityCompiler.initialized setup codec checks ensureInit supplied program runtime)).run initialState).IsTotalQueryBound
      ((qInit + if supplied.isNone then 32 else 0) + ∑ source, PqxdhRegistrationJointRevealCosts.uniformCost caps source * budget source) := by
  have correspondence := PqxdhRegistrationJointIdentityCompiler.reduction_source setup ensureInit
    (PqxdhRegistrationJointOpenInitialization.client setup codec checks supplied program)
    (PqxdhLiveKemBirth.empty, runtime) (⟨[], []⟩, initialState) PqxdhRegistrationJointIdentityRouting.initial_valid
  have bound := PqxdhRegistrationJointOpenInitialization.interpreted_uniform setup codec checks ensureInit qInit initBound
    caps bounded supplied program budget certified
    ((PqxdhRegistrationJointIdentityRouting.project (⟨[], []⟩, initialState), PqxdhLiveKemBirth.empty), runtime)
  rw [← correspondence] at bound
  simpa only [PqxdhRegistrationJointIdentityCompiler.initialized, IsTotalQueryBound, isQueryBound_map_iff] using bound

end BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCosts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCosts.route_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCosts.route_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCosts.route_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCosts.route_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCosts.coins_nonuniform' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCosts.coins_nonuniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCosts.compiler_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCosts.compiler_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCosts.compiler_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCosts.compiler_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCosts.reduction_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCosts.reduction_private

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCosts.initialized_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCosts.initialized_private

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCosts.initialized_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCosts.initialized_uniform
