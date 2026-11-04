-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaLiveOwners
import BeaconcryptCore.Computational.RegistrationNativeMldsaBundle

/-! Reified bundles preserve complete immutable owner metadata for every private capability reply, including arbitrary optional signature and private count. This support proof does not evaluate the named signing leaf through the opaque source's dummy closed signer. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaBundleOwnership
open RegistrationNativeBeaconFrontend (M Owner Phase)
open RegistrationNativeMldsaShared (Local lower close)
open RegistrationNativeOwnerFields (metadata)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeMldsaProgram (Spec)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem simulate_support {Query Other : Type} {queries : OracleSpec Query} {target : OracleSpec Other}
    (implementation : QueryImpl queries (OracleComp target)) (work : OracleComp queries Value)
    (value : Value) (supported : value ∈ support (simulateQ implementation work)) : value ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure input =>
      simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported ⊢
      exact supported
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
      obtain ⟨reply, _queried, continued⟩ := supported
      rw [mem_support_bind_iff]
      exact ⟨reply, mem_support_query query reply, ih reply continued⟩

private def SourceKeeps (work : M n KemSK source RegistrationServerRoleBackend.State Value) : Prop :=
  ∀ owners env result, result ∈ support ((work.run owners).run env) →
    result.1.2.map metadata = owners.map metadata
private def Keeps (work : StateT (Local n KemSK source) (OracleComp (Spec source)) Value) : Prop :=
  ∀ before result, result ∈ support (work.run before) → result.2.1.map metadata = before.1.map metadata

private theorem pure_keeps (value : Value) : Keeps (pure value : StateT (Local n KemSK source) _ Value) := by
  intro before result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl
private theorem bind_keeps (work : StateT (Local n KemSK source) (OracleComp (Spec source)) Value)
    (next : Value → StateT (Local n KemSK source) (OracleComp (Spec source)) Next)
    (first : Keeps work) (rest : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
  intro before result supported
  rw [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, queried, continued⟩ := supported
  exact (rest middle.1 middle.2 result continued).trans (first before middle queried)
private theorem simulate_keeps {Query : Type} {queries : OracleSpec Query}
    (implementation : QueryImpl queries (StateT (Local n KemSK source) (OracleComp (Spec source))))
    (law : ∀ query, Keeps (implementation query)) (work : OracleComp queries Value) : Keeps (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_keeps value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_keeps _ _ (law query) ih

private theorem native_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : M n KemSK source RegistrationServerRoleBackend.State Value) (law : SourceKeeps work) :
    Keeps (RegistrationNativeMldsaBundle.native setup checks representation created work) := by
  intro before result supported
  have actual : result ∈ support ((lower setup checks representation created work).run before) := by
    apply simulate_support RegistrationNativeMldsaProgram.ordinary _ result
    exact supported
  simp only [lower, StateT.run, support_map] at actual
  obtain ⟨inner, possible, same⟩ := actual
  cases same
  apply law before.1 before.2.1 inner.1
  apply OracleComp.support_simulateQ_run'_subset
    (RegistrationNativeExperiment.trusted setup checks representation created source) _ before.2.2
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst possible

private theorem source_lift (work : StateT (EnvState RegistrationServerRoleBackend.State)
    (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) Value) :
    SourceKeeps (StateT.lift work : M n KemSK source RegistrationServerRoleBackend.State Value) := by
  intro owners env result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  rfl
private theorem source_get : SourceKeeps
    (get : M n KemSK source RegistrationServerRoleBackend.State (RegistrationNativeBeaconFrontend.State source)) := by
  intro owners env result supported
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl
private theorem source_bind (work : M n KemSK source RegistrationServerRoleBackend.State Value)
    (next : Value → M n KemSK source RegistrationServerRoleBackend.State Next)
    (first : SourceKeeps work) (rest : ∀ value, SourceKeeps (next value)) : SourceKeeps (work >>= next) := by
  intro owners env result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, queried, continued⟩ := supported
  exact (rest middle.1.1 middle.1.2 middle.2 result continued).trans (first owners env middle queried)
private theorem source_pure (value : Value) :
    SourceKeeps (pure value : M n KemSK source RegistrationServerRoleBackend.State Value) := by
  intro owners env result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl
private theorem source_simulate {Query : Type} {queries : OracleSpec Query}
    (implementation : QueryImpl queries (M n KemSK source RegistrationServerRoleBackend.State))
    (law : ∀ query, SourceKeeps (implementation query)) (work : OracleComp queries Value) : SourceKeeps (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact source_pure value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact source_bind _ _ (law query) ih
private theorem source_sample (draw : ProbComp Value) :
    SourceKeeps (RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) (mldsaSource := source)
      (Auxiliary := RegistrationServerRoleBackend.State) draw) := by
  unfold RegistrationNativeBeaconFrontend.sample
  exact source_simulate (fun (query : unifSpec.Domain) => RegistrationNativeBeaconFrontend.effect (.inl query))
    (fun _ => source_lift _) draw
private theorem source_phase (index : Nat) (phase : Phase) :
    SourceKeeps (RegistrationNativeBeaconFrontend.updatePhase (n := n) (KemSK := KemSK) (mldsaSource := source)
      (Auxiliary := RegistrationServerRoleBackend.State) index phase) := by
  intro owners env result supported
  simp only [RegistrationNativeBeaconFrontend.updatePhase, StateT.run_modify, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at supported
  cases supported
  cases found : owners[index]? with
  | none => rfl
  | some owner =>
      simp only [List.map_set]
      have lookup : (owners.map metadata)[index]? = some (metadata owner) := by simp [found]
      obtain ⟨below, selected⟩ := List.getElem?_eq_some_iff.mp lookup
      change (owners.map metadata).set index (metadata owner) = owners.map metadata
      rw [← selected]
      exact List.set_getElem_self below

/-- Every reified outgoing Init callback retains the complete working owner metadata for all capability replies and private counts. -/
theorem outgoing (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) (before : Local n KemSK source)
    (result : RegistrationBeaconInitExecutor.Spec.Range query × Local n KemSK source)
    (supported : result ∈ support
      ((RegistrationNativeMldsaBundle.outgoing setup checks representation created index owner query).run before)) :
    result.2.1.map metadata = before.1.map metadata := by
  cases query with
  | inl query => cases query with
    | hash request =>
        apply native_keeps setup checks representation created _ ?_ before result supported
        intro owners env reached possible
        have law := RegistrationNativeOwnerFields.outgoing_metadata (n := n) setup source index owner
          (RegistrationBeaconInitExecutor.Spec.query (.inl (.hash request))) owners env reached
        simp only [simulateQ_spec_query] at law
        exact law possible
    | sign request payload digest =>
        simp only [RegistrationNativeMldsaBundle.outgoing, StateT.run, bind_pure_comp, support_map] at supported
        obtain ⟨reply, _possible, same⟩ := supported
        cases same
        rfl
  | inr request =>
      apply native_keeps setup checks representation created _ ?_ before result supported
      intro owners env reached possible
      have law := RegistrationNativeOwnerFields.outgoing_metadata (n := n) setup source index owner
        (RegistrationBeaconInitExecutor.Spec.query (.inr request)) owners env reached
      simp only [simulateQ_spec_query] at law
      exact law possible

/-- Arbitrary complete native Init continuations preserve owner metadata even under arbitrary reified private signer replies. -/
theorem program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) (owner : Owner source)
    (work : OracleComp RegistrationBeaconInitExecutor.Spec Value) (before : Local n KemSK source)
    (result : Value × Local n KemSK source)
    (supported : result ∈ support
      ((simulateQ (RegistrationNativeMldsaBundle.outgoing setup checks representation created index owner) work).run before)) :
    result.2.1.map metadata = before.1.map metadata :=
  simulate_keeps _ (outgoing setup checks representation created index owner) work before result supported

private theorem afterPublished_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (published : RustM (RegistrationBeaconInitExecutor.Result Pqxdh.Bytes)) :
    Keeps (RegistrationNativeMldsaBundle.afterPublished (n := n) setup checks representation created index owner oneTime published) := by
  cases published with
  | fail error | div => exact pure_keeps _
  | ok answer => cases answer with
    | Err previous => exact pure_keeps _
    | Ok completed =>
        unfold RegistrationNativeMldsaBundle.afterPublished
        apply bind_keeps _ _ (native_keeps setup checks representation created _ (source_phase index _))
        intro ignored
        exact bind_keeps _ _ (native_keeps setup checks representation created _ (source_lift _)) (fun _ => pure_keeps _)

/-- The entire reified bundle preserves all immutable native owner fields on every success or failure path. -/
theorem bundle (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) (before : Local n KemSK source)
    (result : RustM (Option Pqxdh.Bytes) × Local n KemSK source)
    (supported : result ∈ support ((RegistrationNativeMldsaBundle.bundle setup checks wire representation created index).run before)) :
    result.2.1.map metadata = before.1.map metadata := by
  have law : Keeps (RegistrationNativeMldsaBundle.bundle (n := n) (source := source) setup checks wire representation created index) := by
    unfold RegistrationNativeMldsaBundle.bundle
    apply bind_keeps _ _ (native_keeps setup checks representation created _ source_get)
    intro owners
    cases owners[index]? with
    | none => exact pure_keeps _
    | some owner =>
        dsimp only
        cases owner.phase with
        | fresh | freshWithCoins _ =>
            apply bind_keeps _ _ ?_
            · intro oneTime
              apply bind_keeps _ _ (program setup checks representation created index owner _)
              exact afterPublished_keeps setup checks representation created index owner oneTime
            · first | exact pure_keeps _ | exact native_keeps setup checks representation created _ (source_sample _)
        | _ => exact pure_keeps _
  exact law before result supported

/-- Closing the reified bundle restores the same complete old owner metadata into the original native envelope. -/
theorem sourceBundle (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : RustM (Option Pqxdh.Bytes) × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support
      ((RegistrationNativeMldsaBundle.sourceBundle setup checks wire representation created index).run before)) :
    result.2.beacons.map metadata = before.beacons.map metadata := by
  simp only [RegistrationNativeMldsaBundle.sourceBundle, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact bundle setup checks wire representation created index _ inner possible

/-- Arbitrary reified signing replies retain all already-reached live working owners at the same private table. -/
theorem program_live (actual : RegistrationNativeMldsa.Source) (pool : RegistrationNativeMldsaOpaque.Pool actual)
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat)
    (owner : Owner (RegistrationNativeMldsaOpaque.handleSource actual))
    (work : OracleComp RegistrationBeaconInitExecutor.Spec Value)
    (before : Local n KemSK (RegistrationNativeMldsaOpaque.handleSource actual))
    (result : Value × Local n KemSK (RegistrationNativeMldsaOpaque.handleSource actual))
    (live : RegistrationNativeMldsaPoolMap.OwnersLive actual pool before.1)
    (supported : result ∈ support
      ((simulateQ (RegistrationNativeMldsaBundle.outgoing setup checks representation created index owner) work).run before)) :
    RegistrationNativeMldsaPoolMap.OwnersLive actual pool result.2.1 :=
  RegistrationNativeMldsaLiveOwners.metadata_live actual pool before.1 result.2.1
    (program setup checks representation created index owner work before result supported) live

/-- The full reified bundle preserves live ML owner handles without evaluating any named capability reply through a dummy closed signer. -/
theorem sourceBundle_live (actual : RegistrationNativeMldsa.Source) (pool : RegistrationNativeMldsaOpaque.Pool actual)
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat)
    (before : RegistrationNativeExperiment.State n KemSK (RegistrationNativeMldsaOpaque.handleSource actual))
    (result : RustM (Option Pqxdh.Bytes) × RegistrationNativeExperiment.State n KemSK (RegistrationNativeMldsaOpaque.handleSource actual))
    (live : RegistrationNativeMldsaPoolMap.StateLive actual pool before)
    (supported : result ∈ support
      ((RegistrationNativeMldsaBundle.sourceBundle setup checks wire representation created index).run before)) :
    RegistrationNativeMldsaPoolMap.StateLive actual pool result.2 :=
  RegistrationNativeMldsaLiveOwners.metadata_live actual pool before.beacons result.2.beacons
    (sourceBundle setup checks wire representation created index before result supported) live

end BeaconcryptCore.Computational.RegistrationNativeMldsaBundleOwnership
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBundleOwnership.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBundleOwnership.outgoing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBundleOwnership.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBundleOwnership.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBundleOwnership.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBundleOwnership.bundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBundleOwnership.sourceBundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBundleOwnership.sourceBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBundleOwnership.program_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBundleOwnership.program_live
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBundleOwnership.sourceBundle_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBundleOwnership.sourceBundle_live
