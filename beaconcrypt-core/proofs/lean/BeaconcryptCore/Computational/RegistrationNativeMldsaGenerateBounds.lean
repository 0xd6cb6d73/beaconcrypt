-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaNoGenerate
import BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityProfileCreateCaps

/-! Actual named ML generation has a syntactic attempt bill independent of primitive coin counts or optional key-generation success. Only Server startup calls generation. Beacon creation makes no named ML request. Bundle/build and every other original callback are generation-free on all reply paths. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds
attribute [local irreducible] RegistrationNativeExperiment.handler
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaProgram (Spec)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK State Value : Type} {base : OracleSpec ι} {source : Source}

instance allowedDecidable : DecidablePred (RegistrationNativeMldsaNoGenerate.Allowed source) := fun query => by
  rcases query with coin | call
  · exact instDecidableTrue
  · cases call
    · exact instDecidableFalse
    · exact instDecidableTrue

def IsGenerate (query : (Spec source).Domain) : Prop := ¬ RegistrationNativeMldsaNoGenerate.Allowed source query
instance : DecidablePred (IsGenerate (source := source)) := fun query => inferInstanceAs (Decidable (¬ RegistrationNativeMldsaNoGenerate.Allowed source query))

private theorem ordinary (work : ProbComp Value) :
    (RegistrationNativeMldsaProgram.lift (source := source) work).IsQueryBoundP IsGenerate 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_of_step
  all_goals simp [RegistrationNativeMldsaProgram.ordinary, IsGenerate, RegistrationNativeMldsaNoGenerate.Allowed,
    isQueryBoundP_query_iff]

private theorem lifted (work : StateT State ProbComp Value) (before : State) :
    ((RegistrationNativeMldsaProgram.liftState (source := source) work).run before).IsQueryBoundP IsGenerate 0 :=
  ordinary (work.run before)

private theorem generated (accounting : RegistrationNativeMldsaCapability.Accounting) (before : PqxdhRecordLiftWorld.State n) :
    ((RegistrationNativeMldsaProgram.call (source := source) accounting .generate).run before).IsQueryBoundP IsGenerate 1 := by
  simp [RegistrationNativeMldsaProgram.call, StateT.run, IsGenerate, RegistrationNativeMldsaNoGenerate.Allowed]

/-- Current Beacon construction makes no ML generation request. -/
theorem create_no_generate (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    ((RegistrationNativeMldsaCreation.create setup checks representation created edPin mlPin keyId).run before).IsQueryBoundP IsGenerate 0 :=
  lifted _ before

/-- The existing coarse resource ceiling is implied by the exact zero-generation source result. -/
theorem create (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    ((RegistrationNativeMldsaCreation.create setup checks representation created edPin mlPin keyId).run before).IsQueryBoundP IsGenerate 1 :=
  (create_no_generate setup checks representation created edPin mlPin keyId before).mono (Nat.zero_le 1)

/-- Actual startup attempts generation at most once, including constructor rejection and every generated-key failure branch. -/
theorem start (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64) :
    (RegistrationNativeMldsaCreation.start (n := n) (source := source) setup ensureInit identityIndex serverKid).IsQueryBoundP IsGenerate 1 := by
  unfold RegistrationNativeMldsaCreation.start
  apply isQueryBoundP_bind (n := 0) (m := 1) (ordinary _)
  intro constructed _
  cases selected : constructed.1.1 with
  | none => exact isQueryBoundP_pure _ _ _
  | some created =>
    apply isQueryBoundP_bind (m := 0) (generated .native constructed.2)
    intro generated _
    cases generated.1 with
    | none => exact isQueryBoundP_pure _ _ _
    | some credential =>
      apply isQueryBoundP_bind (n := 0) (m := 0) (ordinary _)
      intro initialized _
      cases initialized.1 <;> try exact isQueryBoundP_pure _ _ _
      rename_i answer
      cases answer <;> exact isQueryBoundP_pure _ _ _

private theorem no_generate (work : OracleComp (Spec source) Value)
    (safe : work.AllQueriesSatisfy (RegistrationNativeMldsaNoGenerate.Allowed source)) :
    work.IsQueryBoundP IsGenerate 0 :=
  (isQueryBoundP_zero_iff work (RegistrationNativeMldsaNoGenerate.Allowed source)).mpr safe

/-- The former per-create ceiling remains a conservative resource upper bound. Actual Beacon creation has zero generation, as create_no_generate establishes. -/
theorem handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : RegistrationNativeExperiment.State n KemSK source) :
    ((RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query).run before).IsQueryBoundP
      IsGenerate (if RegistrationNativeRawAdapter.kind query = (1 : Fin 12) then 1 else 0) := by
  cases query with
  | inl coin => exact lifted _ before
  | inr query => cases query with
    | create edPin mlPin keyId => exact create setup checks representation created edPin mlPin keyId before
    | bundle index => exact no_generate _ (RegistrationNativeMldsaNoGenerate.Bundle.sourceBundle source setup checks representation created wire index before)
    | build index application =>
      change ((fun result => (result.1, { before with server := result.2 })) <$>
        (RegistrationNativeMldsaServer.build source credential setup (RegistrationNativeWire.ledgerCodec wire) checks wire.encodeResponse index application).run before.server).IsQueryBoundP IsGenerate 0
      simpa only [isQueryBoundP_map_iff] using
        no_generate _ (RegistrationNativeMldsaNoGenerate.Server.build source credential setup (RegistrationNativeWire.ledgerCodec wire)
          checks wire.encodeResponse index application before.server)
    | _ => exact lifted _ before

/-- After the single Server startup generation, every current typed callback makes zero ML generation requests. -/
theorem handler_no_generate (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : RegistrationNativeExperiment.State n KemSK source) :
    ((RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query).run before).IsQueryBoundP
      IsGenerate 0 := by
  cases query with
  | inl coin => exact lifted _ before
  | inr query => cases query with
    | create edPin mlPin keyId => exact create_no_generate setup checks representation created edPin mlPin keyId before
    | bundle index => exact no_generate _ (RegistrationNativeMldsaNoGenerate.Bundle.sourceBundle source setup checks representation created wire index before)
    | build index application =>
      change ((fun result => (result.1, { before with server := result.2 })) <$>
        (RegistrationNativeMldsaServer.build source credential setup (RegistrationNativeWire.ledgerCodec wire) checks wire.encodeResponse index application).run before.server).IsQueryBoundP IsGenerate 0
      simpa only [isQueryBoundP_map_iff] using
        no_generate _ (RegistrationNativeMldsaNoGenerate.Server.build source credential setup (RegistrationNativeWire.ledgerCodec wire)
          checks wire.encodeResponse index application before.server)
    | _ => exact lifted _ before

/-- Arbitrary adaptive post-startup execution cannot generate any further ML key. -/
theorem program_no_generate (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential source)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    ((simulateQ (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential) work).run before).IsQueryBoundP IsGenerate 0 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact isQueryBoundP_bind (n := 0) (m := 0)
        (handler_no_generate setup checks wire route representation created credential query before)
        (fun result _ => ih result.1 result.2)

/-- Every adaptive typed source run inherits its literal create-attempt cap as a named ML generation cap. -/
theorem program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential source)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = (1 : Fin 12)) cap)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    ((simulateQ (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential) work).run before).IsQueryBoundP IsGenerate cap := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [counted, ite_true] using handler setup checks wire route representation created credential query current
  · intro query free current
    simpa only [free, ite_false] using handler setup checks wire route representation created credential query current

/-- First-candidate stopping cannot add named generation attempts; the same typed create cap applies for arbitrary fixed post-stop replies. -/
theorem stopped {Candidate : Type} (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential source)
    (observe : RegistrationNativeMldsaStop.Observer (spec := RegistrationNativeRawAdapter.TypedSpec)
      (State := RegistrationNativeExperiment.State n KemSK source) (Candidate := Candidate))
    (defaultReply : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = (1 : Fin 12)) cap)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Option Candidate) :
    ((simulateQ (RegistrationNativeMldsaStop.freeze (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential)
      observe defaultReply) work).run (before, previous)).IsQueryBoundP IsGenerate cap := by
  have step (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
      (current : RegistrationNativeExperiment.State n KemSK source × Option Candidate) :
      ((RegistrationNativeMldsaStop.freeze (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential)
        observe defaultReply query).run current).IsQueryBoundP IsGenerate
          (if RegistrationNativeRawAdapter.kind query = (1 : Fin 12) then 1 else 0) := by
    rcases current with ⟨current, previous⟩
    cases previous with
    | none =>
      simpa only [RegistrationNativeMldsaStop.freeze, RegistrationNativeMldsaStop.monitor, StateT.run, bind_pure_comp,
        isQueryBoundP_map_iff] using handler setup checks wire route representation created credential query current
    | some candidate => exact isQueryBoundP_pure _ _ _
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [counted, ite_true] using step query current
  · intro query free current
    simpa only [free, ite_false] using step query current

/-- The literal full native compiler supplies exactly the original raw adversary create budget to named generation. -/
theorem run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (before : RegistrationNativeExperiment.State n KemSK source) :
    (RegistrationNativeMldsaProfile.run setup checks wire route representation created credential bounds mode work before).IsQueryBoundP IsGenerate budget.create := by
  unfold RegistrationNativeMldsaProfile.run
  rw [isQueryBoundP_map_iff]
  apply program setup checks wire route representation created credential _ budget.create _ before
  simpa only [RegistrationNativeIdentityProfileCreateCaps.wrap_create_sum] using
    RegistrationNativeFullCompiler.compile_bound setup.source.crypto wire created.server.server.metadata.sender bounds mode work budget bounded (1 : Fin 12)

end BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds.create

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds.start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds.start

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds.stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds.stopped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds.run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds.create_no_generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds.create_no_generate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds.handler_no_generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds.handler_no_generate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds.program_no_generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds.program_no_generate
