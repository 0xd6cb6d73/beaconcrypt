-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaNoGenerate
import BeaconcryptCore.Computational.RegistrationNativePlatformQueryBounds
/-! The corrected initialized source platform profile has at most qCreate + 1 named ML generation attempts. Actual failed creates, allocator retries, source bundle writes, token-consuming builds and constructor failure remain in the counted execution. This bounds generation attempts rather than primitive coin counts, and assumes no primitive security conclusion. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGenerateBounds
open BeaconcryptCore.Refinement
open RegistrationNativePlatformQuerySafety
open RegistrationNativePlatformMldsaProgram (M)
open RegistrationNativeMldsaNoGenerate (Allowed)
open RegistrationNativeMldsaGenerateBounds (IsGenerate)
open PqxdhServerAuthExperiment (Setup Checks)
variable {source : RegistrationNativeMldsa.Source} {Platform State Value : Type} {n : Nat}
variable {E ι KemSK : Type} {base : OracleSpec ι}

private theorem no_generate (work : OracleComp (RegistrationNativeMldsaProgram.Spec source) Value)
    (allowed : work.AllQueriesSatisfy (Allowed source)) : work.IsQueryBoundP IsGenerate 0 :=
  (isQueryBoundP_zero_iff work (Allowed source)).mpr allowed

private theorem inject_bound (work : StateT State (OracleComp (RegistrationNativeMldsaProgram.Spec source)) Value)
    (cap : Nat) (bounded : ∀ before, (work.run before).IsQueryBoundP IsGenerate cap)
    (before : State) (previous : Platform) :
    (((RegistrationNativePlatformMldsaProgram.inject work).run before).run previous).IsQueryBoundP IsGenerate cap := by
  change ((StateT.lift (work.run before) : M source Platform (Value × State)).run previous).IsQueryBoundP IsGenerate cap
  simpa only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff] using bounded before

private theorem ordinary (work : StateT State (StateT Platform ProbComp) Value) (before : State) (previous : Platform) :
    (((RegistrationNativePlatformMldsaProgram.lift (source := source) work).run before).run previous).IsQueryBoundP IsGenerate 0 :=
  no_generate _ (lift_safe (Allowed source) (fun _ => trivial) work before previous)

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

/-- Only create can issue a named generation attempt in the corrected source callback interpreter. -/
theorem handler (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform) :
    (((RegistrationNativePlatformMldsaProfile.handler setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer query).run before).run previous).IsQueryBoundP IsGenerate
      (if RegistrationNativeRawAdapter.kind query = (1 : Fin 12) then 1 else 0) := by
  cases query with
  | inl coin => exact ordinary _ before previous
  | inr query => cases query with
    | create edPin mlPin keyId =>
        exact inject_bound _ 1 (RegistrationNativeMldsaGenerateBounds.create setup checks representation created edPin mlPin keyId) before previous
    | bundle owner =>
        exact no_generate _ (RegistrationNativePlatformMldsaNoGenerate.Bundle.sourceBundle setup checks representation created writer owner before previous)
    | build session application =>
        apply no_generate
        apply bind_safe (Allowed source) _ _ _ (fun _ => pure_safe (Allowed source) _) before previous
        exact frame_safe (Allowed source) (fun current : RegistrationNativeExperiment.State n KemSK source => current.server)
          (fun current after => { current with server := after }) _
          (RegistrationNativePlatformMldsaNoGenerate.Server.build source credential setup (RegistrationNativeWire.ledgerCodec wire)
            view failure allocation erased reservePeer helper writer session application)
    | accept packet =>
        simp only [RegistrationNativePlatformMldsaProfile.handler, RegistrationNativeRawAdapter.kind, Fin.reduceEq, ite_false]
        generalize RegistrationNativePlatformExperiment.handler RegistrationNativePlatformMldsaProgram.coins setup checks wire
          route representation created source credential view failure allocation reserveRegistration reservePeer
          erased helper writer (Sum.inr (RegistrationNativeRawAdapter.Command.accept packet)) = work
        exact ordinary work before previous
    | _ => exact ordinary _ before previous

/-- Both state layers retain the raw program's literal create-attempt cap. -/
theorem program (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = (1 : Fin 12)) cap)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform) :
    (((simulateQ (RegistrationNativePlatformMldsaProfile.handler setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer) work).run before).run previous).IsQueryBoundP IsGenerate cap :=
  RegistrationNativePlatformQueryBounds.simulate_bound _ IsGenerate _
    (handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer)
    work cap bounded before previous

/-- The actual compiler supplies the deployment's create budget without restricting failed bundle/build attempts. -/
theorem run (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform) :
    ((RegistrationNativePlatformMldsaProfile.run setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer bounds mode work before).run previous).IsQueryBoundP IsGenerate budget.create := by
  unfold RegistrationNativePlatformMldsaProfile.run
  apply program setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
    _ budget.create _ before previous
  simpa only [RegistrationNativeIdentityProfileCreateCaps.wrap_create_sum] using
    RegistrationNativeFullCompiler.compile_bound setup.source.crypto wire created.server.server.metadata.sender bounds mode work budget bounded (1 : Fin 12)

/-- Startup contributes one additional attempt, even if generation fails; no later callback adds a hidden generation cost. -/
theorem profile (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicView, RegistrationNativeInterface.Respects budget (adversary publicView)) (previous : Platform) :
    ((RegistrationNativePlatformMldsaProfile.profile setup checks wire route representation ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer erased helper writer bounds mode adversary event).run previous).IsQueryBoundP IsGenerate (budget.create + 1) := by
  unfold RegistrationNativePlatformMldsaProfile.profile
  rw [StateT.run_bind, StateT.run_lift]
  have startup := RegistrationNativeMldsaGenerateBounds.start (n := n) (source := source) setup ensureInit identityIndex serverKeyId
  rw [Nat.add_comm budget.create 1]
  apply isQueryBoundP_bind (n := 1) (m := budget.create)
  · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using startup
  · intro initialized _
    cases initialized.1 with
    | none => exact isQueryBoundP_pure _ _ _
    | some initial =>
        rw [StateT.run_map, isQueryBoundP_map_iff]
        exact run setup checks wire route representation initial.created initial.credential view failure allocation
          reserveRegistration reservePeer erased helper writer bounds mode (adversary initial.public) budget (bounded initial.public)
          initial.state initialized.2
end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGenerateBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGenerateBounds.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGenerateBounds.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGenerateBounds.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGenerateBounds.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGenerateBounds.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGenerateBounds.run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGenerateBounds.profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGenerateBounds.profile
