-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaProfile
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGenerateBounds
/-! The final initialized runtime platform profile has at most qCreate + 1 named ML generation attempts. Actual failed creates, allocator retries, source bundle writes, token-consuming builds and constructor failure remain in the counted execution. This bounds generation attempts rather than primitive coin counts, and assumes no primitive security conclusion. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaGenerateBounds
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
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

/-- Only create can issue a named generation attempt in the corrected source callback interpreter. -/
theorem handler (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform) :
    (((RegistrationNativePlatformOrdinaryMldsaProfile.handler setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query).run before).run previous).IsQueryBoundP IsGenerate
      (if RegistrationNativeRawAdapter.kind query = (1 : Fin 12) then 1 else 0) := by
  have original := RegistrationNativePlatformMldsaGenerateBounds.handler (n := n) setup checks
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential
    view failure allocation reserveRegistration reservePeer erased helper writer query before previous
  cases query with
  | inl coin => exact original
  | inr query => cases query with
    | serverSend keyId plaintext => exact ordinary _ before previous
    | serverRaw raw => exact ordinary _ before previous
    | beaconSend owner plaintext => exact ordinary _ before previous
    | beaconRaw owner raw => exact ordinary _ before previous
    | accept packet =>
        simp only [RegistrationNativePlatformOrdinaryMldsaProfile.handler, RegistrationNativePlatformMldsaProfile.handler,
          RegistrationNativeRawAdapter.kind, Fin.reduceEq, ite_false]
        generalize RegistrationNativePlatformExperiment.handler RegistrationNativePlatformMldsaProgram.coins setup checks
          (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created source credential
          view failure allocation reserveRegistration reservePeer erased helper writer
          (Sum.inr (RegistrationNativeRawAdapter.Command.accept packet)) = work
        exact ordinary work before previous
    | _ => exact original

/-- Both state layers retain the raw program's literal create-attempt cap. -/
theorem program (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = (1 : Fin 12)) cap)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform) :
    (((simulateQ (RegistrationNativePlatformOrdinaryMldsaProfile.handler setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer) work).run before).run previous).IsQueryBoundP IsGenerate cap :=
  RegistrationNativePlatformQueryBounds.simulate_bound _ IsGenerate _
    (handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
    work cap bounded before previous

/-- The actual compiler supplies the deployment's create budget without restricting failed bundle/build attempts. -/
theorem run (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform) :
    ((RegistrationNativePlatformOrdinaryMldsaProfile.run setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before).run previous).IsQueryBoundP IsGenerate budget.create := by
  unfold RegistrationNativePlatformOrdinaryMldsaProfile.run
  apply program setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    _ budget.create _ before previous
  simpa only [RegistrationNativeIdentityProfileCreateCaps.wrap_create_sum] using
    RegistrationNativeFullCompiler.compile_bound setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) created.server.server.metadata.sender bounds mode work budget bounded (1 : Fin 12)

/-- Startup contributes one additional attempt, even if generation fails; no later callback adds a hidden generation cost. -/
theorem profile (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicView, RegistrationNativeInterface.Respects budget (adversary publicView)) (previous : Platform) :
    ((RegistrationNativePlatformOrdinaryMldsaProfile.profile setup checks wire route representation ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary event).run previous).IsQueryBoundP IsGenerate (budget.create + 1) := by
  unfold RegistrationNativePlatformOrdinaryMldsaProfile.profile
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
          reserveRegistration reservePeer reserveFrame erased helper writer bounds mode (adversary initial.public) budget (bounded initial.public)
          initial.state initialized.2
end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaGenerateBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaGenerateBounds.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaGenerateBounds.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaGenerateBounds.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaGenerateBounds.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaGenerateBounds.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaGenerateBounds.run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaGenerateBounds.profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaGenerateBounds.profile
