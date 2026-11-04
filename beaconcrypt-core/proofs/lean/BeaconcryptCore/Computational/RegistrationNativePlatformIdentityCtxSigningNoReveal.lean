-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReplay
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal

/-! Passthrough signing counters/logs add no reveal capability. The exact current typed and full raw source runs therefore have empty replay reveals beside their unchanged complete private source, physical cache and platform fields. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningNoReveal
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativePlatformIdentityCtxSigningLog (Trace logging)
open RegistrationNativePlatformIdentityCtxNoReveal (Allowed)
open RegistrationNativePlatformIdentityCtxKeyJournal (Whole)
open RegistrationNativeStageTrace (Call)
variable {S A : Type}

private theorem mapped {I A B : Type} {queries : OracleSpec I} (work : OracleComp queries A)
    (change : A → B) (predicate : I → Prop) (safe : work.AllQueriesSatisfy predicate) :
    (change <$> work).AllQueriesSatisfy predicate := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind safe (fun _ => allQueriesSatisfy_pure _ _)

/-- The signing logger forwards the same original requests, independent of every reply and analysis state. -/
theorem logging_safe (tag : Option Nat) (work : OracleComp Spec A) (allowed : work.AllQueriesSatisfy Allowed) (before : Trace) :
    ((simulateQ (logging tag) work).run before).AllQueriesSatisfy Allowed := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    apply allQueriesSatisfy_bind
    · apply mapped
      exact (allQueriesSatisfy_query_iff _ _).mpr allowed.1
    · intro result
      exact ih result.1 (allowed.2 result.1) result.2

/-- The public attempt marker and passthrough analysis log preserve no-reveal for a complete adaptive typed tree. -/
theorem wrap_program_safe (frontend : QueryImpl TypedSpec (StateT S (OracleComp Spec)))
    (safe : ∀ query before, ((frontend query).run before).AllQueriesSatisfy Allowed)
    (work : OracleComp TypedSpec A) (before : S × Trace) :
    ((simulateQ (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend) work).run before).AllQueriesSatisfy Allowed := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    apply allQueriesSatisfy_bind
    · apply mapped
      exact logging_safe _ ((frontend query).run before.1) (safe query before.1) _
    · intro result
      exact ih result.1 result.2

variable {V : Type}
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "actual" => RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint frontend

local notation "signedFrontend" => RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend

/-- All actual current callbacks, including dynamic writer failures and corrected finish, discharge the no-reveal language condition internally. -/
theorem actual_program_safe (work : OracleComp TypedSpec V)
    (before : (RegistrationNativeIdentityMain.State n KemSK source × Platform) × Trace) :
    ((simulateQ signedFrontend work).run before).AllQueriesSatisfy Allowed :=
  wrap_program_safe frontend (RegistrationNativePlatformIdentityCtxNoReveal.handler_safe setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer) work before

/-- The actual marked free source run has the same literal transcript replay with no reveals for any family size and any warmed physical cache/journal. -/
theorem initialized_reveals (count : Nat) (work : OracleComp TypedSpec V)
    (before : (RegistrationNativeIdentityMain.State n KemSK source × Platform) × Trace)
    (physical : RegistrationNativePlatformCtxBackend.State)
    (result : (V × ((RegistrationNativeIdentityMain.State n KemSK source × Platform) × Trace)) × RegistrationNativePlatformIdentityCtxSource.State)
    (reached : result ∈ support ((simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint)
      ((simulateQ signedFrontend work).run before)).run (PqxdhDynamicIdentityPool.initialState, physical))) :
    (RegistrationNativeIdentityHistory.replay count result.2.1.transcript).reveals = [] :=
  RegistrationNativePlatformIdentityCtxReplay.initialized_reveals setup.joint count _
    (actual_program_safe setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer work before)
    physical result reached

/-- Linking the actual callback and source interpreter retains the same no-reveal replay receipt on their full product state. -/
theorem linked_reveals (count : Nat) (work : OracleComp TypedSpec V)
    (before : (RegistrationNativeIdentityMain.State n KemSK source × Platform) × Trace)
    (physical : RegistrationNativePlatformCtxBackend.State)
    (result : V × Whole n KemSK Platform source)
    (reached : result ∈ support ((simulateQ actual work).run (before, (PqxdhDynamicIdentityPool.initialState, physical)))) :
    (RegistrationNativeIdentityHistory.replay count result.2.2.1.transcript).reveals = [] := by
  rw [RegistrationNativePlatformIdentityCtxSigningSource.typedHandler, QueryImpl.Stateful.simulateQ_link_run, support_map] at reached
  obtain ⟨inner, called, rfl⟩ := reached
  exact initialized_reveals setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer count work before physical inner called

/-- The original full raw compiler, original ledger, and actual same-run callback journal all retain the source-derived empty reveal history. -/
theorem full_reveals (count : Nat) (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (before : (RegistrationNativeIdentityMain.State n KemSK source × Platform) × Trace)
    (physical : RegistrationNativePlatformCtxBackend.State)
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work ((before, (PqxdhDynamicIdentityPool.initialState, physical)), []))) :
    (RegistrationNativeIdentityHistory.replay count result.2.2.1.2.1.transcript).reveals = [] := by
  rw [RegistrationNativeFullCompiler.compile_run, support_map] at reached
  obtain ⟨inner, called, rfl⟩ := reached
  have original := Set.mem_image_of_mem (Prod.map id Prod.fst) called
  rw [← support_map, RegistrationNativeStageTrace.erase] at original
  exact linked_reveals setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    count (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work) before physical (inner.1, inner.2.1) original

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningNoReveal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningNoReveal.logging_safe' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningNoReveal.logging_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningNoReveal.wrap_program_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningNoReveal.wrap_program_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningNoReveal.actual_program_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningNoReveal.actual_program_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningNoReveal.initialized_reveals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningNoReveal.initialized_reveals

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningNoReveal.linked_reveals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningNoReveal.linked_reveals

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningNoReveal.full_reveals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningNoReveal.full_reveals
