-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceQueries
import BeaconcryptCore.Computational.RegistrationNativePlatformRuntimeMetricView
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetricView
import BeaconcryptCore.Computational.RegistrationAgreementNestedState
/-! The actual corrected adaptive public program restores the literal final fixed-scalar runtime on the same reached platform state. Internal source invariants are preserved by actual callback support, and instrumentation input independence is derived from actual runtime bodies. No original security event is restricted. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceProgram
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicSourceExecution (State execute)
open RegistrationNativePublicSourceState (roots restore project nativeView)
open RegistrationNativePlatformOrdinaryExperiment (canonicalWire)
open RegistrationNativePlatformPublicSourceGood (Good)
variable {n : Nat} {I KemSK Platform E Value : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem project_program {Index S T Result : Type} {spec : OracleSpec Index}
    (sourceImpl : QueryImpl spec (StateT S ProbComp)) (targetImpl : QueryImpl spec (StateT T ProbComp))
    (restore : S → T) (view : T → T) (idempotent : ∀ state, view (view state) = view state)
    (invariant : S → Prop)
    (keeps : ∀ query before result, invariant before → result ∈ support ((sourceImpl query).run before) → invariant result.2)
    (step : ∀ query before, invariant before →
      Prod.map id (view ∘ restore) <$> (sourceImpl query).run before =
        Prod.map id view <$> (targetImpl query).run (restore before))
    (stable : ∀ query, RegistrationStateView.Stable view (targetImpl query))
    (work : OracleComp spec Result) (before : S) (valid : invariant before) :
    Prod.map id (view ∘ restore) <$> (simulateQ sourceImpl work).run before =
      Prod.map id view <$> (simulateQ targetImpl work).run (restore before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq, Function.comp_def]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      calc
        _ = (sourceImpl query).run before >>= fun reached =>
            Prod.map id view <$> (simulateQ targetImpl (next reached.1)).run ((view ∘ restore) reached.2) := by
          apply bind_congr_of_forall_mem_support
          rintro ⟨value, after⟩ supported
          exact (ih value after (keeps query before (value, after) valid supported)).trans
            (RegistrationStateView.program_stable view idempotent targetImpl stable (next value) (restore after))
        _ = (Prod.map id (view ∘ restore) <$> (sourceImpl query).run before) >>= fun reached =>
            Prod.map id view <$> (simulateQ targetImpl (next reached.1)).run reached.2 := by
          rw [bind_map_left]
          rfl
        _ = (Prod.map id view <$> (targetImpl query).run (restore before)) >>= fun reached =>
            Prod.map id view <$> (simulateQ targetImpl (next reached.1)).run reached.2 := by rw [step query before valid]
        _ = _ := by
          rw [bind_map_left]
          apply bind_congr
          rintro ⟨value, after⟩
          exact (RegistrationStateView.program_stable view idempotent targetImpl stable (next value) after).symm


private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

def view (before : RegistrationNativeExperiment.State n KemSK source × Platform) :=
  (nativeView before.1, before.2)

private theorem idempotent (before : RegistrationNativeExperiment.State n KemSK source × Platform) : view (view before) = view before := by
  simp only [view, RegistrationNativeMainViewLift.view_idempotent]

private theorem flatten_stable
    (work : StateT (RegistrationNativeExperiment.State n KemSK source) (StateT Platform ProbComp) Value)
    (stable : RegistrationStateView.Stable nativeView work) :
    RegistrationStateView.Stable view (RegistrationAgreementNestedState.flatten work) := by
  intro before
  have actual := congrArg (fun action => action.run before.2) (stable before.1)
  have mapped := congrArg (fun action => (fun result => (result.1.1, (result.1.2, result.2))) <$> action) actual
  simpa only [RegistrationAgreementNestedState.flatten, StateT.run, map_apply,
    Functor.map_map, view, Prod.map_def, id_eq] using mapped

section Callbacks
variable [primitive : AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (selectedOwner selectedAccept : Nat) (scalar : PqxdhJointGapDh.ScalarBytes)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

noncomputable def native : QueryImpl RegistrationNativeRawAdapter.TypedSpec (RegistrationNativePlatformOrdinaryExperiment.M n KemSK source Platform) := RegistrationNativePlatformOrdinaryScalarEager.handler (n := n) setup checks wire route representation created source credential
  keyView failure allocation reserveRegistration reservePeer reserveFrame erased helper writer selectedOwner scalar
private noncomputable def sourceCallback : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (State n KemSK Platform source) ProbComp) := RegistrationNativePlatformPublicSourceInvariant.callback (n := n) setup checks (canonicalWire wire) route
  (RegistrationNativeMldsa.owned source credential) created.seed scalar selectedOwner selectedAccept (setup.dh.publicKey scalar)
  keyView failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
noncomputable def restoreState (before : State n KemSK Platform source) :=
  (restore (roots setup created.seed scalar) scalar before.1.1 before.2, before.1.2)

include correct in
private theorem step (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK Platform source)
    (good : Good setup created.seed scalar selectedOwner before) :
    Prod.map id (view ∘ restoreState setup created scalar) <$>
      (sourceCallback setup checks wire route created credential selectedOwner selectedAccept scalar keyView failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query).run before =
      Prod.map id view <$> (RegistrationAgreementNestedState.flatten
        (native setup checks wire route representation created credential selectedOwner scalar keyView failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer query)).run (restoreState setup created scalar before) := by
  have actual := RegistrationNativePlatformPublicSourceQueries.query setup checks wire route representation correct created credential selectedOwner selectedAccept scalar
    keyView failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before good
  have mapped := congrArg (fun action => (fun result => (result.1.1, (result.1.2, result.2))) <$> action) actual
  simpa only [sourceCallback, RegistrationNativePlatformPublicSourceInvariant.callback, native,
    RegistrationAgreementNestedState.flatten, StateT.run, restoreState, view, project,
    Functor.map_map, Prod.map_def, id_eq, Function.comp_def] using mapped

private theorem native_stable (query : RegistrationNativeRawAdapter.TypedSpec.Domain) :
    RegistrationStateView.Stable nativeView (native (n := n) setup checks wire route representation created credential selectedOwner scalar keyView failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query) := by
  cases query with
  | inl coin =>
    exact RegistrationNativePlatformRuntimeMetricView.nonbundle setup checks wire route representation created credential selectedOwner scalar
      keyView failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inl coin) trivial
  | inr command => cases command <;> first
    | exact RegistrationNativePlatformRuntimeMetricView.nonbundle setup checks wire route representation created credential selectedOwner scalar
        keyView failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ trivial
    | exact RegistrationNativePlatformBundleMetricView.bundle RegistrationNativePlatformMldsaProgram.coins setup checks representation created writer _

private theorem keeps (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK Platform source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK Platform source)
    (good : Good setup created.seed scalar selectedOwner before)
    (supported : result ∈ support ((sourceCallback setup checks wire route created credential selectedOwner selectedAccept scalar keyView failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query).run before)) :
    Good setup created.seed scalar selectedOwner result.2 := by
  have actual := RegistrationNativePlatformPublicSourceGood.program setup checks (canonicalWire wire) route (RegistrationNativeMldsa.owned source credential)
    created.seed scalar selectedOwner selectedAccept keyView failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    (RegistrationNativeRawAdapter.TypedSpec.query query) before result good
  apply actual
  simpa only [simulateQ_spec_query, sourceCallback, RegistrationNativePlatformPublicSourceInvariant.callback] using supported

include correct in
/-- Complete adaptive execution retains the original client result, Native security state and actual P, from derived initialized source invariants. -/
theorem program_source (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : State n KemSK Platform source)
    (good : Good setup created.seed scalar selectedOwner before) :
    Prod.map id (view ∘ restoreState setup created scalar) <$>
      (execute setup (canonicalWire wire) route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (simulateQ (RegistrationNativePlatformPublicFrontend.handler setup checks (canonicalWire wire) source
          (RegistrationNativeMldsa.owned source credential) selectedOwner selectedAccept (setup.dh.publicKey scalar)
          keyView failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work)).run before =
      Prod.map id view <$> (RegistrationAgreementNestedState.flatten
        (simulateQ (native setup checks wire route representation created credential selectedOwner scalar keyView failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer) work)).run (restoreState setup created scalar before) := by
  rw [← RegistrationNativePlatformPublicSourceInvariant.program_source setup checks (canonicalWire wire) route (RegistrationNativeMldsa.owned source credential)
    created.seed scalar selectedOwner selectedAccept (setup.dh.publicKey scalar) keyView failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer]
  rw [← RegistrationAgreementNestedState.program]
  exact project_program
    (sourceCallback setup checks wire route created credential selectedOwner selectedAccept scalar keyView failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer)
    (RegistrationAgreementNestedState.implementation (native setup checks wire route representation created credential selectedOwner scalar keyView failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer))
    (restoreState setup created scalar) view idempotent (Good setup created.seed scalar selectedOwner)
    (keeps setup checks wire route created credential selectedOwner selectedAccept scalar keyView failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer)
    (step setup checks wire route representation correct created credential selectedOwner selectedAccept scalar keyView failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer)
    (fun query => flatten_stable _ (native_stable setup checks wire route representation created credential selectedOwner scalar keyView failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query)) work before good
end Callbacks
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceProgram.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceProgram.program_source
