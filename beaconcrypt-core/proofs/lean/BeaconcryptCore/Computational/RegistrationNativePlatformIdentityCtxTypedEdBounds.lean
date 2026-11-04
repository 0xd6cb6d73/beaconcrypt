-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEdCompilerBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleEdBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityQuiet
/-! Actual shared-CTX typed callbacks create at most one indexed Ed row in creation and attempt at most three Ed signatures in bundle. Counts cover all source outcomes, including rows born before a later owner failure and signatures before a failed writer. Ordinary/backend and ghost report operations cannot issue either indexed capability. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedEdBounds
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformIdentityCtxEdCompilerBounds (Kind Target Native Program)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

private theorem quiet_zero
    (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source A)
    (quiet : RegistrationNativePlatformIdentityQuiet.PlatformSafe work)
    (owners : RegistrationNativeIdentityFrontend.State source) (env : RegistrationServerReferenceCompiler.Environment) (previous : Platform) :
    (((work.run owners).run env).run previous).IsQueryBoundP (Program (KemSK := KemSK) .create) 0 := by
  classical
  have never : AllQueriesSatisfy (((work.run owners).run env).run previous)
      (fun query => ¬ Program (KemSK := KemSK) .create query) := by
    apply (quiet owners env previous).mono
    intro query allowed
    rcases query with coin | ambient | query
    · simp only [Program, not_false_eq_true]
    · simp only [Program, Native, not_false_eq_true]
    · cases query with
      | create | reveal handle => simp_all [RegistrationNativePlatformIdentityQuiet.PlatformAllowed, RegistrationNativePlatformIdentityQuiet.Allowed]
      | service handle request => cases request <;> simp_all [Program, Native, RegistrationNativePlatformIdentityQuiet.PlatformAllowed, RegistrationNativePlatformIdentityQuiet.Allowed]
  simpa only [not_not] using (isQueryBoundP_zero_iff _
    (fun query => ¬ Program (KemSK := KemSK) .create query)).mpr never

private theorem emit_zero (kind : Kind) (reports : List PqxdhJointPhase1Reports.CandidateReport) :
    (simulateQ RegistrationNativePlatformIdentityCtxCompiler.protocol (RegistrationNativeIdentityMain.emit reports)).IsQueryBoundP (Target kind) 0 := by
  induction reports with
  | nil => trivial
  | cons report rest ih =>
    simp only [RegistrationNativeIdentityMain.emit, simulateQ_bind, simulateQ_spec_query,
      RegistrationNativePlatformIdentityCtxCompiler.protocol]
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨by simp [Target], fun _ => ih⟩

private theorem report_run (packet : registration.InitPacket) (before : RegistrationNativeIdentityMain.State n KemSK source) :
    RegistrationNativeIdentityMain.report packet before =
      (fun reply => (reply, before)) <$> RegistrationNativeIdentityMain.emit (RegistrationNativeIdentityMain.reports packet before.beacons) := by
  change (RegistrationNativeIdentityMain.emit (RegistrationNativeIdentityMain.reports packet before.beacons) >>= fun reply => pure (reply, before)) = _
  exact bind_pure_comp _ _

private theorem report_zero (kind : Kind) (packet : registration.InitPacket)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxOrdinary.report packet).run before).IsQueryBoundP (Target kind) 0 := by
  simp only [RegistrationNativePlatformIdentityCtxOrdinary.report, StateT.run, report_run,
    simulateQ_map, isQueryBoundP_map_iff]
  exact emit_zero kind _

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {E : Type}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "callback" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

omit primitive in
theorem create_bound (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxLifecycle.create setup edPin mlPin keyId checks representation created).run before).IsQueryBoundP (Target .create) 1 := by
  apply RegistrationNativePlatformIdentityCtxEdCompilerBounds.beacon_bound
  apply RegistrationNativePlatformIdentityCtxEdCompilerBounds.native_bound
  intro owners env
  apply OracleComp.IsQueryBoundP.of_imp _ (RegistrationNativeIdentityCreateCaps.create_one setup edPin mlPin keyId owners env)
  intro query counted
  rcases query with ambient | query
  · exact counted.elim
  · cases query with
    | create | reveal handle => simp_all [Native, RegistrationNativeIdentityBirthCaps.Creates, RegistrationNativeIdentityNoCreate.Allowed]
    | service handle request => cases request <;> simp_all [Native]

omit primitive in
theorem bundle_create_zero (index : Nat) (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index).run before).IsQueryBoundP (Target .create) 0 := by
  simp only [RegistrationNativePlatformIdentityCtxLifecycle.bundle, StateT.run_map, isQueryBoundP_map_iff]
  exact RegistrationNativePlatformIdentityCtxEdCompilerBounds.beacon_bound setup checks representation created .create _ 0
    (quiet_zero _ (RegistrationNativePlatformIdentityQuiet.bundle_quiet setup index writer)) before

omit primitive in
theorem finish_create_zero (index : Nat) (packet : Option registration.ResponsePacket)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxLifecycle.finish setup checks representation created wire index packet).run before).IsQueryBoundP (Target .create) 0 :=
  RegistrationNativePlatformIdentityCtxEdCompilerBounds.beacon_bound setup checks representation created .create _ 0
    (quiet_zero _ (RegistrationNativePlatformIdentityQuiet.native_quiet _
      (RegistrationNativePlatformIdentityQuiet.finish_quiet setup wire index packet))) before

omit primitive in
theorem bundle_sign_bound (index : Nat) (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index).run before).IsQueryBoundP (Target .sign) 3 := by
  simp only [RegistrationNativePlatformIdentityCtxLifecycle.bundle, StateT.run_map, isQueryBoundP_map_iff]
  apply RegistrationNativePlatformIdentityCtxEdCompilerBounds.beacon_bound setup checks representation created .sign _ 3
  intro owners env previous
  have bounded := RegistrationNativePlatformIdentityBundleEdBounds.bundle_bound (n := n)
    (Auxiliary := RegistrationServerRoleBackend.State) setup index writer owners env previous
  apply OracleComp.IsQueryBoundP.of_imp _ bounded
  intro query counted
  rcases query with coin | query
  · exact counted.elim
  · cases query with
    | inl ambient => exact counted.elim
    | inr query => cases query with
      | create | reveal handle => simp_all [Program, Native]
      | service handle request => cases request <;> simp_all [Program, Native, RegistrationNativePlatformIdentitySourceEdBounds.IsSign, RegistrationNativePlatformIdentityFrontendEdBounds.IsSign]

private theorem dispatch_zero (kind : Kind) (query : TypedSpec.Domain)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxDispatch.step (n := n) setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query).run before).IsQueryBoundP (Target kind) 0 := by
  simp only [RegistrationNativePlatformIdentityCtxDispatch.step, StateT.run]
  exact RegistrationNativePlatformIdentityCtxEdCompilerBounds.ordinary_zero kind _ before

attribute [local irreducible] RegistrationNativePlatformIdentityCtxDispatch.step

theorem handler_create_bound (query : TypedSpec.Domain)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((callback query).run before).IsQueryBoundP (Target .create)
      (if RegistrationNativeRawAdapter.kind query = 1 then 1 else 0) := by
  cases query with
  | inl coin => exact dispatch_zero setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer .create (.inl coin) before
  | inr query => cases query with
    | create edPin mlPin keyId => exact create_bound setup checks representation created edPin mlPin keyId before
    | bundle index => exact bundle_create_zero setup checks representation created writer index before
    | finish index packet => exact finish_create_zero setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) representation created index packet before
    | accept packet =>
      simp only [RegistrationNativePlatformIdentityCtxTyped.handler, StateT.run_bind]
      exact isQueryBoundP_bind (n := 0) (m := 0) (report_zero .create packet before)
        (fun result _ => dispatch_zero setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer .create (.inr (.accept packet)) result.2)
    | build handle application => exact dispatch_zero setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer .create (.inr (.build handle application)) before
    | hmac key bytes => exact dispatch_zero setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer .create (.inr (.hmac key bytes)) before
    | hash bytes => exact dispatch_zero setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer .create (.inr (.hash bytes)) before
    | serverSend keyId bytes => exact dispatch_zero setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer .create (.inr (.serverSend keyId bytes)) before
    | serverRaw bytes => exact dispatch_zero setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer .create (.inr (.serverRaw bytes)) before
    | beaconSend index bytes => exact dispatch_zero setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer .create (.inr (.beaconSend index bytes)) before
    | beaconRaw index bytes => exact dispatch_zero setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer .create (.inr (.beaconRaw index bytes)) before

theorem handler_sign_bound (query : TypedSpec.Domain)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((callback query).run before).IsQueryBoundP (Target .sign)
      (if RegistrationNativeRawAdapter.kind query = 2 then 3 else 0) := by
  by_cases selected : ∃ index, query = .inr (.bundle index)
  · obtain ⟨index, rfl⟩ := selected
    exact bundle_sign_bound setup checks representation created writer index before
  · have free := RegistrationNativePlatformIdentityCtxSignScope.handler_sign_bound setup checks wire route representation created credential
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query
      (fun index same => selected ⟨index, same⟩) before
    have notBundle : RegistrationNativeRawAdapter.kind query ≠ 2 := by
      cases query with
      | inl coin => simp [RegistrationNativeRawAdapter.kind]
      | inr query => cases query <;> simp_all [RegistrationNativeRawAdapter.kind]
    simp only [notBundle, ite_false]
    apply OracleComp.IsQueryBoundP.of_imp _ free
    intro query counted
    rcases query with (query | report) | bytes
    · rcases query with coin | query
      · exact counted.elim
      · cases query with
        | create | reveal handle => simp_all [Target]
        | service handle request => cases request <;> simp_all [Target, RegistrationNativePlatformIdentityCtxSignScope.IsSign]
    · exact counted.elim
    · exact counted.elim
omit primitive in
private theorem triple_run {I J S V : Type} {input : OracleSpec I} {output : OracleSpec J}
    (selected : I → Prop) [DecidablePred selected] (counted : J → Prop) [DecidablePred counted]
    (implementation : QueryImpl input (StateT S (OracleComp output)))
    (step : ∀ query before, ((implementation query).run before).IsQueryBoundP counted (if selected query then 3 else 0))
    (work : OracleComp input V) (cap : Nat) (bounded : work.IsQueryBoundP selected cap) (before : S) :
    ((simulateQ implementation work).run before).IsQueryBoundP counted (3 * cap) := by
  induction work using OracleComp.inductionOn generalizing cap before with
  | pure value => trivial
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    apply (isQueryBoundP_bind (step query before) (fun result _ => ih result.1 _ (bounded.2 result.1) result.2)).mono
    by_cases hit : selected query
    · have positive := bounded.1
      simp only [hit, not_true_eq_false, false_or] at positive
      simp only [hit, ite_true]
      omega
    · simp [hit]

/-- Adaptive complete typed programs create no more indexed rows than their original create-command allowance. -/
theorem program_create_bound (work : OracleComp TypedSpec A) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = 1) cap)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((simulateQ callback work).run before).IsQueryBoundP (Target .create) cap :=
  OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step bounded
    (fun query current => handler_create_bound setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query current) before

/-- Every adaptive source prefix has at most three indexed signing attempts per original bundle-command allowance. -/
theorem program_sign_bound (work : OracleComp TypedSpec A) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = 2) cap)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((simulateQ callback work).run before).IsQueryBoundP (Target .sign) (3 * cap) :=
  triple_run (fun query => RegistrationNativeRawAdapter.kind query = 2) (Target .sign) callback
    (fun query current => handler_sign_bound setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query current) work cap bounded before

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedEdBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedEdBounds.create_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedEdBounds.create_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedEdBounds.bundle_create_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedEdBounds.bundle_create_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedEdBounds.finish_create_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedEdBounds.finish_create_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedEdBounds.bundle_sign_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedEdBounds.bundle_sign_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedEdBounds.handler_create_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedEdBounds.handler_create_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedEdBounds.handler_sign_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedEdBounds.handler_sign_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedEdBounds.program_create_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedEdBounds.program_create_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedEdBounds.program_sign_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedEdBounds.program_sign_bound
