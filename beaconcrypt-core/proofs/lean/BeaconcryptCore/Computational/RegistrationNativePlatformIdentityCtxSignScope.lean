-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTyped
import BeaconcryptCore.Computational.RegistrationNativeIdentitySignScope
/-! Indexed Ed signing can occur only inside actual public bundle callbacks. This structural scope follows the literal CTX compiler and corrected constructor/assigned-ID finish controllers; arbitrary common backend work, stateful platform failures and pre-accept ghost reports cannot issue that indexed signing capability. No ownership, success or complete callback/source law is a premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSignScope
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
variable {n : Nat} {I KemSK Platform A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def IsSign : Spec.Domain → Prop
  | .inl (.inl (.inr (.service _ (.sign _)))) => True
  | _ => False
instance : DecidablePred IsSign := fun query => by
  unfold IsSign
  split <;> infer_instance
abbrev Allowed (query : Spec.Domain) : Prop := ¬ IsSign query

def ProgramAllowed : (RegistrationNativePlatformIdentityProgram.Spec n KemSK).Domain → Prop
  | .inl _ => True
  | .inr query => RegistrationNativeIdentitySignScope.Allowed n KemSK query

private theorem mapped {I A B : Type} {queries : OracleSpec I} (work : OracleComp queries A)
    (change : A → B) (predicate : I → Prop) (allowed : work.AllQueriesSatisfy predicate) :
    (change <$> work).AllQueriesSatisfy predicate := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind allowed (fun _ => allQueriesSatisfy_pure _ _)

private theorem lower_safe {I J State A : Type} {queries : OracleSpec I} {target : OracleSpec J}
    (input : I → Prop) (output : J → Prop) (implementation : QueryImpl queries (StateT State (OracleComp target)))
    (leaf : ∀ query, input query → ∀ before, ((implementation query).run before).AllQueriesSatisfy output)
    (work : OracleComp queries A) (allowed : work.AllQueriesSatisfy input) (before : State) :
    ((simulateQ implementation work).run before).AllQueriesSatisfy output := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact allQueriesSatisfy_bind (leaf query allowed.1 before) (fun result => ih result.1 (allowed.2 result.1) result.2)

/-- The literal ambient hash/uniform backend cannot issue an indexed Ed signing request. -/
theorem backend_safe (work : OracleComp RegistrationNativePlatformCtxBackend.Spec A) :
    (simulateQ RegistrationNativePlatformIdentityCtxCompiler.backend work).AllQueriesSatisfy Allowed := by
  induction work using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    cases query with
    | inl bytes =>
      rw [RegistrationNativePlatformIdentityCtxCompiler.backend, allQueriesSatisfy_query_bind_iff]
      exact ⟨by simp only [Allowed, IsSign, not_false_eq_true], ih⟩
    | inr coin =>
      rw [RegistrationNativePlatformIdentityCtxCompiler.backend, allQueriesSatisfy_query_bind_iff]
      exact ⟨by simp only [Allowed, IsSign, not_false_eq_true], ih⟩

private theorem native_lift_safe
    (work : OracleComp (RegistrationNativeIdentityFrontend.Trusted n KemSK) A)
    (allowed : work.AllQueriesSatisfy (RegistrationNativeIdentitySignScope.Allowed n KemSK)) :
    (simulateQ (RegistrationNativePlatformIdentityProgram.nativeLift (n := n) (KemSK := KemSK)) work).AllQueriesSatisfy
      (ProgramAllowed (n := n) (KemSK := KemSK)) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformIdentityProgram.nativeLift]
    rw [allQueriesSatisfy_query_bind_iff]
    exact ⟨allowed.1, fun reply => ih reply (allowed.2 reply)⟩

private theorem native_safe (work : RegistrationNativeIdentityFrontend.M n KemSK RegistrationServerRoleBackend.State source A)
    (allowed : RegistrationNativeIdentitySignScope.Safe work)
    (owners : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (previous : Platform) :
    ((((RegistrationNativePlatformIdentityProgram.native work).run owners).run env).run previous).AllQueriesSatisfy
      (ProgramAllowed (n := n) (KemSK := KemSK)) := by
  apply mapped
  exact native_lift_safe _ (allowed owners env)

private theorem free_query_safe (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativePlatformIdentityProgram.Spec n KemSK).Domain)
    (allowed : ProgramAllowed (KemSK := KemSK) query) (before : RegistrationNativeIdentityWorld.Context n KemSK) :
    ((RegistrationNativePlatformIdentityCtxCompiler.free
      (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created) query).run before).AllQueriesSatisfy Allowed := by
  rcases query with coin | ambient | query
  · simp only [RegistrationNativePlatformIdentityCtxCompiler.free, RegistrationNativePlatformIdentityCtxCompiler.implementation,
      StateT.run, RegistrationNativePlatformIdentityCtxCompiler.coins]
    apply mapped
    rw [allQueriesSatisfy_query_iff]
    simp only [Allowed, IsSign, not_false_eq_true]
  · exact backend_safe _
  · cases query with
    | create =>
      simp only [RegistrationNativePlatformIdentityCtxCompiler.free, RegistrationNativePlatformIdentityCtxCompiler.implementation,
        StateT.run, RegistrationNativePlatformIdentityCtxCompiler.joint]
      apply mapped
      rw [allQueriesSatisfy_query_iff]
      simp only [Allowed, IsSign, not_false_eq_true]
    | reveal handle =>
      simp only [RegistrationNativePlatformIdentityCtxCompiler.free, RegistrationNativePlatformIdentityCtxCompiler.implementation,
        StateT.run, RegistrationNativePlatformIdentityCtxCompiler.joint]
      apply mapped
      rw [allQueriesSatisfy_query_iff]
      simp only [Allowed, IsSign, not_false_eq_true]
    | service handle request =>
      cases request with
      | sign message => exact False.elim allowed
      | staticDh point =>
        simp only [RegistrationNativePlatformIdentityCtxCompiler.free, RegistrationNativePlatformIdentityCtxCompiler.implementation,
          StateT.run, RegistrationNativePlatformIdentityCtxCompiler.joint]
        apply mapped
        rw [allQueriesSatisfy_query_iff]
        simp only [Allowed, IsSign, not_false_eq_true]

private theorem native_beacon_safe (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeIdentityFrontend.M n KemSK RegistrationServerRoleBackend.State source A)
    (allowed : RegistrationNativeIdentitySignScope.Safe work)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (RegistrationNativePlatformIdentityProgram.native work)).run before).AllQueriesSatisfy Allowed := by
  unfold RegistrationNativePlatformIdentityCtxMain.beacon RegistrationNativePlatformIdentityCtxCompiler.beacon
  apply mapped
  exact lower_safe (ProgramAllowed (n := n) (KemSK := KemSK)) Allowed _
    (free_query_safe setup checks representation created) _
    (native_safe work allowed before.1.beacons (RegistrationWorldAgreementCompiler.erase before.1.context.server.world) before.2) before.1.context

/-- Every actual CTX constructor branch remains free of indexed Ed signing, with its complete counters and current state retained. -/
theorem create_safe (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxLifecycle.create setup edPin mlPin keyId checks representation created).run before).AllQueriesSatisfy Allowed :=
  native_beacon_safe setup checks representation created _
    (RegistrationNativeIdentitySignScope.create_safe setup edPin mlPin keyId) before

/-- Corrected assigned-ID finish and its actual opening/copy/abort branches cannot issue indexed Ed signing. -/
theorem finish_safe (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxLifecycle.finish setup checks representation created wire index packet).run before).AllQueriesSatisfy Allowed :=
  native_beacon_safe setup checks representation created _
    (RegistrationNativeIdentitySignScope.finish_safe setup wire index packet) before

/-- Every arbitrary actual ordinary CTX branch, including source writers and shared platform failures, is confined to the non-signing backend language. -/
theorem ordinary_safe (work : RegistrationNativePlatformCtxContext.M n KemSK Platform A)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxOrdinary.ordinary (source := source) work).run before).AllQueriesSatisfy Allowed := by
  unfold RegistrationNativePlatformIdentityCtxOrdinary.ordinary RegistrationNativePlatformIdentityCtxCompiler.ordinary
  apply mapped
  exact backend_safe _

private theorem emit_safe (reports : List PqxdhJointPhase1Reports.CandidateReport) :
    (simulateQ RegistrationNativePlatformIdentityCtxCompiler.protocol (RegistrationNativeIdentityMain.emit reports)).AllQueriesSatisfy Allowed := by
  induction reports with
  | nil => exact allQueriesSatisfy_pure _ _
  | cons report rest ih =>
    simp only [RegistrationNativeIdentityMain.emit, simulateQ_bind, simulateQ_spec_query,
      RegistrationNativePlatformIdentityCtxCompiler.protocol]
    rw [allQueriesSatisfy_query_bind_iff]
    exact ⟨by simp only [Allowed, IsSign, not_false_eq_true], fun _ => ih⟩

private theorem report_run (packet : registration.InitPacket) (before : RegistrationNativeIdentityMain.State n KemSK source) :
    (RegistrationNativeIdentityMain.report packet).run before =
      (fun reply => (reply, before)) <$> RegistrationNativeIdentityMain.emit (RegistrationNativeIdentityMain.reports packet before.beacons) := by
  change (RegistrationNativeIdentityMain.emit (RegistrationNativeIdentityMain.reports packet before.beacons) >>= fun reply => pure (reply, before)) = _
  exact bind_pure_comp _ _

/-- All actual pre-accept candidate reports are ghost-only requests and cannot issue indexed Ed signing. -/
theorem report_safe (packet : registration.InitPacket) (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxOrdinary.report packet).run before).AllQueriesSatisfy Allowed := by
  unfold RegistrationNativePlatformIdentityCtxOrdinary.report
  apply mapped
  rw [report_run, simulateQ_map]
  exact mapped _ _ Allowed (emit_safe _)
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {E : Type}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "callback" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "dispatch" => RegistrationNativePlatformIdentityCtxDispatch.step (n := n) setup checks wire route representation created credential
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

private theorem dispatch_safe (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((dispatch query).run before).AllQueriesSatisfy Allowed :=
  ordinary_safe (RegistrationNativePlatformIdentityCtxDispatch.context setup checks wire route representation created credential
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before.1.beacons) before

attribute [local irreducible] RegistrationNativePlatformIdentityCtxDispatch.step
  RegistrationNativePlatformIdentityMainAmbient.command

/-- Every literal typed callback except a public bundle attempt has zero indexed Ed signing queries, on every source branch and from arbitrary full current state. -/
theorem handler_safe (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (notBundle : ∀ index, query ≠ .inr (.bundle index))
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((callback query).run before).AllQueriesSatisfy Allowed := by
  cases query with
  | inl coin =>
    exact dispatch_safe setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (.inl coin) before
  | inr command =>
    cases command with
    | create edPin mlPin keyId =>
      exact create_safe setup checks representation created edPin mlPin keyId before
    | bundle index => exact False.elim (notBundle index rfl)
    | finish index packet =>
      exact finish_safe setup checks representation created
        (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) index packet before
    | accept packet =>
      change (((RegistrationNativePlatformIdentityCtxOrdinary.report packet >>= fun _ => dispatch (.inr (.accept packet))).run before)).AllQueriesSatisfy Allowed
      rw [StateT.run_bind]
      exact allQueriesSatisfy_bind (report_safe packet before) (fun result =>
        dispatch_safe setup checks wire route representation created credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.accept packet)) result.2)
    | build handle application =>
      exact dispatch_safe setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.build handle application)) before
    | hmac key message =>
      exact dispatch_safe setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.hmac key message)) before
    | hash bytes =>
      exact dispatch_safe setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.hash bytes)) before
    | serverSend keyId plaintext =>
      exact dispatch_safe setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.serverSend keyId plaintext)) before
    | serverRaw raw =>
      exact dispatch_safe setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.serverRaw raw)) before
    | beaconSend index plaintext =>
      exact dispatch_safe setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.beaconSend index plaintext)) before
    | beaconRaw index raw =>
      exact dispatch_safe setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.beaconRaw index raw)) before

/-- The exact free client therefore has a literal zero signing-query bill outside bundle callbacks; this is before any source or proxy interpretation. -/
theorem handler_sign_bound (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (notBundle : ∀ index, query ≠ .inr (.bundle index))
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((callback query).run before).IsQueryBoundP IsSign 0 := by
  classical
  have safe := handler_safe setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer query notBundle before
  have zero := (isQueryBoundP_zero_iff _ Allowed).mpr safe
  simpa only [Allowed, not_not] using zero
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSignScope

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSignScope.backend_safe' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSignScope.backend_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSignScope.create_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSignScope.create_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSignScope.finish_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSignScope.finish_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSignScope.ordinary_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSignScope.ordinary_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSignScope.report_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSignScope.report_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSignScope.handler_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSignScope.handler_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSignScope.handler_sign_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSignScope.handler_sign_bound
