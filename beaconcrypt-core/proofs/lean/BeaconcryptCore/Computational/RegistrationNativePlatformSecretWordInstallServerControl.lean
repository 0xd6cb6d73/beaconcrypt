-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallServerBranch
import BeaconcryptCore.Computational.RegistrationNativeInstallBeaconComplete
/-! The actual corrected moved-token Server controller records the exact successful installation suffix from its consumed Ready, retaining repeated pin, occupancy, mutable reserve and every publication or writer failure. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallServerControl
open PqxdhRecordLiftInterface (EnvEffects Role)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativePlatformBoundCompiler (PublicState)
open RegistrationNativeSecretWordFrontendTrace (State handler)
open RegistrationNativeSecretWordInstallOrdinals (messages)
open RegistrationNativeSecretWordInstallInsert (success)
open RegistrationNativeInstallBeaconComplete (present)
open RegistrationNativePlatformPairedServerSafe (output after)
variable {n : Nat} {KemSK E Platform A : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
open RegistrationNativeSecretWordMessage (ServerReady ServerState Message)
open RegistrationNativePlatformSecretWordBuildControl
abbrev Base (n : Nat) (Platform : Type) := StateT (PublicState Platform) (OracleComp (RegistrationNativePlatformSecretWordBuild.Spec n))

omit primitive in
def compile (work : Base n Platform A) (before : PublicState Platform) (trace : State) :
    OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) ((A × PublicState Platform) × State) :=
  (simulateQ handler (simulateQ RegistrationNativePlatformSecretWordInstallServerBranch.embed (work.run before))).run trace

omit primitive in
private theorem compile_pure (value : A) (before : PublicState Platform) (trace : State) :
    compile (n := n) (KemSK := KemSK) (pure value) before trace = pure ((value, before), trace) := by
  simp only [compile, StateT.run_pure, simulateQ_pure]

omit primitive in
private theorem compile_bind {B : Type} (work : Base n Platform A) (next : A → Base n Platform B)
    (before : PublicState Platform) (trace : State) :
    compile (n := n) (KemSK := KemSK) (work >>= next) before trace = (do
      let result ← compile work before trace
      compile (next result.1.1) result.1.2 result.2) := by
  simp only [compile, StateT.run_bind, simulateQ_bind]

omit primitive in
private theorem effects_neutral (work : StateT (PublicState Platform) (OracleComp (RegistrationNativePlatformEffectCompiler.Spec n)) A)
    (quiet : RegistrationNativePlatformPairedPublicationFree.Quiet work) (before : PublicState Platform) (trace : State) :
    compile (n := n) (KemSK := KemSK) (RegistrationNativePlatformSecretWordBuild.liftEffects work) before trace =
      (fun result => (result, trace)) <$> simulateQ RegistrationNativePlatformSecretWordAtomEffects.effects (work.run before) := by
  simp only [compile, RegistrationNativePlatformSecretWordBuild.liftEffects, RegistrationNativePlatformInterpret.state,
    StateT.run, ← QueryImpl.simulateQ_compose, RegistrationNativePlatformSecretWordInstallServerBranch.embed]
  rw [RegistrationNativePlatformSecretWordAtomEffects.embedding]
  simpa only [QueryImpl.simulateQ_compose, StateT.run] using
    RegistrationNativePlatformSecretWordAtomEffects.state_neutral (KemSK := KemSK) work quiet before trace

omit primitive in
private theorem reserve_quiet (reserve : StateT Platform ProbComp Bool) :
    RegistrationNativePlatformPairedPublicationFree.Quiet
      (RegistrationNativePlatformBoundCompiler.liftPlatform (n := n) (RegistrationNativePlatformEffectCompiler.compile reserve)) := by
  intro before
  simp only [RegistrationNativePlatformBoundCompiler.liftPlatform, StateT.run, map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind
    (RegistrationNativePlatformPairedPublicationFree.platform_quiet reserve before.2) (fun _ => trivial)

variable (reserve : StateT Platform ProbComp Bool)
local notation "reserveSource" => RegistrationNativePlatformSecretWordBuild.liftEffects
  (RegistrationNativePlatformBoundCompiler.liftPlatform (n := n) (RegistrationNativePlatformEffectCompiler.compile reserve))
local notation "serviceSource" => RegistrationNativePlatformSecretWordBuild.service (n := n) source view failure allocation erased helper sign writer


omit primitive in
private theorem finish_present (published : RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8))) (before : ServerState) :
    present (finish published before).1 = success published := by
  cases published with
  | fail error | div => rfl
  | ok result => cases result <;> rfl

private theorem afterResult_messages (role : Role) (control : pqxdh.ServerState) (reference : Message)
    (action : RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState))
    (before : ServerState) (previous : PublicState Platform) (trace : State)
    (result : ((RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8) × ServerState) × PublicState Platform) × State)
    (supported : result ∈ support (compile (n := n) (KemSK := KemSK)
      ((afterResult reserveSource serviceSource control reference action).run before) previous trace)) :
    messages role result.2.events = messages role trace.events ++
      if role = .server ∧ present result.1.1.1 = true then [reference] else [] := by
  cases action with
  | fail error | div =>
    simp only [afterResult,StateT.run_pure,compile_pure,mem_support_pure_iff] at supported
    cases supported
    simp [present]
  | ok value => cases value with
    | Err previousControl =>
      simp only [afterResult,StateT.run_pure,compile_pure,mem_support_pure_iff] at supported
      cases supported
      simp [present]
    | Ok initial =>
      simp only [afterResult,StateT.run_bind,StateT.run_lift,bind_pure_comp,bind_map_left] at supported
      rw [compile_bind,mem_support_bind_iff] at supported
      obtain ⟨allowed,called,supported⟩ := supported
      rw [effects_neutral _ (reserve_quiet reserve) previous trace,support_map] at called
      obtain ⟨admission,_reserved,returned⟩ := called
      cases returned
      cases allowedEq : admission.1 with
      | false =>
        simp only [allowedEq,Bool.false_eq_true,ite_false,StateT.run_pure,compile_pure,mem_support_pure_iff] at supported
        cases supported
        simp [present]
      | true =>
        simp only [allowedEq,ite_true,StateT.run_bind,StateT.run_lift,bind_pure_comp,bind_map_left] at supported
        rw [compile_bind,mem_support_bind_iff] at supported
        obtain ⟨published,called,supported⟩ := supported
        have counted := RegistrationNativePlatformSecretWordInstallServerBranch.service_messages source view failure allocation erased helper sign writer
          role control initial reference admission.2 trace published called
        change result ∈ support (compile (pure (finish published.1.1 before)) published.1.2 published.2) at supported
        rw [compile_pure,mem_support_pure_iff] at supported
        cases supported
        rw [finish_present published.1.1 before]
        exact counted

omit primitive in
private theorem effect_quiet (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain)
    (allowed : ∀ role, ¬ RegistrationNativeSecretWordAtomInstallCaps.InstallEnv role query) :
    RegistrationNativePlatformPairedPublicationFree.Quiet
      (RegistrationNativePlatformEffectCompiler.effect (Platform := PublicState Platform) query) := by
  intro before
  change AllQueriesSatisfy (((RegistrationNativePlatformEffectCompiler.Spec n).query (.inl query) :
    OracleComp (RegistrationNativePlatformEffectCompiler.Spec n) _) >>= fun reply => pure (reply, before)) _
  exact ⟨allowed, fun _ => trivial⟩

omit primitive in
private theorem pin_quiet (current : session.ServerAuthenticationPin) :
    RegistrationNativePlatformPairedPublicationFree.Quiet
      (RegistrationNativePlatformServerRestrictedService.pin (n := n) (Platform := Platform) current) := by
  unfold RegistrationNativePlatformServerRestrictedService.pin
  exact RegistrationNativePlatformPairedPublicationFree.bind_quiet _ _
    (effect_quiet _ (by intro role; simp [RegistrationNativeSecretWordAtomInstallCaps.InstallEnv]))
    (fun _ => RegistrationNativePlatformPairedPublicationFree.pure_quiet _)

private theorem afterPin_messages (role : Role) (control : pqxdh.ServerState) (ready : ServerReady) (application : Slice U8)
    (current : RustM (core.option.Option session.ServerAuthenticationPin)) (before : ServerState)
    (previous : PublicState Platform) (trace : State)
    (result : ((RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8) × ServerState) × PublicState Platform) × State)
    (supported : result ∈ support (compile (n := n) (KemSK := KemSK)
      ((afterPin reserveSource
        (fun keyId => RegistrationNativePlatformSecretWordBuild.liftEffects (RegistrationNativePlatformEffectCompiler.effect (.inr (.peerPresent keyId))))
        serviceSource control ready application current).run before) previous trace)) :
    messages role result.2.events = messages role trace.events ++
      if role = .server ∧ present result.1.1.1 = true then [ready.reference] else [] := by
  cases current with
  | fail error | div =>
    simp only [afterPin, StateT.run] at supported
    rw [compile_pure,mem_support_pure_iff] at supported
    cases supported
    simp [present]
  | ok value => cases value with
    | none =>
      simp only [afterPin, StateT.run] at supported
      rw [compile_pure,mem_support_pure_iff] at supported
      cases supported
      simp [present]
    | some pin =>
      unfold afterPin at supported
      dsimp only [StateT.run] at supported
      cases beginning : peer.begin_completion_lookup control pin (RegistrationNativeSecretWordServerMaterial.token ready) application with
      | fail error | div =>
        simp only [beginning] at supported
        rw [compile_pure,mem_support_pure_iff] at supported
        cases supported
        simp [present]
      | ok answer =>
        simp only [beginning] at supported
        cases answer with
        | Err state =>
          rw [compile_pure,mem_support_pure_iff] at supported
          cases supported
          simp [present]
        | Ok lookup =>
          cases requested : lookup.request with
          | fail error | div =>
            simp only [requested] at supported
            rw [compile_pure,mem_support_pure_iff] at supported
            cases supported
            simp [present]
          | ok keyId =>
            simp only [requested] at supported
            split at supported
            · rw [compile_bind, mem_support_bind_iff] at supported
              obtain ⟨occupied, called, supported⟩ := supported
              rw [effects_neutral _ (effect_quiet (.inr (.peerPresent keyId))
                (by intro actual; simp [RegistrationNativeSecretWordAtomInstallCaps.InstallEnv])) previous trace,support_map] at called
              obtain ⟨reached,_called,equal⟩ := called
              cases equal
              exact afterResult_messages source view failure allocation erased helper sign writer reserve role control ready.reference
                _ before reached.2 trace result supported
            · rw [compile_pure,mem_support_pure_iff] at supported
              cases supported
              simp [present]



/-- The actual corrected moved-token body records its literal retained descriptor exactly when its own public build reply succeeds. -/
theorem body_live (role : Role) (handle : Nat) (application : Option (Slice U8)) (before : ServerState)
    (ready : ServerReady) (stored : before.sessions[handle]? = some (some ready))
    (previous : PublicState Platform) (trace : State)
    (result : ((RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8) × ServerState) × PublicState Platform) × State)
    (supported : result ∈ support (compile (n := n) (KemSK := KemSK)
      ((RegistrationNativePlatformSecretWordBuild.body source view failure allocation erased helper sign writer reserve handle application).run before)
        previous trace)) :
    messages role result.2.events = messages role trace.events ++
      if role = .server ∧ present result.1.1.1 = true then [ready.reference] else [] := by
  simp only [RegistrationNativePlatformSecretWordBuild.body,build,StateT.run,RegistrationNativeSecretWordServerMaterial.take,stored] at supported
  cases application with
  | none =>
    rw [compile_pure,mem_support_pure_iff] at supported
    cases supported
    simp [present]
  | some application =>
    simp only [complete,StateT.run] at supported
    rw [compile_bind,mem_support_bind_iff] at supported
    obtain ⟨pinned,called,supported⟩ := supported
    rw [effects_neutral _ (pin_quiet before.pin) previous trace,support_map] at called
    obtain ⟨reached,_pinned,equal⟩ := called
    cases equal
    exact afterPin_messages source view failure allocation erased helper sign writer reserve role before.control ready application
      reached.1 {before with sessions := before.sessions.set handle none} reached.2 trace result supported

/-- Failed or successful corrected source builds have precisely the same-result public reply's installation count, including missing and consumed handles. -/
theorem body_count (role : Role) (handle : Nat) (application : Option (Slice U8)) (before : ServerState)
    (previous : PublicState Platform) (trace : State)
    (result : ((RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8) × ServerState) × PublicState Platform) × State)
    (supported : result ∈ support (compile (n := n) (KemSK := KemSK)
      ((RegistrationNativePlatformSecretWordBuild.body source view failure allocation erased helper sign writer reserve handle application).run before)
        previous trace)) :
    ∃ added, messages role result.2.events = messages role trace.events ++ added ∧
      added.length = if role = .server ∧ present result.1.1.1 = true then 1 else 0 := by
  cases stored : before.sessions[handle]? with
  | none =>
    simp only [RegistrationNativePlatformSecretWordBuild.body,build,StateT.run,RegistrationNativeSecretWordServerMaterial.take,stored,
      compile_pure,mem_support_pure_iff] at supported
    cases supported
    exact ⟨[],by simp only [List.append_nil],by simp [present]⟩
  | some entry => cases entry with
    | none =>
      simp only [RegistrationNativePlatformSecretWordBuild.body,build,StateT.run,RegistrationNativeSecretWordServerMaterial.take,stored,
        compile_pure,mem_support_pure_iff] at supported
      cases supported
      exact ⟨[],by simp only [List.append_nil],by simp [present]⟩
    | some ready =>
      have counted := body_live source view failure allocation erased helper sign writer reserve role handle application before ready stored previous trace result supported
      refine ⟨if role = .server ∧ present result.1.1.1 = true then [ready.reference] else [],counted,?_⟩
      split <;> rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallServerControl

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallServerControl.body_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallServerControl.body_live

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallServerControl.body_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallServerControl.body_count
