-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerBranch
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallServerControl
/-! Exact successful Server response identifiers survive the complete actual moved-token build and its four source effect leaves. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerControl
open PqxdhRecordLiftInterface (EnvEffects Role)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativePlatformBoundCompiler (PublicState)
open RegistrationNativePlatformRecordPartnerSnapshotHandles (handler)
open RegistrationNativePlatformRecordPartnerServerAfter (outputHandles)


open RegistrationNativePlatformPublicSlotServerSafe (output after)
variable {n : Nat} {KemSK E Platform A : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
open RegistrationNativeRelatedFamily (Message)
abbrev ServerReady := RegistrationServerReferenceRoot.Ready
abbrev ServerState := RegistrationServerMaterialFrontend.State
open RegistrationNativePlatformServerMaterialFrontend
abbrev Base (n : Nat) (Platform : Type) := StateT (PublicState Platform) (OracleComp (RegistrationNativePlatformServerFrontendCompiler.Spec n))

omit primitive in
def compile (work : Base n Platform A) (before : PublicState Platform) (trace : List PqxdhDeploymentInterface.Handle) :
    OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) ((A × PublicState Platform) × List PqxdhDeploymentInterface.Handle) :=
  (simulateQ (handler PqxdhRecordLiftInterface.Role.server) (simulateQ RegistrationNativePlatformRecordPartnerServerBranch.embed (work.run before))).run trace

omit primitive in
private theorem compile_pure (value : A) (before : PublicState Platform) (trace : List PqxdhDeploymentInterface.Handle) :
    compile (n := n) (KemSK := KemSK) (pure value) before trace = pure ((value, before), trace) := by
  simp only [compile, StateT.run_pure, simulateQ_pure]

omit primitive in
private theorem compile_bind {B : Type} (work : Base n Platform A) (next : A → Base n Platform B)
    (before : PublicState Platform) (trace : List PqxdhDeploymentInterface.Handle) :
    compile (n := n) (KemSK := KemSK) (work >>= next) before trace = (do
      let result ← compile work before trace
      compile (next result.1.1) result.1.2 result.2) := by
  simp only [compile, StateT.run_bind, simulateQ_bind]

omit primitive in
private theorem effects_neutral (work : StateT (PublicState Platform) (OracleComp (RegistrationNativePlatformEffectCompiler.Spec n)) A)
    (quiet : RegistrationNativePlatformPairedPublicationFree.Quiet work) (before : PublicState Platform) (trace : List PqxdhDeploymentInterface.Handle) :
    compile (n := n) (KemSK := KemSK) (RegistrationNativePlatformServerFrontendCompiler.liftEffects work) before trace =
      (fun result => (result, trace)) <$> simulateQ RegistrationNativePlatformPublicSlotEffects.effects (work.run before) := by
  have embedding : RegistrationNativePlatformRecordPartnerServerBranch.embed ∘ₛ
      RegistrationNativePlatformServerFrontendCompiler.embed (n := n) =
      RegistrationNativePlatformPublicSlotEffects.effects (n := n) (KemSK := KemSK) := by
    funext query
    cases query <;> rfl
  simp only [compile,RegistrationNativePlatformServerFrontendCompiler.liftEffects,StateT.run,
    ←QueryImpl.simulateQ_compose]
  rw [embedding,QueryImpl.simulateQ_compose]
  exact RegistrationNativePlatformRecordPartnerServerEffects.state_neutral (KemSK := KemSK) work quiet before trace

omit primitive in
private theorem reserve_quiet (reserve : StateT Platform ProbComp Bool) :
    RegistrationNativePlatformPairedPublicationFree.Quiet
      (RegistrationNativePlatformBoundCompiler.liftPlatform (n := n) (RegistrationNativePlatformEffectCompiler.compile reserve)) := by
  intro before
  simp only [RegistrationNativePlatformBoundCompiler.liftPlatform, StateT.run, map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind
    (RegistrationNativePlatformPairedPublicationFree.platform_quiet reserve before.2) (fun _ => trivial)

variable (reserve : StateT Platform ProbComp Bool)
local notation "reserveSource" => RegistrationNativePlatformServerFrontendCompiler.liftEffects
  (RegistrationNativePlatformBoundCompiler.liftPlatform (n := n) (RegistrationNativePlatformEffectCompiler.compile reserve))
local notation "adHashSource" => (fun pending => RegistrationNativePlatformServerFrontendCompiler.liftEffects
  (RegistrationNativePlatformServerRestrictedService.adHash (n := n) (Platform := Platform) pending))
local notation "serviceSource" => RegistrationNativePlatformServerFrontendCompiler.service (n := n) source view failure allocation erased helper sign writer


noncomputable def body (handle : Nat) (application : Option (Slice U8)) :
    StateT ServerState (Base n Platform) (RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8)) :=
  RegistrationNativePlatformServerMaterialFrontend.build
    (fun pending => RegistrationNativePlatformServerFrontendCompiler.liftEffects (RegistrationNativePlatformServerRestrictedService.adHash pending))
    (fun current => RegistrationNativePlatformServerFrontendCompiler.liftEffects (RegistrationNativePlatformServerRestrictedService.pin current))
    reserveSource
    (fun keyId => RegistrationNativePlatformServerFrontendCompiler.liftEffects (RegistrationNativePlatformEffectCompiler.effect (.inr (.peerPresent keyId))))
    serviceSource handle application


/-- The controller is the literal interpretation of the actual source four-leaf build program. -/
theorem program_source (handle : Nat) (application : Option (Slice U8)) (before : ServerState) :
    simulateQ (RegistrationNativePlatformServerFrontendCompiler.target (n := n) source view failure allocation erased helper sign writer reserve)
      ((RegistrationNativePlatformServerFrontendProgram.program handle application).run before) =
      ((body source view failure allocation erased helper sign writer reserve handle application).run before) := by
  rw [RegistrationNativePlatformServerFrontendProgram.interpret]
  rfl


omit primitive in
def resultHandles {Encoded : Type} : RustM (Option (Std.U64 × Encoded)) → List PqxdhDeploymentInterface.Handle
  | .ok (some response)=>[.peer response.1]
  | _=>[]
omit primitive in
private theorem finish_handles (published : RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8))) (before : ServerState) :
    resultHandles (finish published before).1=outputHandles published := by
  cases published with
  | fail error | div=>rfl
  | ok result=>cases result <;> rfl

private theorem afterResult_handles (control : pqxdh.ServerState) (reference : Message)
    (action : RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState))
    (before : ServerState) (previous : PublicState Platform) (trace : List PqxdhDeploymentInterface.Handle)
    (result : ((RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8) × ServerState) × PublicState Platform) × List PqxdhDeploymentInterface.Handle)
    (supported : result ∈ support (compile (n := n) (KemSK := KemSK)
      ((afterResult reserveSource serviceSource control reference action).run before) previous trace)) :
    result.2=trace++resultHandles result.1.1.1 := by
  cases action with
  | fail error | div =>
    simp only [afterResult,StateT.run_pure,compile_pure,mem_support_pure_iff] at supported
    cases supported
    simp [resultHandles]
  | ok value => cases value with
    | Err previousControl =>
      simp only [afterResult,StateT.run_pure,compile_pure,mem_support_pure_iff] at supported
      cases supported
      simp [resultHandles]
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
        simp [resultHandles]
      | true =>
        simp only [allowedEq,ite_true,StateT.run_bind,StateT.run_lift,bind_pure_comp,bind_map_left] at supported
        rw [compile_bind,mem_support_bind_iff] at supported
        obtain ⟨published,called,supported⟩ := supported
        have counted := RegistrationNativePlatformRecordPartnerServerBranch.service source view failure allocation erased helper sign writer
          control initial reference admission.2 trace published called
        change result ∈ support (compile (pure (finish published.1.1 before)) published.1.2 published.2) at supported
        rw [compile_pure,mem_support_pure_iff] at supported
        cases supported
        rw [finish_handles published.1.1 before]
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
  exact RegistrationNativePlatformPairedPublicationFree.pure_quiet _

omit primitive in
private theorem adHash_quiet (pending : registration.ServerAdHash) :
    RegistrationNativePlatformPairedPublicationFree.Quiet
      (RegistrationNativePlatformServerRestrictedService.adHash (n := n) (Platform := Platform) pending) := by
  unfold RegistrationNativePlatformServerRestrictedService.adHash RegistrationServerAdHash.runWith
  cases pending.request with
  | fail error | div => exact RegistrationNativePlatformPairedPublicationFree.pure_quiet _
  | ok request =>
    simp only [bind_assoc,pure_bind]
    exact RegistrationNativePlatformPairedPublicationFree.bind_quiet _ _
      (effect_quiet _ (by intro role; simp [RegistrationNativeSecretWordAtomInstallCaps.InstallEnv]))
      (fun _ => RegistrationNativePlatformPairedPublicationFree.pure_quiet _)

private theorem afterOccupancy_handles (control : pqxdh.ServerState) (lookup : peer.CompletionLookup)
    (reference : Message) (occupied : Bool) (before : ServerState) (previous : PublicState Platform)
    (trace : List PqxdhDeploymentInterface.Handle)
    (result : ((RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8) × ServerState) × PublicState Platform) × List PqxdhDeploymentInterface.Handle)
    (supported : result ∈ support (compile (n := n) (KemSK := KemSK)
      ((afterOccupancy adHashSource reserveSource serviceSource control lookup reference occupied).run before) previous trace)) :
    result.2=trace++resultHandles result.1.1.1 := by
  cases selected : lookup.resume occupied with
  | fail error | div =>
    simp only [afterOccupancy,selected,StateT.run_pure,compile_pure,mem_support_pure_iff] at supported
    cases supported
    simp [resultHandles]
  | ok answer => cases answer with
    | Err previousControl =>
      simp only [afterOccupancy,selected,StateT.run_pure,compile_pure,mem_support_pure_iff] at supported
      cases supported
      simp [resultHandles]
    | Ok pending =>
      simp only [afterOccupancy,selected,StateT.run_bind,StateT.run_lift,bind_pure_comp,bind_map_left] at supported
      rw [compile_bind,mem_support_bind_iff] at supported
      obtain ⟨hashed,called,supported⟩ := supported
      rw [effects_neutral _ (adHash_quiet pending) previous trace,support_map] at called
      obtain ⟨reached,_hashed,returned⟩ := called
      cases returned
      exact afterResult_handles source view failure allocation erased helper sign writer reserve control reference
        _ before reached.2 trace result supported


private theorem afterPin_handles (control : pqxdh.ServerState) (ready : ServerReady) (application : Slice U8)
    (current : RustM (core.option.Option session.ServerAuthenticationPin)) (before : ServerState)
    (previous : PublicState Platform) (trace : List PqxdhDeploymentInterface.Handle)
    (result : ((RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8) × ServerState) × PublicState Platform) × List PqxdhDeploymentInterface.Handle)
    (supported : result ∈ support (compile (n := n) (KemSK := KemSK)
      ((afterPin adHashSource reserveSource
        (fun keyId => RegistrationNativePlatformServerFrontendCompiler.liftEffects (RegistrationNativePlatformEffectCompiler.effect (.inr (.peerPresent keyId))))
        serviceSource control ready application current).run before) previous trace)) :
    result.2=trace++resultHandles result.1.1.1 := by
  cases current with
  | fail error | div =>
    simp only [afterPin, StateT.run] at supported
    rw [compile_pure,mem_support_pure_iff] at supported
    cases supported
    simp [resultHandles]
  | ok value => cases value with
    | none =>
      simp only [afterPin, StateT.run] at supported
      rw [compile_pure,mem_support_pure_iff] at supported
      cases supported
      simp [resultHandles]
    | some pin =>
      unfold afterPin at supported
      dsimp only [StateT.run] at supported
      cases beginning : peer.begin_completion_lookup control pin (RegistrationServerMaterialFrontend.token ready) application with
      | fail error | div =>
        simp only [beginning] at supported
        rw [compile_pure,mem_support_pure_iff] at supported
        cases supported
        simp [resultHandles]
      | ok answer =>
        simp only [beginning] at supported
        cases answer with
        | Err state =>
          rw [compile_pure,mem_support_pure_iff] at supported
          cases supported
          simp [resultHandles]
        | Ok lookup =>
          cases requested : lookup.request with
          | fail error | div =>
            simp only [requested] at supported
            rw [compile_pure,mem_support_pure_iff] at supported
            cases supported
            simp [resultHandles]
          | ok keyId =>
            simp only [requested] at supported
            split at supported
            · rw [compile_bind, mem_support_bind_iff] at supported
              obtain ⟨occupied, called, supported⟩ := supported
              rw [effects_neutral _ (effect_quiet (.inr (.peerPresent keyId))
                (by intro actual; simp [RegistrationNativeSecretWordAtomInstallCaps.InstallEnv])) previous trace,support_map] at called
              obtain ⟨reached,_called,equal⟩ := called
              cases equal
              exact afterOccupancy_handles source view failure allocation erased helper sign writer reserve control lookup ready.reference reached.1
                before reached.2 trace result supported
            · rw [compile_pure,mem_support_pure_iff] at supported
              cases supported
              simp [resultHandles]



/-- The actual corrected moved-token body records its literal retained descriptor exactly when its own public build reply succeeds. -/
theorem body_live_handles (handle : Nat) (application : Option (Slice U8)) (before : ServerState)
    (ready : ServerReady) (stored : before.sessions[handle]? = some (some ready))
    (previous : PublicState Platform) (trace : List PqxdhDeploymentInterface.Handle)
    (result : ((RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8) × ServerState) × PublicState Platform) × List PqxdhDeploymentInterface.Handle)
    (supported : result ∈ support (compile (n := n) (KemSK := KemSK)
      ((body source view failure allocation erased helper sign writer reserve handle application).run before)
        previous trace)) :
    result.2=trace++resultHandles result.1.1.1 := by
  simp only [body,build,StateT.run,RegistrationServerMaterialFrontend.take,stored] at supported
  cases application with
  | none =>
    rw [compile_pure,mem_support_pure_iff] at supported
    cases supported
    simp [resultHandles]
  | some application =>
    simp only [complete,StateT.run] at supported
    rw [compile_bind,mem_support_bind_iff] at supported
    obtain ⟨pinned,called,supported⟩ := supported
    rw [effects_neutral _ (pin_quiet before.pin) previous trace,support_map] at called
    obtain ⟨reached,_pinned,equal⟩ := called
    cases equal
    exact afterPin_handles source view failure allocation erased helper sign writer reserve before.control ready application
      reached.1 {before with sessions := before.sessions.set handle none} reached.2 trace result supported


/-- Every missing, consumed, failed or successful actual Server build has precisely its same returned response's public installation handles. -/
theorem body_handles (handle : Nat) (application : Option (Slice U8)) (before : ServerState)
    (previous : PublicState Platform) (trace : List PqxdhDeploymentInterface.Handle)
    (result : ((RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8) × ServerState) × PublicState Platform) × List PqxdhDeploymentInterface.Handle)
    (supported : result∈support (compile (n := n) (KemSK := KemSK)
      ((body source view failure allocation erased helper sign writer reserve handle application).run before) previous trace)) :
    result.2=trace++resultHandles result.1.1.1 := by
  cases stored : before.sessions[handle]? with
  | none=>
    simp only [body,build,StateT.run,RegistrationServerMaterialFrontend.take,stored,compile_pure,mem_support_pure_iff] at supported
    cases supported
    simp [resultHandles]
  | some entry=>cases entry with
    | none=>
      simp only [body,build,StateT.run,RegistrationServerMaterialFrontend.take,stored,compile_pure,mem_support_pure_iff] at supported
      cases supported
      simp [resultHandles]
    | some ready=>
        exact body_live_handles source view failure allocation erased helper sign writer reserve
          handle application before ready stored previous trace result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerControl

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerControl.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerControl.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerControl.body_live_handles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerControl.body_live_handles

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerControl.body_handles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerControl.body_handles
