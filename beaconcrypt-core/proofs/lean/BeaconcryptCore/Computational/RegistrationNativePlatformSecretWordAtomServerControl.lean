-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerTrace
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionCredit
/-! The actual corrected moved-token Server controller funds each chronological installation attempt only from the Ready consumed at its literal initial take, including repeated pin, occupancy, mutable reserve and every publication or writer failure. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerControl
open PqxdhRecordLiftInterface (EnvEffects Role)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativePlatformBoundCompiler (PublicState)
open RegistrationNativeSecretWordFrontendTrace (State handler)
open RegistrationNativeSecretWordAtomInstallTrace (count atom)
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
  (simulateQ handler (simulateQ RegistrationNativePlatformSecretWordAtomServerTrace.embed (work.run before))).run trace

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
private theorem compile_map {B : Type} (work : Base n Platform A) (observe : A → B)
    (before : PublicState Platform) (trace : State) :
    compile (n := n) (KemSK := KemSK) (observe <$> work) before trace =
      (fun result => ((observe result.1.1, result.1.2), result.2)) <$> compile work before trace := by
  simp only [compile, StateT.run_map, simulateQ_map]

omit primitive in
private theorem pure_count (role : Role) (value : A) (before : PublicState Platform) (trace : State)
    (result : (A × PublicState Platform) × State)
    (supported : result ∈ support (compile (n := n) (KemSK := KemSK) (pure value) before trace)) :
    count role result.2 ≤ count role trace := by
  rw [compile_pure, mem_support_pure_iff] at supported
  cases supported
  exact Nat.le_refl _

omit primitive in
private theorem effects_neutral (work : StateT (PublicState Platform) (OracleComp (RegistrationNativePlatformEffectCompiler.Spec n)) A)
    (quiet : RegistrationNativePlatformPairedPublicationFree.Quiet work) (before : PublicState Platform) (trace : State) :
    compile (n := n) (KemSK := KemSK) (RegistrationNativePlatformSecretWordBuild.liftEffects work) before trace =
      (fun result => (result, trace)) <$> simulateQ RegistrationNativePlatformSecretWordAtomEffects.effects (work.run before) := by
  simp only [compile, RegistrationNativePlatformSecretWordBuild.liftEffects, RegistrationNativePlatformInterpret.state,
    StateT.run, ← QueryImpl.simulateQ_compose, RegistrationNativePlatformSecretWordAtomServerTrace.embed]
  rw [RegistrationNativePlatformSecretWordAtomEffects.embedding]
  simpa only [QueryImpl.simulateQ_compose, StateT.run] using
    RegistrationNativePlatformSecretWordAtomEffects.state_neutral (KemSK := KemSK) work quiet before trace

omit primitive in
private theorem effect_count (role : Role)
    (work : StateT (PublicState Platform) (OracleComp (RegistrationNativePlatformEffectCompiler.Spec n)) A)
    (quiet : RegistrationNativePlatformPairedPublicationFree.Quiet work) (before : PublicState Platform) (trace : State)
    (result : (A × PublicState Platform) × State)
    (supported : result ∈ support (compile (n := n) (KemSK := KemSK) (RegistrationNativePlatformSecretWordBuild.liftEffects work) before trace)) :
    count role result.2 ≤ count role trace := by
  rw [effects_neutral work quiet before trace, support_map] at supported
  obtain ⟨reached, _called, equal⟩ := supported
  cases equal
  exact Nat.le_refl _

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
local notation "adHashSource" => fun pending => RegistrationNativePlatformSecretWordBuild.liftEffects
  (RegistrationNativePlatformServerRestrictedService.adHash pending)

private theorem afterResult_count (role : Role) (control : pqxdh.ServerState) (reference : Message)
    (action : RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState))
    (before : ServerState) (previous : PublicState Platform) (trace : State)
    (result : ((RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8) × ServerState) × PublicState Platform) × State)
    (supported : result ∈ support (compile (n := n) (KemSK := KemSK)
      ((afterResult reserveSource serviceSource control reference action).run before) previous trace)) :
    count role result.2 ≤ count role trace + (if role = .server then 1 else 0) * atom (some reference) := by
  cases action with
  | fail error | div =>
    simp only [afterResult, StateT.run_pure] at supported
    have same := pure_count role _ previous trace result supported
    omega
  | ok value => cases value with
    | Err previousControl =>
      simp only [afterResult, StateT.run_pure] at supported
      have same := pure_count role _ previous trace result supported
      omega
    | Ok initial =>
      simp only [afterResult, StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left] at supported
      rw [compile_bind, mem_support_bind_iff] at supported
      obtain ⟨allowed, called, supported⟩ := supported
      have first := effect_count role _ (reserve_quiet reserve) previous trace allowed called
      cases allowedEq : allowed.1.1 with
      | false =>
        simp only [allowedEq, Bool.false_eq_true, ite_false, StateT.run_pure] at supported
        have last := pure_count role _ allowed.1.2 allowed.2 result supported
        omega
      | true =>
        simp only [allowedEq, ite_true, StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left] at supported
        rw [compile_bind, mem_support_bind_iff] at supported
        obtain ⟨published, called, supported⟩ := supported
        have second := RegistrationNativePlatformSecretWordAtomServerTrace.service_count source view failure allocation erased helper sign writer
          role control initial reference allowed.1.2 allowed.2 published called
        change result ∈ support (compile (pure (finish published.1.1 before)) published.1.2 published.2) at supported
        have last := pure_count role _ published.1.2 published.2 result supported
        omega

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
    simp only [bind_assoc, pure_bind]
    exact RegistrationNativePlatformPairedPublicationFree.bind_quiet _ _
      (effect_quiet _ (by intro role; simp [RegistrationNativeSecretWordAtomInstallCaps.InstallEnv]))
      (fun _ => RegistrationNativePlatformPairedPublicationFree.pure_quiet _)

private theorem afterOccupancy_count (role : Role) (control : pqxdh.ServerState) (lookup : peer.CompletionLookup)
    (reference : Message) (occupied : Bool) (before : ServerState) (previous : PublicState Platform)
    (trace : State)
    (result : ((RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8) × ServerState) × PublicState Platform) × State)
    (supported : result ∈ support (compile (n := n) (KemSK := KemSK)
      ((afterOccupancy adHashSource reserveSource serviceSource control lookup reference occupied).run before) previous trace)) :
    count role result.2 ≤ count role trace + (if role = .server then 1 else 0) * atom (some reference) := by
  cases selected : lookup.resume occupied with
  | fail error | div =>
    simp only [afterOccupancy, selected, StateT.run_pure] at supported
    have same := pure_count role _ previous trace result supported
    omega
  | ok answer => cases answer with
    | Err previousControl =>
      simp only [afterOccupancy, selected, StateT.run_pure] at supported
      have same := pure_count role _ previous trace result supported
      omega
    | Ok pending =>
      simp only [afterOccupancy, selected, StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left] at supported
      rw [compile_bind, mem_support_bind_iff] at supported
      obtain ⟨hashed, called, supported⟩ := supported
      rw [effects_neutral _ (adHash_quiet pending) previous trace, support_map] at called
      obtain ⟨reached, _hashed, returned⟩ := called
      cases returned
      exact afterResult_count source view failure allocation erased helper sign writer reserve role control reference
        _ before reached.2 trace result supported

private theorem afterPin_count (role : Role) (control : pqxdh.ServerState) (ready : ServerReady) (application : Slice U8)
    (current : RustM (core.option.Option session.ServerAuthenticationPin)) (before : ServerState)
    (previous : PublicState Platform) (trace : State)
    (result : ((RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8) × ServerState) × PublicState Platform) × State)
    (supported : result ∈ support (compile (n := n) (KemSK := KemSK)
      ((afterPin adHashSource reserveSource
        (fun keyId => RegistrationNativePlatformSecretWordBuild.liftEffects (RegistrationNativePlatformEffectCompiler.effect (.inr (.peerPresent keyId))))
        serviceSource control ready application current).run before) previous trace)) :
    count role result.2 ≤ count role trace + (if role = .server then 1 else 0) * atom (some ready.reference) := by
  cases current with
  | fail error | div =>
    simp only [afterPin, StateT.run] at supported
    have same := pure_count role _ previous trace result supported
    omega
  | ok value => cases value with
    | none =>
      simp only [afterPin, StateT.run] at supported
      have same := pure_count role _ previous trace result supported
      omega
    | some pin =>
      unfold afterPin at supported
      dsimp only [StateT.run] at supported
      cases beginning : peer.begin_completion_lookup control pin (RegistrationNativeSecretWordServerMaterial.token ready) application with
      | fail error | div =>
        simp only [beginning] at supported
        have same := pure_count role _ previous trace result supported
        omega
      | ok answer =>
        simp only [beginning] at supported
        cases answer with
        | Err state =>
          have same := pure_count role _ previous trace result supported
          omega
        | Ok lookup =>
          cases requested : lookup.request with
          | fail error | div =>
            simp only [requested] at supported
            have same := pure_count role _ previous trace result supported
            omega
          | ok keyId =>
            simp only [requested] at supported
            split at supported
            · rw [compile_bind, mem_support_bind_iff] at supported
              obtain ⟨occupied, called, supported⟩ := supported
              have first := effect_count role _ (effect_quiet (.inr (.peerPresent keyId))
                (by intro actual; simp [RegistrationNativeSecretWordAtomInstallCaps.InstallEnv])) previous trace occupied called
              have last := afterOccupancy_count source view failure allocation erased helper sign writer reserve role control lookup ready.reference
                occupied.1.1 before occupied.1.2 occupied.2 result supported
              exact last.trans (Nat.add_le_add_right first _)
            · have same := pure_count role _ previous trace result supported
              omega

/-- The actual corrected source build spends at most the atom weight moved before all pin, reserve, publication and writer outcomes. -/
theorem body_count (role : Role) (handle : Nat) (application : Option (Slice U8)) (before : ServerState)
    (previous : PublicState Platform) (trace : State)
    (result : ((RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8) × ServerState) × PublicState Platform) × State)
    (supported : result ∈ support (compile (n := n) (KemSK := KemSK)
      ((RegistrationNativePlatformSecretWordBuild.body source view failure allocation erased helper sign writer reserve handle application).run before)
        previous trace)) :
    count role result.2 ≤ count role trace + (if role = .server then 1 else 0) *
      RegistrationNativeSecretWordAtomSessionCredit.weight (RegistrationNativeSecretWordServerMaterial.take handle before).1 := by
  simp only [RegistrationNativePlatformSecretWordBuild.body, build, StateT.run] at supported
  rcases taken : RegistrationNativeSecretWordServerMaterial.take handle before with ⟨selected, moved⟩
  rw [taken] at supported
  change count role result.2 ≤ count role trace + (if role = .server then 1 else 0) *
    RegistrationNativeSecretWordAtomSessionCredit.weight selected
  cases selected with
  | none =>
    have same := pure_count role _ previous trace result supported
    simp only [RegistrationNativeSecretWordAtomSessionCredit.weight, Nat.mul_zero, Nat.add_zero]
    exact same
  | some ready => cases application with
    | none =>
      have same := pure_count role _ previous trace result supported
      omega
    | some application =>
      simp only [complete, StateT.run] at supported
      rw [compile_bind, mem_support_bind_iff] at supported
      obtain ⟨pinned, called, supported⟩ := supported
      have first := effect_count role _ (pin_quiet moved.pin) previous trace pinned called
      have last := afterPin_count source view failure allocation erased helper sign writer reserve role moved.control ready application
        pinned.1.1 moved pinned.1.2 pinned.2 result supported
      have word : atom (some ready.reference) = RegistrationNativeSecretWordAtomSessionCredit.weight (some ready) := by
        cases formed : ready.reference.kem <;> simp only [atom, RegistrationNativeSecretWordAtomSessionCredit.weight, formed]
      rw [word] at last
      exact last.trans (Nat.add_le_add_right first _)

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerControl

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerControl.body_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerControl.body_count
