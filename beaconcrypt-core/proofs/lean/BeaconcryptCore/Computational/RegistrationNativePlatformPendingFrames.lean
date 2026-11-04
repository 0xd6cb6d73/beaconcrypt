-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePendingFrames
import BeaconcryptCore.Computational.RegistrationNativePlatformFinishMetadata

/-! Corrected assigned-ID finish cannot introduce a pending Init capability. Every operation follows its actual source support, including authentication failure, agreement/open failure and source application copy before installation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPendingFrames
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (M Owner Phase)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeBeaconFootprint (ReadOnly)
open RegistrationNativePendingFrames (PendingAt Backwards)
variable {n : Nat} {ι KemSK Auxiliary Value Next Platform : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private def Keeps (work : M n KemSK source Auxiliary Value) : Prop :=
  ∀ owners env result, result ∈ support ((work.run owners).run env) → Backwards owners result.1.2

private theorem pure_keeps (value : Value) : Keeps (pure value : M n KemSK source Auxiliary Value) := by
  intro owners env result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact Backwards.refl owners

private theorem bind_keeps (work : M n KemSK source Auxiliary Value)
    (next : Value → M n KemSK source Auxiliary Next) (first : Keeps work) (later : ∀ value, Keeps (next value)) :
    Keeps (work >>= next) := by
  intro owners env result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact Backwards.trans owners middle.1.2 result.1.2
    (first owners env middle reached) (later middle.1.1 middle.1.2 middle.2 result continued)

private theorem readonly_keeps (work : M n KemSK source Auxiliary Value) (readonly : ReadOnly work) : Keeps work := by
  intro owners env result supported
  rw [readonly owners env result supported]
  exact Backwards.refl owners

private theorem lift_keeps (work : StateT (EnvState Auxiliary) (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) Value) :
    Keeps (StateT.lift work : M n KemSK source Auxiliary Value) := by
  intro owners env result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨middle, _reached, returned⟩ := supported
  cases returned
  exact Backwards.refl owners

private theorem get_keeps : Keeps (get : M n KemSK source Auxiliary (RegistrationNativeBeaconFrontend.State source)) := by
  intro owners env result supported
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact Backwards.refl owners

private theorem current_keeps (index : Nat) (change : Owner source → Owner source)
    (backward : ∀ owner pending oneTime, (change owner).phase = .initSent pending oneTime →
      owner.phase = .initSent pending oneTime) :
    Keeps ((modify fun owners => match owners[index]? with
      | none => owners
      | some owner => owners.set index (change owner)) : M n KemSK source Auxiliary Unit) := by
  intro owners env result supported
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  intro target pending oneTime entered
  obtain ⟨selected, found, phase⟩ := entered
  cases original : owners[index]? with
  | none => exact ⟨selected, by simpa only [original] using found, phase⟩
  | some owner =>
    simp only [original] at found
    by_cases same : index = target
    · subst target
      rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp original).1] at found
      cases found
      exact ⟨owner, original, backward owner pending oneTime phase⟩
    · rw [List.getElem?_set_ne same] at found
      exact ⟨selected, found, phase⟩

private theorem phase_keeps (index : Nat) (phase : Phase)
    (terminal : ∀ pending oneTime, phase ≠ .initSent pending oneTime) :
    Keeps (RegistrationNativeBeaconFrontend.updatePhase (n := n) (KemSK := KemSK) (mldsaSource := source)
      (Auxiliary := Auxiliary) index phase) :=
  current_keeps index (fun owner => { owner with phase })
    (fun _ pending oneTime same => (terminal pending oneTime same).elim)

private theorem abort_return (owner : Owner source) (value : Value) :
    Keeps (RegistrationNativeBeaconFrontend.abort owner *> pure value : M n KemSK source Auxiliary Value) := by
  rw [seqRight_eq_bind]
  exact bind_keeps _ _ (readonly_keeps _ (RegistrationNativeBeaconFootprint.abort_readonly owner))
    (fun _ => pure_keeps value)

private theorem install_keeps (index : Nat) (owner : Owner source) (completed : registration.CompletedBeacon) :
    Keeps (RegistrationNativePlatformBeaconFinish.install (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index owner completed) := by
  rw [RegistrationNativePlatformBeaconFinish.install_exact]
  apply bind_keeps _ _ (lift_keeps _)
  intro installed
  cases installed with
  | false => exact abort_return owner _
  | true => exact bind_keeps _ _ (phase_keeps index _ (fun _ _ impossible => Phase.noConfusion impossible)) (fun _ => pure_keeps _)

private theorem after_keeps (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (accepted : registration.AuthenticatedResponse) :
    Keeps (RegistrationNativePlatformBeaconFinish.afterAuthentication (n := n) (Auxiliary := Auxiliary) setup wire index owner oneTime accepted) := by
  unfold RegistrationNativePlatformBeaconFinish.afterAuthentication RegistrationNativePlatformBeaconFinish.afterAuthenticationWith
  apply bind_keeps _ _ (readonly_keeps _ (RegistrationNativeBeaconFootprint.program_readonly _
    (RegistrationNativeBeaconFootprint.agreement_readonly setup owner oneTime) _))
  intro agreed
  cases agreed with
  | fail error | div => exact abort_return owner _
  | ok effect =>
    cases effect
    all_goals first
      | exact abort_return owner _
      | apply bind_keeps _ _ (readonly_keeps _ (RegistrationNativeBeaconFootprint.program_readonly _
          (RegistrationNativeBeaconFootprint.record_readonly setup wire) _))
        intro opened
        cases opened with
        | fail error | div => exact abort_return owner _
        | ok answer => cases answer with
          | Err previous => exact abort_return owner _
          | Ok completed => exact install_keeps index owner completed

/-- Every actual corrected finish result retains or consumes an existing pending capability; none is synthesized. -/
theorem finish (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket) (owners : RegistrationNativeBeaconFrontend.State source)
    (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativeBeaconFrontend.State source) × EnvState Auxiliary)
    (supported : result ∈ support
      (((RegistrationNativePlatformBeaconFinish.finish (n := n) setup source wire index packet).run owners).run env)) :
    Backwards owners result.1.2 := by
  have law : Keeps (RegistrationNativePlatformBeaconFinish.finish (n := n) (Auxiliary := Auxiliary) setup source wire index packet) := by
    unfold RegistrationNativePlatformBeaconFinish.finish RegistrationNativePlatformBeaconFinish.finishWith
    apply bind_keeps _ _ get_keeps
    intro selectedOwners
    cases selectedOwners[index]? with
    | none => exact pure_keeps _
    | some owner =>
      simp only
      cases owner.phase with
      | fresh | freshWithCoins _ | established _ | aborted _ => exact pure_keeps _
      | initSent pending oneTime =>
        simp only
        cases pending.aborted_state with
        | fail error | div => exact pure_keeps _
        | ok aborted =>
          apply bind_keeps _ _ (phase_keeps index (.aborted aborted) (fun _ _ impossible => Phase.noConfusion impossible))
          intro _
          apply bind_keeps _ _ (readonly_keeps _ (RegistrationNativeBeaconFootprint.program_readonly _
            (RegistrationNativeBeaconFootprint.authentication_readonly setup) _))
          intro authenticated
          cases authenticated with
          | fail error | div => exact abort_return owner _
          | ok verdict => cases verdict with
            | Err rejected => exact abort_return owner _
            | Ok accepted => exact after_keeps setup wire index owner oneTime accepted
  exact law owners env result supported

/-- The literal nested corrected Platform finish inherits that exact pending frame at its actual native/platform poststates. -/
theorem native_finish (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket)
    (before after : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform) (reply : RustM (Option Pqxdh.Bytes))
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformExperiment.liftNative coins (RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet))).run before).run previous)) :
    Backwards before.beacons after.beacons := by
  have actual : (reply, after) ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet)).run before) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous next supported
  simp only [RegistrationNativeExperiment.beacon, StateT.run, bind_pure_comp, support_map] at actual
  obtain ⟨inner, possible, same⟩ := actual
  cases same
  apply finish setup wire index packet before.beacons (RegistrationWorldAgreementCompiler.erase before.server.world) inner.1
  apply OracleComp.support_simulateQ_run'_subset
    (RegistrationNativeExperiment.trusted setup checks representation created source) _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst possible

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem server_frame (work : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Value)
    (before after : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform) (reply : Value)
    (supported : ((reply, after), next) ∈ support (((RegistrationNativePlatformExperiment.server work).run before).run previous)) :
    after.beacons = before.beacons := by
  simp only [RegistrationNativePlatformExperiment.server, StateT.run, map_apply, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  exact (congrArg (fun result => result.1.2.beacons) same).symm

variable {E : Type} [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]

/-- Every actual corrected typed callback except bundle transports exact pending capabilities backwards, including stateful source accept/build and assigned-ID finish. -/
theorem handler (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (allowed : RegistrationNativePendingFrames.NonBundle query)
    (before after : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformExperiment.handler (n := n) coins setup checks wire route representation created source credential view failure
        allocation reserveRegistration reservePeer erased helper writer query).run before).run previous)) :
    Backwards before.beacons after.beacons := by
  have ordinary (same : RegistrationNativePlatformExperiment.handler (n := n) coins setup checks wire route representation created source credential view failure
      allocation reserveRegistration reservePeer erased helper writer query =
      RegistrationNativePlatformExperiment.liftNative (n := n) coins (RegistrationNativeExperiment.handler setup checks wire route representation created source credential query)) :
      Backwards before.beacons after.beacons := by
    rw [same] at supported
    have actual := RegistrationNativePlatformHashReceipt.native_support coins _ _ previous next supported
    exact RegistrationNativePendingFrames.handler setup checks wire route representation created credential query allowed before (reply, after) actual
  cases query with
  | inl coin => exact ordinary rfl
  | inr command => cases command with
    | bundle index => exact False.elim allowed
    | finish index packet => exact native_finish coins setup checks representation created wire index packet before after previous next reply supported
    | accept packet =>
      simp only [RegistrationNativePlatformExperiment.handler, StateT.run_bind, StateT.run_modify, pure_bind] at supported
      have owners := server_frame _ _ after previous next reply supported
      rw [owners]
      exact Backwards.refl _
    | build index application =>
      simp only [RegistrationNativePlatformExperiment.handler, StateT.run, bind_pure_comp, map_apply, support_map] at supported
      obtain ⟨⟨⟨result, current⟩, platform⟩, called, same⟩ := supported
      have afterEq : current = after := congrArg (fun result => result.1.2) same
      cases afterEq
      have platformEq : platform = next := congrArg Prod.snd same
      cases platformEq
      have owners := server_frame _ before after previous next result called
      rw [owners]
      exact Backwards.refl _
    | create _ _ _ | hmac _ _ | hash _ | serverSend _ _ | serverRaw _ | beaconSend _ _ | beaconRaw _ _ => exact ordinary rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPendingFrames

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPendingFrames.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPendingFrames.finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPendingFrames.native_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPendingFrames.native_finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPendingFrames.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPendingFrames.handler
