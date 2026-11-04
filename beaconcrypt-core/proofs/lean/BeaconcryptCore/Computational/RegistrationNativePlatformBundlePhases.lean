-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicationPhases
import BeaconcryptCore.Computational.RegistrationNativePlatformPendingTuple

/-! Every actual effectful source bundle changes no lifecycle phase, or returns its actual bytes while changing only its selected phase. Every resulting pending capability therefore comes from the earlier state or from this same successful source bundle; source writer failures cannot synthesize a pending capability. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBundlePhases
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner M)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeBundlePhases (phases masked Shape)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

def bytesReply (reply : RustM (Option (alloc.vec.Vec U8))) : RustM (Option Pqxdh.Bytes) := do
  let value ← reply
  .ok (value.map TranscriptAuthParts.absSlice)

private theorem state_pure_apply {S A : Type} {m : Type → Type} [Monad m]
    (value : A) (before : S) : (pure value : StateT S m A) before = pure (value, before) := rfl
private theorem state_get_apply {S : Type} {m : Type → Type} [Monad m]
    (before : S) : (get : StateT S m S) before = pure (before, before) := rfl

private theorem native_get (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (before : Local n KemSK source) :
    (RegistrationNativePlatformBundleLower.native coins setup checks representation created
      (get : M n KemSK source RegistrationServerRoleBackend.State (RegistrationNativeBeaconFrontend.State source))).run before =
      pure (before.1, before) := by
  simp only [RegistrationNativePlatformBundleLower.native, RegistrationNativeMldsaShared.lower, StateT.run,
    state_get_apply, state_pure_apply, simulateQ_pure, map_pure]

private theorem native_source (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : M n KemSK source RegistrationServerRoleBackend.State Value)
    (before after : Local n KemSK source) (previous next : Platform) (value : Value)
    (supported : ((value, after), next) ∈ support (((RegistrationNativePlatformBundleLower.native coins setup checks representation created work).run before).run previous)) :
    ((value, after.1), after.2.1) ∈ support ((work.run before.1).run before.2.1) := by
  have actual : (value, after) ∈ support ((lower setup checks representation created work).run before) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous next supported
  simp only [lower, StateT.run, support_map] at actual
  obtain ⟨inner, possible, same⟩ := actual
  have localEq := congrArg Prod.snd same
  have replyEq := congrArg Prod.fst same
  cases replyEq
  change (inner.1.1.2, (inner.1.2, inner.2)) = after at localEq
  rw [← localEq]
  apply OracleComp.support_simulateQ_run'_subset
    (RegistrationNativeExperiment.trusted setup checks representation created source) _ before.2.2
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst possible

private theorem sampled (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (draw : ProbComp Value)
    (before after : Local n KemSK source) (previous next : Platform) (value : Value)
    (supported : ((value, after), next) ∈ support (((RegistrationNativePlatformBundleLower.native coins setup checks representation created
      (RegistrationNativeBeaconFrontend.sample draw)).run before).run previous)) : after.1 = before.1 := by
  have actual := native_source coins setup checks representation created (RegistrationNativeBeaconFrontend.sample draw) before after previous next value supported
  rw [RegistrationNativeScalarSource.sample_effects] at actual
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map, support_map] at actual
  obtain ⟨inner, _possible, same⟩ := actual
  exact (congrArg (fun result : (Value × RegistrationNativeBeaconFrontend.State source) ×
    RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State => result.1.2) same).symm

private theorem masked_set (index : Nat) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (owners : RegistrationNativeBeaconFrontend.State source) :
    masked index (RegistrationNativePlatformBundleOwnerPhase.setPending owners index pending oneTime) = masked index owners := by
  cases found : owners[index]? with
  | none => simp only [RegistrationNativePlatformBundleOwnerPhase.setPending, found]
  | some owner => simp only [RegistrationNativePlatformBundleOwnerPhase.setPending, found, masked, phases, List.map_set, List.set_set]

private theorem after_shape (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (published : registration.PublishedBeaconInit (alloc.vec.Vec U8))
    (before : Local n KemSK source) (previous : Platform)
    (result : (RustM (Option (alloc.vec.Vec U8)) × Local n KemSK source) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformBundlePublication.afterPublished coins setup checks representation created
      index owner oneTime published).run before).run previous)) : Shape index before.1 (bytesReply result.1.1) result.1.2.1 := by
  have original := supported
  simp only [RegistrationNativePlatformBundlePublication.afterPublished, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨phase, _phaseCalled, advanced, _advancedCalled, returned⟩ := supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at returned
  cases returned
  have owners := RegistrationNativePlatformBundleOwnerPhase.afterPublished_owners coins setup checks representation created index owner oneTime published
    before advanced.1.2 previous advanced.2 published.encoded original
  exact Or.inr ⟨TranscriptAuthParts.absSlice published.encoded, rfl, (congrArg (masked index) owners).trans (masked_set index _ _ before.1)⟩

private theorem prefix_shape (target : Nat) (before middle after : RegistrationNativeBeaconFrontend.State source)
    (reply : RustM (Option Pqxdh.Bytes)) (unchanged : phases middle = phases before) (later : Shape target middle reply after) :
    Shape target before reply after := by
  rcases later with same | ⟨bytes, returned, same⟩
  · exact Or.inl (same.trans unchanged)
  · exact Or.inr ⟨bytes, returned, same.trans (congrArg (fun current => current.set target .fresh) unchanged)⟩

attribute [local irreducible] RegistrationNativePlatformBundleLower.native RegistrationNativePlatformGenericBundle.encoderWith

set_option maxHeartbeats 1000000 in
/-- Actual local bundle phases include every failed primitive, optional writer reply and divergence outcome. -/
theorem bundle (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat)
    (before : Local n KemSK source) (previous : Platform)
    (result : (RustM (Option (alloc.vec.Vec U8)) × Local n KemSK source) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformBundleLower.bundle coins setup checks representation created
      (RegistrationNativePlatformGenericBundle.encoderWith (source := source) (Auxiliary := RegistrationServerRoleBackend.State)
        (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := source) writer)) index).run before).run previous)) :
    Shape index before.1 (bytesReply result.1.1) result.1.2.1 := by
  simp only [RegistrationNativePlatformBundleLower.bundle, StateT.run_bind, native_get, pure_bind] at supported
  have encodingEq : (fun view => RegistrationNativePlatformBundleLower.lower
      (RegistrationNativePlatformGenericBundle.encoderWith (source := source) (Auxiliary := RegistrationServerRoleBackend.State)
        (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := source) writer) view)) =
      RegistrationNativePlatformInitWriterFrame.encoder (n := n) (KemSK := KemSK) (source := source) writer := rfl
  rw [encodingEq] at supported
  cases found : before.1[index]? with
  | none =>
    simp only [found, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    cases supported
    exact Or.inl rfl
  | some owner =>
    rw [found] at supported
    cases phase : owner.phase <;> simp only [phase] at supported
    all_goals try { simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported; cases supported; exact Or.inl rfl }
    case fresh =>
      simp only [StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨⟨oneTime, during⟩, platform⟩, sampledCall, ⟨⟨pubReply, afterPublication⟩, afterPlatform⟩, called, continued⟩ := supported
      have initial := congrArg phases (sampled coins setup checks representation created _ before during previous platform oneTime sampledCall)
      have publication : phases afterPublication.1 = phases during.1 := RegistrationNativePlatformPublicationPhases.outgoing coins setup checks representation created writer
        index owner oneTime during platform ((pubReply, afterPublication), afterPlatform) called
      apply prefix_shape index before.1 afterPublication.1 result.1.2.1 _ (publication.trans initial)
      cases pubReply with
      | fail error | div =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
        cases continued
        exact Or.inl rfl
      | ok answer => cases answer with
        | Err previous =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
          cases continued
          exact Or.inl rfl
        | Ok completed => exact after_shape coins setup checks representation created index owner oneTime completed afterPublication afterPlatform result continued
    case freshWithCoins oneTime =>
      simp only [StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨⟨pubReply, afterPublication⟩, afterPlatform⟩, called, continued⟩ := supported
      have publication : phases afterPublication.1 = phases before.1 := RegistrationNativePlatformPublicationPhases.outgoing coins setup checks representation created writer
        index owner oneTime before previous ((pubReply, afterPublication), afterPlatform) called
      apply prefix_shape index before.1 afterPublication.1 result.1.2.1 _ publication
      cases pubReply with
      | fail error | div =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
        cases continued
        exact Or.inl rfl
      | ok answer => cases answer with
        | Err previous =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
          cases continued
          exact Or.inl rfl
        | Ok completed => exact after_shape coins setup checks representation created index owner oneTime completed afterPublication afterPlatform result continued

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Literal source closure retains exactly the same all-outcome phase-change alternative. -/
theorem native_shape (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativeExperiment.State n KemSK source) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run before).run previous)) :
    Shape index before.beacons result.1.1 result.1.2.beacons := by
  rw [← RegistrationNativePlatformBundleLower.sourceBundle_actual] at supported
  simp only [RegistrationNativePlatformBundleLower.sourceBundle, StateT.run, map_apply, support_map] at supported
  obtain ⟨⟨⟨reply, current⟩, platform⟩, called, same⟩ := supported
  cases same
  exact bundle coins setup checks representation created writer index
    (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) previous ((reply, current), platform) called

private theorem pending_lookup (before after : RegistrationNativeBeaconFrontend.State source) (index : Nat)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (same : (phases after)[index]? = (phases before)[index]?)
    (present : RegistrationNativePendingFrames.PendingAt after index pending oneTime) :
    RegistrationNativePendingFrames.PendingAt before index pending oneTime := by
  obtain ⟨owner, found, phase⟩ := present
  have actual : (phases after)[index]? = some (.initSent pending oneTime) := by
    simp only [phases, List.getElem?_map, found, Option.map_some, phase]
  rw [same] at actual
  simp only [phases, List.getElem?_map] at actual
  obtain ⟨earlier, earlierFound, earlierPhase⟩ := Option.map_eq_some_iff.mp actual
  exact ⟨earlier, earlierFound, earlierPhase⟩

/-- A retained pending capability is inherited, or supplied by this same actual successful source bundle at its selected slot. -/
theorem native_pending (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (target : Nat)
    (before after : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform) (reply : RustM (Option Pqxdh.Bytes))
    (supported : ((reply, after), next) ∈ support (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer target).run before).run previous))
    (index : Nat) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (present : RegistrationNativePendingFrames.PendingAt after.beacons index pending oneTime) :
    RegistrationNativePendingFrames.PendingAt before.beacons index pending oneTime ∨
      ∃ bytes, index = target ∧ reply = .ok (some bytes) ∧
        Nonempty (RegistrationNativePlatformBundleOwnerPhase.Stored coins setup checks representation created writer target before after previous next bytes) := by
  rcases native_shape coins setup checks representation created writer target before previous ((reply, after), next) supported with unchanged | ⟨bytes, returned, same⟩
  · exact Or.inl (pending_lookup before.beacons after.beacons index pending oneTime
      (congrArg (fun current => current[index]?) unchanged) present)
  · change reply = .ok (some bytes) at returned
    by_cases selected : index = target
    · exact Or.inr ⟨bytes, selected, returned,
        RegistrationNativePlatformBundleOwnerPhase.native_bundle coins setup checks representation created writer target before after previous next bytes
          (by simpa only [returned] using supported)⟩
    · have atIndex := congrArg (fun current => current[index]?) same
      simp only [masked, List.getElem?_set_ne (Ne.symm selected)] at atIndex
      exact Or.inl (pending_lookup before.beacons after.beacons index pending oneTime atIndex present)

end BeaconcryptCore.Computational.RegistrationNativePlatformBundlePhases

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundlePhases.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundlePhases.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundlePhases.native_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundlePhases.native_shape

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundlePhases.native_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundlePhases.native_pending
