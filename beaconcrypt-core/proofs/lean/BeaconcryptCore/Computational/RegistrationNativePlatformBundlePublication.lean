-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInitTupleCache
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetadata
import BeaconcryptCore.Computational.RegistrationNativeWorldCache

/-! A successful complete source bundle selects an actual existing owner/scalar, reaches its literal effectful source publication and then retains its actual phase-update/lifecycle suffix. The terminal writer and external states remain in the same execution. This supplies source-stage receipts without a static encoder equation or desired partner premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBundlePublication
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner M)
open RegistrationNativeMldsaShared (Local)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

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

noncomputable def afterPublished (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (published : registration.PublishedBeaconInit (alloc.vec.Vec U8)) :
    StateT (Local n KemSK source) (StateT Platform ProbComp) (RustM (Option (alloc.vec.Vec U8))) := do
  RegistrationNativePlatformBundleLower.native coins setup checks representation created
    (RegistrationNativeBeaconFrontend.updatePhase index (.initSent published.pending oneTime))
  let _ ← RegistrationNativePlatformBundleLower.native coins setup checks representation created
    (RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent)))
  pure (.ok (some published.encoded))

private theorem afterPublished_bytes (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (published : registration.PublishedBeaconInit (alloc.vec.Vec U8))
    (before after : Local n KemSK source) (previous next : Platform) (bytes : alloc.vec.Vec U8)
    (supported : ((.ok (some bytes), after), next) ∈ support
      (((afterPublished coins setup checks representation created index owner oneTime published).run before).run previous)) :
    published.encoded = bytes := by
  simp only [afterPublished, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨first, _phase, second, _advanced, returned⟩ := supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at returned
  exact (Option.some.inj (RustM.ok.inj returned.1.1)).symm

structure Cut (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before after : Local n KemSK source) (previous next : Platform) (bytes : alloc.vec.Vec U8) where
  owner : Owner source
  oneTime : PqxdhJointGapDh.ScalarBytes
  atPublication : Local n KemSK source
  publicationPlatform : Platform
  published : registration.PublishedBeaconInit (alloc.vec.Vec U8)
  afterPublication : Local n KemSK source
  afterPublicationPlatform : Platform
  found : before.1[index]? = some owner
  selected : (owner.phase = .fresh ∧ ((oneTime, atPublication), publicationPlatform) ∈ support
    (((RegistrationNativePlatformBundleLower.native coins setup checks representation created
      (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar)).run before).run previous)) ∨
    (owner.phase = .freshWithCoins oneTime ∧ atPublication = before ∧ publicationPlatform = previous)
  publicationCalled : ((.ok (.Ok published), afterPublication), afterPublicationPlatform) ∈ support
    (((RegistrationNativePlatformInitTupleCache.program coins setup checks representation created writer index owner oneTime).run atPublication).run publicationPlatform)
  continued : ((.ok (some bytes), after), next) ∈ support
    (((afterPublished coins setup checks representation created index owner oneTime published).run afterPublication).run afterPublicationPlatform)
  encoded : published.encoded = bytes

/-- Actual complete local source bundle success retains its literal selected owner/scalar, source publication and later phase/advance calls. -/
theorem bundle (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before after : Local n KemSK source) (previous next : Platform) (bytes : alloc.vec.Vec U8)
    (supported : ((.ok (some bytes), after), next) ∈ support
      (((RegistrationNativePlatformBundleLower.bundle coins setup checks representation created
        (RegistrationNativePlatformGenericBundle.encoderWith (source := source) (Auxiliary := RegistrationServerRoleBackend.State)
          (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := source) writer)) index).run before).run previous)) :
    Nonempty (Cut coins setup checks representation created writer index before after previous next bytes) := by
  simp only [RegistrationNativePlatformBundleLower.bundle, StateT.run_bind, native_get, pure_bind] at supported
  have encodingEq : (fun view => RegistrationNativePlatformBundleLower.lower
      (RegistrationNativePlatformGenericBundle.encoderWith (source := source) (Auxiliary := RegistrationServerRoleBackend.State)
        (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := source) writer) view)) =
      RegistrationNativePlatformInitWriterFrame.encoder (n := n) (KemSK := KemSK) (source := source) writer := rfl
  rw [encodingEq] at supported
  cases found : before.1[index]? with
  | none => simp [found, StateT.run_pure] at supported
  | some owner =>
    rw [found] at supported
    cases phase : owner.phase <;> simp only [phase] at supported
    all_goals try { simp [StateT.run_pure] at supported }
    case fresh =>
      simp only [StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨⟨oneTime, during⟩, platform⟩, sampled,
        ⟨⟨pubReply, afterPublication⟩, afterPlatform⟩, publishedCall, continued⟩ := supported
      cases actual : pubReply with
      | fail error | div => simp [actual, StateT.run_pure] at continued
      | ok answer => cases answer with
        | Err previous => simp [actual, StateT.run_pure] at continued
        | Ok published =>
          have called : ((.ok (.Ok published), afterPublication), afterPlatform) ∈ support
              (((RegistrationNativePlatformInitTupleCache.program coins setup checks representation created writer index owner oneTime).run during).run platform) := by
            simpa only [RegistrationNativePlatformInitTupleCache.program, actual] using publishedCall
          have suffix : ((.ok (some bytes), after), next) ∈ support
              (((afterPublished coins setup checks representation created index owner oneTime published).run afterPublication).run afterPlatform) := by
            simpa only [afterPublished, actual] using continued
          exact ⟨⟨owner, oneTime, during, platform, published, afterPublication, afterPlatform, found,
            Or.inl ⟨phase, sampled⟩, called, suffix,
            afterPublished_bytes coins setup checks representation created index owner oneTime published afterPublication after afterPlatform next bytes suffix⟩⟩
    case freshWithCoins oneTime =>
      simp only [StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨⟨pubReply, afterPublication⟩, afterPlatform⟩, publishedCall, continued⟩ := supported
      cases actual : pubReply with
      | fail error | div => simp [actual, StateT.run_pure] at continued
      | ok answer => cases answer with
        | Err previous => simp [actual, StateT.run_pure] at continued
        | Ok published =>
          have called : ((.ok (.Ok published), afterPublication), afterPlatform) ∈ support
              (((RegistrationNativePlatformInitTupleCache.program coins setup checks representation created writer index owner oneTime).run before).run previous) := by
            simpa only [RegistrationNativePlatformInitTupleCache.program, actual] using publishedCall
          have suffix : ((.ok (some bytes), after), next) ∈ support
              (((afterPublished coins setup checks representation created index owner oneTime published).run afterPublication).run afterPlatform) := by
            simpa only [afterPublished, actual] using continued
          exact ⟨⟨owner, oneTime, before, previous, published, afterPublication, afterPlatform, found,
            Or.inr ⟨phase, rfl, rfl⟩, called, suffix,
            afterPublished_bytes coins setup checks representation created index owner oneTime published afterPublication after afterPlatform next bytes suffix⟩⟩

/-- The actual post-publication phase and lifecycle suffix preserves the earlier shared-cache receipts. -/
theorem afterPublished_cache (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (published : registration.PublishedBeaconInit (alloc.vec.Vec U8))
    (before after : Local n KemSK source) (previous next : Platform) (bytes : alloc.vec.Vec U8)
    (supported : ((.ok (some bytes), after), next) ∈ support
      (((afterPublished coins setup checks representation created index owner oneTime published).run before).run previous)) :
    RegistrationNativeWorldCache.cache before.2.2 ≤ RegistrationNativeWorldCache.cache after.2.2 := by
  simp only [afterPublished, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨phaseReply, phaseAfter⟩, phasePlatform⟩, phaseCalled,
    ⟨⟨advanceReply, advanceAfter⟩, advancePlatform⟩, advanceCalled, returned⟩ := supported
  have first : (phaseReply, phaseAfter) ∈ support ((RegistrationNativeMldsaShared.lower setup checks representation created
      (RegistrationNativeBeaconFrontend.updatePhase index (.initSent published.pending oneTime))).run before) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous phasePlatform phaseCalled
  have second : (advanceReply, advanceAfter) ∈ support ((RegistrationNativeMldsaShared.lower setup checks representation created
      (RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent)))).run phaseAfter) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ phasePlatform advancePlatform advanceCalled
  have firstExtension := RegistrationNativeWorldCache.localProgram setup checks representation created _ before (phaseReply, phaseAfter) first
  have secondExtension := RegistrationNativeWorldCache.localProgram setup checks representation created _ phaseAfter (advanceReply, advanceAfter) second
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at returned
  exact (firstExtension.trans secondExtension).trans_eq (congrArg (fun state : Local n KemSK source => RegistrationNativeWorldCache.cache state.2.2) returned.1.2.symm)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Public native source bundle success retains the same literal local publication cut, external states and source bytes. -/
theorem native_bundle (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before after : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform) (bytes : Pqxdh.Bytes)
    (supported : ((.ok (some bytes), after), next) ∈ support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run before).run previous)) :
    ∃ (encoded : alloc.vec.Vec U8) (localAfter : Local n KemSK source),
      TranscriptAuthParts.absSlice encoded = bytes ∧ RegistrationNativeMldsaShared.close localAfter = after ∧
      Nonempty (Cut coins setup checks representation created writer index
        (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) localAfter previous next encoded) := by
  rw [← RegistrationNativePlatformBundleLower.sourceBundle_actual] at supported
  simp only [RegistrationNativePlatformBundleLower.sourceBundle, StateT.run, map_apply, support_map] at supported
  obtain ⟨⟨⟨raw, localAfter⟩, platform⟩, called, same⟩ := supported
  have replyEq := congrArg (fun result => result.1.1) same
  have nativeEq : RegistrationNativeMldsaShared.close localAfter = after := congrArg (fun result => result.1.2) same
  have platformEq : platform = next := congrArg Prod.snd same
  cases platformEq
  cases raw with
  | fail error | div => cases replyEq
  | ok optional => cases optional with
    | none => cases replyEq
    | some encoded =>
      have bytesEq : TranscriptAuthParts.absSlice encoded = bytes := Option.some.inj (RustM.ok.inj replyEq)
      exact ⟨encoded, localAfter, bytesEq, nativeEq,
        bundle coins setup checks representation created writer index
          (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) localAfter previous next encoded called⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformBundlePublication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundlePublication.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundlePublication.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundlePublication.afterPublished_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundlePublication.afterPublished_cache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundlePublication.native_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundlePublication.native_bundle
