-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBundlePublication

/-! Successful actual source bundle installs exactly the reached publication's pending phase at its original owner slot. The owner metadata is the actual complete-bundle frame, and all Local/platform states and suffix calls come from the literal source cut. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBundleOwnerPhase
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner M)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeOwnerFields (metadata)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

def setPending (owners : RegistrationNativeBeaconFrontend.State source) (index : Nat)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes) :=
  match owners[index]? with
  | none => owners
  | some current => owners.set index { current with phase := .initSent pending oneTime }

private theorem native_source (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
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

/-- Actual phase update and World advance have exactly the source owner-list result, including an absent slot. -/
theorem afterPublished_owners (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (published : registration.PublishedBeaconInit (alloc.vec.Vec U8))
    (before after : Local n KemSK source) (previous next : Platform) (bytes : alloc.vec.Vec U8)
    (supported : ((.ok (some bytes), after), next) ∈ support
      (((RegistrationNativePlatformBundlePublication.afterPublished coins setup checks representation created index owner oneTime published).run before).run previous)) :
    after.1 = setPending before.1 index published.pending oneTime := by
  simp only [RegistrationNativePlatformBundlePublication.afterPublished, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨phaseReply, phaseAfter⟩, phasePlatform⟩, phaseCalled,
    ⟨⟨advanceReply, advanceAfter⟩, advancePlatform⟩, advanceCalled, returned⟩ := supported
  have phaseSource := native_source coins setup checks representation created
    (RegistrationNativeBeaconFrontend.updatePhase index (.initSent published.pending oneTime)) before phaseAfter previous phasePlatform phaseReply phaseCalled
  simp only [RegistrationNativeBeaconFrontend.updatePhase, StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at phaseSource
  have phaseEq : phaseAfter.1 = setPending before.1 index published.pending oneTime := congrArg (fun result => result.1.2) phaseSource
  have advanceSource := native_source coins setup checks representation created
    (RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent))) phaseAfter advanceAfter phasePlatform advancePlatform advanceReply advanceCalled
  simp only [RegistrationNativeBeaconFrontend.effect, StateT.run_lift, bind_pure_comp,
    StateT.run_map, Functor.map_map, support_map] at advanceSource
  obtain ⟨raw, _called, same⟩ := advanceSource
  have advanceEq : advanceAfter.1 = phaseAfter.1 := (congrArg (fun result => result.1.2) same).symm
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at returned
  exact (congrArg Prod.fst returned.1.2).trans (advanceEq.trans phaseEq)

structure Stored (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before after : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform) (bytes : Pqxdh.Bytes) where
  encoded : alloc.vec.Vec U8
  localAfter : Local n KemSK source
  cut : RegistrationNativePlatformBundlePublication.Cut coins setup checks representation created writer index
    (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) localAfter previous next encoded
  bytesEq : TranscriptAuthParts.absSlice encoded = bytes
  nativeEq : RegistrationNativeMldsaShared.close localAfter = after
  current : Owner source
  found : after.beacons[index]? = some current
  phase : current.phase = .initSent cut.published.pending cut.oneTime
  metadataEq : metadata current = metadata cut.owner

/-- Literal complete native source bundle success retains that actual owner slot, exact reached pending capability and immutable source owner fields. -/
theorem native_bundle (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before after : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform) (bytes : Pqxdh.Bytes)
    (supported : ((.ok (some bytes), after), next) ∈ support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run before).run previous)) :
    Nonempty (Stored coins setup checks representation created writer index before after previous next bytes) := by
  obtain ⟨encoded, localAfter, bytesEq, nativeEq, ⟨cut⟩⟩ := RegistrationNativePlatformBundlePublication.native_bundle
    coins setup checks representation created writer index before after previous next bytes supported
  have fullMetadata := RegistrationNativePlatformBundleMetadata.native_bundle coins setup checks representation created source writer index
    before after previous next (.ok (some bytes)) supported
  have finalMetadata : (after.beacons.map metadata)[index]? = some (metadata cut.owner) := by
    rw [fullMetadata, List.getElem?_map, cut.found]
    rfl
  have ownersEq : localAfter.1 = after.beacons := congrArg (fun current => current.beacons) nativeEq
  have stored := afterPublished_owners coins setup checks representation created index cut.owner cut.oneTime cut.published
    cut.afterPublication localAfter cut.afterPublicationPlatform next encoded cut.continued
  rw [ownersEq] at stored
  cases original : cut.afterPublication.1[index]? with
  | none =>
    simp only [stored, setPending, original, List.getElem?_map, Option.map_none] at finalMetadata
    cases finalMetadata
  | some current =>
    have found : after.beacons[index]? = some { current with phase := .initSent cut.published.pending cut.oneTime } := by
      rw [stored]
      simp only [setPending, original]
      exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp original).1
    simp only [List.getElem?_map, found, Option.map_some, Option.some.injEq] at finalMetadata
    refine ⟨⟨encoded, localAfter, cut, bytesEq, nativeEq, { current with phase := .initSent cut.published.pending cut.oneTime }, found, rfl, ?_⟩⟩
    exact finalMetadata

end BeaconcryptCore.Computational.RegistrationNativePlatformBundleOwnerPhase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleOwnerPhase.afterPublished_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleOwnerPhase.afterPublished_owners

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleOwnerPhase.native_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleOwnerPhase.native_bundle
