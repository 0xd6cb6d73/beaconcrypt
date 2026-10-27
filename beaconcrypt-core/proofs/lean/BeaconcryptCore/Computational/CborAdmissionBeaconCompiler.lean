-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborAdmissionCompiler
import BeaconcryptCore.Computational.CborAdmissionCachedBudget
/-! Beacon sends prefetch the existing owner kernel before checking the complete CBOR frame size. Admitted sends reuse that cached kernel; rejected sends preserve the merged deployment state. The simulation covers inactive owners and retains the compiler invariant and public assignment counter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborAdmissionBeaconCompiler
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhDeploymentCompile (Kernel phaseKernel mergeOwner)
open CborAdmissionCompiler (Local Good merge)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

theorem inactive_send (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed)
    (index : Nat) (plaintext : Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK)
    (inactive : (state.native.owners[index]?).bind
      (fun owner => phaseKernel owner.beacon.phase) = none) :
    (PqxdhDeploymentNative.handler setup codec checks route seed (.inr (.beaconSend index plaintext))).run state =
      pure (none, state) := by
  simp only [PqxdhDeploymentNative.handler, PqxdhDeploymentNative.beaconStep, StateT.run]
  cases lookup : state.native.owners[index]?
  case some owner =>
    obtain ⟨bound, atIndex⟩ := List.getElem_of_getElem? lookup
    simp only [RawCtxBeaconLifecycle.beaconImpl]
    cases phase : owner.beacon.phase
    case established control associatedData kernel =>
      simp only [lookup, Option.bind_some, phase, phaseKernel, Option.some_ne_none] at inactive
    all_goals simp only [RawCtxBeaconLifecycle.rejected, PqxdhDeploymentNative.logged_pure,
      PqxdhDeploymentNative.record, PqxdhRegistrationSchedule.onShared,
      PqxdhServerAuthNative.nativeCtx, simulateQ_pure, StateT.run_pure, map_pure, pure_bind,
      PqxdhDeploymentNative.produce, List.map_nil, List.append_nil, Function.update_eq_self,
      ← atIndex, List.set_getElem_self bound]
  case none => rfl

theorem allowed_inactive (index : Nat) (plaintext : Pqxdh.Bytes)
    (state : PqxdhDeploymentNative.State KemSK)
    (inactive : (state.native.owners[index]?).bind
      (fun owner => phaseKernel owner.beacon.phase) = none) :
    CborProductionBoundary.allowed (.inr (.beaconSend index plaintext)) state = true := by
  cases lookup : state.native.owners[index]?
  case none => simp only [CborProductionBoundary.allowed, lookup]
  case some owner =>
    cases phase : owner.beacon.phase
    case established control associatedData kernel =>
      simp only [lookup, Option.bind_some, phase, phaseKernel, Option.some_ne_none] at inactive
    all_goals simp only [CborProductionBoundary.allowed, lookup, phase]

theorem native_inactive (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed)
    (index : Nat) (plaintext : Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK)
    (inactive : (state.native.owners[index]?).bind
      (fun owner => phaseKernel owner.beacon.phase) = none) :
    (CborAdmissionCompiler.nativeHandler setup codec checks route seed
      (.inr (.beaconSend index plaintext))).run state = pure (none, state) := by
  change (if CborProductionBoundary.allowed (.inr (.beaconSend index plaintext)) state then _ else _) = _
  rw [allowed_inactive index plaintext state inactive]
  exact inactive_send setup codec checks route seed index plaintext state inactive

theorem observed_some (copies : PqxdhDeploymentCompile.Local)
    (native : PqxdhRegistrationSchedule.State KemSK) (index : Nat) (kernel : Kernel)
    (selected : ((PqxdhDeploymentCompile.merge copies native).native.owners[index]?).bind
      (fun owner => phaseKernel owner.beacon.phase) = some kernel) :
    ∃ owner control associatedData old, native.owners[index]? = some owner ∧
      owner.beacon.phase = .established control associatedData old ∧
      (mergeOwner (copies.owners index) owner).beacon.phase = .established control associatedData kernel := by
  cases found : native.owners[index]?
  case none =>
    simp only [PqxdhDeploymentCompileRecords.merge_owner, found, Option.map_none,
      Option.bind_none] at selected
    cases selected
  case some owner =>
    rw [PqxdhDeploymentCompileRecords.merge_owner, found] at selected
    simp only [Option.map_some, Option.bind_some] at selected
    cases phase : owner.beacon.phase <;> cases cached : copies.owners index
    all_goals simp only [mergeOwner, phase, cached, phaseKernel, Option.some.injEq] at selected
    all_goals cases selected
    all_goals exact ⟨owner, _, _, _, rfl, phase, by
      simp only [mergeOwner, phase]⟩

theorem step_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (index : Nat)
    (plaintext : Pqxdh.Bytes) (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (good : Good setup codec memory native) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$>
      (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
        ((CborAdmissionCompiler.beaconSend setup codec index plaintext).run memory)).run native =
      (CborAdmissionCompiler.nativeHandler setup codec checks route seed (.inr (.beaconSend index plaintext))).run
        (merge memory native) := by
  change (fun result => (result.1.1, merge result.1.2 result.2)) <$>
    (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
      (CborAdmissionCompiler.beaconSend setup codec index plaintext memory)).run native = _
  by_cases inside : index < memory.copies.log.owners.length
  · simp only [CborAdmissionCompiler.beaconSend, inside, ite_true, simulateQ_bind, StateT.run_bind]
    rw [CborAdmissionPreload.owner_read_run setup codec checks seed memory.copies native good.nativeGood index,
      pure_bind]
    cases selected : ((PqxdhDeploymentCompile.merge memory.copies native).native.owners[index]?).bind
      (fun owner => phaseKernel owner.beacon.phase)
    case none =>
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      exact (native_inactive setup codec checks route seed index plaintext (merge memory native) selected).symm
    case some kernel =>
      obtain ⟨owner, control, associatedData, old, found, phase, mergedPhase⟩ :=
        observed_some memory.copies native index kernel selected
      have visible := (PqxdhDeploymentCompileInvariant.good_inv setup codec memory.copies native good.nativeGood).beaconVisible
        index owner control associatedData old found phase
      simp only [visible]
      have loadedGood := CborAdmissionPreload.preload_owner_good setup codec memory.copies native
        good.nativeGood index kernel ⟨owner, control, associatedData, old, found, phase⟩
      have preserved := CborAdmissionPreload.owner_merge memory.copies native index kernel selected
      have mergedFound : (PqxdhDeploymentCompile.merge memory.copies native).native.owners[index]? =
          some (mergeOwner (memory.copies.owners index) owner) := by
        rw [PqxdhDeploymentCompileRecords.merge_owner, found, Option.map_some]
      change _ = if CborProductionBoundary.allowed (.inr (.beaconSend index plaintext)) (merge memory native) then
        (PqxdhDeploymentNative.handler setup codec checks route seed (.inr (.beaconSend index plaintext))).run
          (merge memory native)
        else pure (CborProductionBoundary.reject (.inr (.beaconSend index plaintext)) (merge memory native))
      simp only [CborProductionBoundary.allowed, merge, mergedFound, mergedPhase,
        PqxdhDeploymentCompileRecords.mergeOwner_identityKeyId]
      split_ifs with fits
      case pos =>
        have old := PqxdhDeploymentCompileRecords.beacon_record setup codec checks seed index (.inl plaintext)
          { memory.copies with owners := Function.update memory.copies.owners index (some kernel) }
          native loadedGood.count loadedGood.copied
          (PqxdhDeploymentCompileInvariant.good_inv setup codec _ native loadedGood).beaconVisible
        rw [preserved] at old
        simpa only [simulateQ_map, StateT.run_map, Functor.map_map, PqxdhDeploymentNative.handler] using old
      case neg =>
        simp only [simulateQ_pure, StateT.run_pure, map_pure, CborProductionBoundary.reject, preserved]
  · simp only [CborAdmissionCompiler.beaconSend, inside, ite_false, simulateQ_pure, StateT.run_pure, map_pure]
    have absent : native.owners[index]? = none := List.getElem?_eq_none (by
      have count := good.nativeGood.count
      omega)
    have inactive : ((PqxdhDeploymentCompile.merge memory.copies native).native.owners[index]?).bind
        (fun owner => phaseKernel owner.beacon.phase) = none := by
      rw [PqxdhDeploymentCompileRecords.merge_owner, absent, Option.map_none, Option.bind_none]
    exact (native_inactive setup codec checks route seed index plaintext (merge memory native) inactive).symm

theorem good_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (_route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (index : Nat)
    (plaintext : Pqxdh.Bytes) (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (good : Good setup codec memory native)
    (result : (Option RawCtxSourceSend.Encrypted × Local) × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((simulateQ
      (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
      ((CborAdmissionCompiler.beaconSend setup codec index plaintext).run memory)).run native)) :
    Good setup codec result.1.2 result.2 := by
  change result ∈ support ((simulateQ
    (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
    (CborAdmissionCompiler.beaconSend setup codec index plaintext memory)).run native) at supported
  by_cases inside : index < memory.copies.log.owners.length
  · simp only [CborAdmissionCompiler.beaconSend, inside, ite_true, simulateQ_bind, StateT.run_bind] at supported
    rw [CborAdmissionPreload.owner_read_run setup codec checks seed memory.copies native good.nativeGood index,
      pure_bind] at supported
    cases selected : ((PqxdhDeploymentCompile.merge memory.copies native).native.owners[index]?).bind
      (fun owner => phaseKernel owner.beacon.phase)
    case none =>
      simp only [selected, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      simpa only [supported] using good
    case some kernel =>
      obtain ⟨owner, control, associatedData, old, found, phase, mergedPhase⟩ :=
        observed_some memory.copies native index kernel selected
      have visible := (PqxdhDeploymentCompileInvariant.good_inv setup codec memory.copies native good.nativeGood).beaconVisible
        index owner control associatedData old found phase
      have loadedGood := CborAdmissionPreload.preload_owner_good setup codec memory.copies native
        good.nativeGood index kernel ⟨owner, control, associatedData, old, found, phase⟩
      simp only [selected, visible] at supported
      split_ifs at supported with fits
      case pos =>
        simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
        obtain ⟨reached, supported, rfl⟩ := supported
        refine ⟨PqxdhDeploymentCompileInvariant.good_beacon_record setup codec checks seed
          index (.inl plaintext) _ native loadedGood reached supported, ?_⟩
        obtain ⟨⟨cache, preserved⟩, _⟩ := PqxdhDeploymentCompileInvariant.beaconLocal_support
          setup codec checks seed index (.inl plaintext) _ native reached supported
        simpa only [preserved, PqxdhDeploymentRecordCache.setCtx] using good.lastId
      case neg =>
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact ⟨loadedGood, good.lastId⟩
  · simp only [CborAdmissionCompiler.beaconSend, inside, ite_false, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at supported
    simpa only [supported] using good

end BeaconcryptCore.Computational.CborAdmissionBeaconCompiler

/-- info: 'BeaconcryptCore.Computational.CborAdmissionBeaconCompiler.inactive_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionBeaconCompiler.inactive_send

/-- info: 'BeaconcryptCore.Computational.CborAdmissionBeaconCompiler.allowed_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionBeaconCompiler.allowed_inactive

/-- info: 'BeaconcryptCore.Computational.CborAdmissionBeaconCompiler.native_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionBeaconCompiler.native_inactive

/-- info: 'BeaconcryptCore.Computational.CborAdmissionBeaconCompiler.observed_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionBeaconCompiler.observed_some

/-- info: 'BeaconcryptCore.Computational.CborAdmissionBeaconCompiler.step_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionBeaconCompiler.step_exact

/-- info: 'BeaconcryptCore.Computational.CborAdmissionBeaconCompiler.good_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionBeaconCompiler.good_support
