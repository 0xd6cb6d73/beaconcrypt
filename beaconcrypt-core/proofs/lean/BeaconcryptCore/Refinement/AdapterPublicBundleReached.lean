-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicBundleMaterialLifetime
import BeaconcryptCore.Computational.RegistrationNativeBundleLifetime
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetadata
import BeaconcryptCore.Computational.RegistrationNativePlatformBundlePhases
/-! Every actual successful or failed bundle publication retains the exact source private-material relation at its final native owner and World slot. Metadata and phase facts are derived from the literal native bundle run, and the full private-pool/World frame follows from the actual publication and sampler. Fresh private-key representation remains the individual generation contract; failure discards the local generated object while retaining the caller RNG in the separate joint source theorem. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicBundleReached
open BeaconcryptCore.Computational
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeOwnerFields (metadata)
variable {n : Nat} {KemSK : Type} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

theorem pending_fields (index : Nat) (owner : Owner source) (pending : registration.BeaconPending)
    (scalar : PqxdhJointGapDh.ScalarBytes) (before during : Native)
    (selected : before.beacons[index]? = some owner)
    (same : (RegistrationNativeBundleTerminal.after index owner pending scalar during).beacons.map metadata = before.beacons.map metadata) :
    ∃ current, (RegistrationNativeBundleTerminal.after index owner pending scalar during).beacons[index]? = some current ∧
      current.phase = .initSent pending scalar ∧ metadata current = metadata owner := by
  have found : ((RegistrationNativeBundleTerminal.after index owner pending scalar during).beacons.map metadata)[index]? = some (metadata owner) := by
    rw [same, List.getElem?_map, selected]
    rfl
  cases duringFound : during.beacons[index]? with
  | none =>
      simp only [RegistrationNativeBundleTerminal.after, RegistrationNativeFinishTerminal.setPhase,
        duringFound, List.getElem?_map, Option.map_none] at found
      cases found
  | some current =>
      have finalFound := AdapterPublicBundleMaterialLifetime.after_owner index owner current pending scalar during duringFound
      refine ⟨{current with phase := .initSent pending scalar}, finalFound, rfl, ?_⟩
      simpa only [List.getElem?_map, finalFound, Option.map_some, Option.some.injEq] using found

variable [material : PublicWrapperPlatform.Material]
variable [ed : AdapterInitEdPrimitive.Operations]
theorem pending_material (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (joint : PqxdhJointIdentity.Primitives) (index : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (owner : Owner source) (before during : Native)
    (related : AdapterPublicWrapperState.Beacon view joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (selected : before.beacons[index]? = some owner)
    (identifier : AdapterPublicWrapperState.currentId owner = owner.pin.binding.identity_key_id)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (scalar : PqxdhJointGapDh.ScalarBytes) (finished : registration.PublishedBeaconInit (alloc.vec.Vec U8))
    (same : (RegistrationNativeBundleTerminal.after index owner finished.pending scalar during).beacons.map metadata = before.beacons.map metadata)
    (prekeyView : AdapterPublicWrapperState.KxPair view prekey owner.prekeyScalar owner.prekeyPublic)
    (oneTimeView : view.kxSecret oneTime.secret_key = scalar)
    (kemView : AdapterPublicWrapperState.KemPair view before.pool kem owner.kemHandle owner.kemPublic)
    (pool : during.pool = before.pool)
    (ready : RegistrationNativeBundleTerminal.Ready during.server.world.world.1 owner.worldOwner) :
    ∃ current, (RegistrationNativeBundleTerminal.after index owner finished.pending scalar during).beacons[index]? = some current ∧
      AdapterPublicWrapperState.Beacon view joint (RegistrationNativeBundleTerminal.after index owner finished.pending scalar during).pool
        {self with state := .InitSent finished.pending prekey oneTime kem} current
        (RegistrationNativeBundleTerminal.after index owner finished.pending scalar during).server.world.world.1.owners[current.worldOwner]? := by
  obtain ⟨current, found, phase, fields⟩ := pending_fields index owner finished.pending scalar before during selected same
  refine ⟨current, found, ?_⟩
  have worldOwner : current.worldOwner = owner.worldOwner := congrArg (fun value => value.worldOwner) fields
  have world : (RegistrationNativeBundleTerminal.after index owner finished.pending scalar during).server.world.world.1.owners[current.worldOwner]? = some (.inactive .initSent) := by
    rw [worldOwner]
    exact AdapterPublicBundleMaterialLifetime.advanced_owner during.server.world.world.1 owner.worldOwner ready
  rw [world]
  change AdapterPublicWrapperState.Beacon view joint during.pool _ _ _
  rw [pool]
  exact AdapterPublicBundleMaterialLifetime.installed view joint before.pool self owner current _ related identifier
    prekey oneTime kem scalar prekeyView oneTimeView kemView finished fields phase


variable {I E Platform : Type} {base : OracleSpec I}
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

theorem with_coins_material (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (index : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source) (before during : Native)
    (previous next : Platform)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (selected : before.beacons[index]? = some owner)
    (control : pqxdh.BeaconFresh) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (scalar : PqxdhJointGapDh.ScalarBytes) (stored : self.state = .FreshWithCoins control prekey oneTime kem)
    (phase : owner.phase = .freshWithCoins scalar) (finished : registration.PublishedBeaconInit (alloc.vec.Vec U8))
    (reached : ((.ok (.Ok finished), during), next) ∈ support
      (((RegistrationNativeBundleLifetime.tree coins setup checks representation created writer index owner scalar).run before).run previous)) :
    ∃ current, (RegistrationNativeBundleTerminal.after index owner finished.pending scalar during).beacons[index]? = some current ∧
      AdapterPublicWrapperState.Beacon view setup.joint (RegistrationNativeBundleTerminal.after index owner finished.pending scalar during).pool
        {self with state := .InitSent finished.pending prekey oneTime kem} current
        (RegistrationNativeBundleTerminal.after index owner finished.pending scalar during).server.world.world.1.owners[current.worldOwner]? := by
  have ready := RegistrationNativeBundleLifetime.with_coins_ready setup view self owner before related control prekey oneTime kem scalar stored phase
  have kept := RegistrationNativeBundleSafety.interpreted_snapshot coins setup checks representation created writer _
    (RegistrationNativeBundleSafety.publication_safe setup index owner scalar) before previous ((.ok (.Ok finished), during), next) reached
  have owners : during.server.world.world.1.owners = before.server.world.world.1.owners := congrArg Prod.fst kept
  have terminalReady : RegistrationNativeBundleTerminal.Ready during.server.world.world.1 owner.worldOwner := by
    simpa only [RegistrationNativeBundleTerminal.Ready, owners] using ready
  have actual : ((.ok (some (TranscriptAuthParts.absSlice finished.encoded)), RegistrationNativeBundleTerminal.after index owner finished.pending scalar during), next) ∈ support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run before).run previous) := by
    rw [RegistrationNativeBundleLifetime.with_coins coins setup checks representation created writer index owner scalar before previous selected phase ready, support_map]
    exact ⟨((.ok (.Ok finished), during), next), reached, rfl⟩
  have fields := RegistrationNativePlatformBundleMetadata.native_bundle coins setup checks representation created source writer index before
    (RegistrationNativeBundleTerminal.after index owner finished.pending scalar during) previous next (.ok (some (TranscriptAuthParts.absSlice finished.encoded))) actual
  have data := related.phase
  simp only [AdapterPublicWrapperState.Phase, stored, phase] at data
  have identifier : AdapterPublicWrapperState.currentId owner = owner.pin.binding.identity_key_id := by
    simp only [AdapterPublicWrapperState.currentId, phase]
  exact pending_material view setup.joint index self owner before during related selected identifier prekey oneTime kem scalar finished fields
    data.2.1 data.2.2.1 data.2.2.2.1 (congrArg Prod.snd kept) terminalReady

omit material ed in
theorem fresh_snapshot (index : Nat) (owner : Owner source) (before : Native) (previous : Platform)
    (result : ((PqxdhJointGapDh.ScalarBytes × RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) × Native) × Platform)
    (reached : result ∈ support (((RegistrationNativeBundleLifetime.fresh_tree coins setup checks representation created writer index owner).run before).run previous)) :
    RegistrationNativeBundleSafety.Snapshot result.1.2 = RegistrationNativeBundleSafety.Snapshot before := by
  have run : ((RegistrationNativeBundleLifetime.fresh_tree coins setup checks representation created writer index owner).run before).run previous = (do
      let drawn ← ((RegistrationNativeBundleLifetime.sample coins setup checks representation created writer).run before).run previous
      (fun completed => (((drawn.1.1, completed.1.1), completed.1.2), completed.2)) <$>
        ((RegistrationNativeBundleLifetime.tree coins setup checks representation created writer index owner drawn.1.1).run drawn.1.2).run drawn.2) := by
    simp only [RegistrationNativeBundleLifetime.fresh_tree, StateT.run_bind, bind_pure_comp, StateT.run_map]
  rw [run, mem_support_bind_iff] at reached
  obtain ⟨drawn, sampled, continued⟩ := reached
  rw [support_map] at continued
  obtain ⟨published, called, same⟩ := continued
  have original := RegistrationNativeBundleSafety.sample_snapshot coins setup checks representation created writer
    PqxdhJointGapDh.sampleScalar before previous drawn sampled
  have later := RegistrationNativeBundleSafety.interpreted_snapshot coins setup checks representation created writer _
    (RegistrationNativeBundleSafety.publication_safe setup index owner drawn.1.1) drawn.1.2 drawn.2 published called
  have equality : published.1.2 = result.1.2 := congrArg (fun value => value.1.2) same
  rw [← equality]
  exact later.trans original


theorem fresh_material (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (index : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source) (before during : Native)
    (previous next : Platform)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (selected : before.beacons[index]? = some owner)
    (control : pqxdh.BeaconFresh) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (scalar : PqxdhJointGapDh.ScalarBytes) (stored : self.state = .Fresh control prekey kem)
    (phase : owner.phase = .fresh) (finished : registration.PublishedBeaconInit (alloc.vec.Vec U8))
    (privateView : view.kxSecret oneTime.secret_key = scalar)
    (reached : (((scalar, .ok (.Ok finished)), during), next) ∈ support
      (((RegistrationNativeBundleLifetime.fresh_tree coins setup checks representation created writer index owner).run before).run previous)) :
    ∃ current, (RegistrationNativeBundleTerminal.after index owner finished.pending scalar during).beacons[index]? = some current ∧
      AdapterPublicWrapperState.Beacon view setup.joint (RegistrationNativeBundleTerminal.after index owner finished.pending scalar during).pool
        {self with state := .InitSent finished.pending prekey oneTime kem} current
        (RegistrationNativeBundleTerminal.after index owner finished.pending scalar during).server.world.world.1.owners[current.worldOwner]? := by
  have ready := RegistrationNativeBundleLifetime.fresh_ready setup view self owner before related control prekey kem stored phase
  have kept := fresh_snapshot coins setup checks representation created writer index owner before previous (((scalar, .ok (.Ok finished)), during), next) reached
  have owners : during.server.world.world.1.owners = before.server.world.world.1.owners := congrArg Prod.fst kept
  have terminalReady : RegistrationNativeBundleTerminal.Ready during.server.world.world.1 owner.worldOwner := by
    simpa only [RegistrationNativeBundleTerminal.Ready, owners] using ready
  have actual : ((.ok (some (TranscriptAuthParts.absSlice finished.encoded)), RegistrationNativeBundleTerminal.after index owner finished.pending scalar during), next) ∈ support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run before).run previous) := by
    rw [RegistrationNativeBundleLifetime.fresh coins setup checks representation created writer index owner before previous selected phase ready, support_map]
    exact ⟨(((scalar, .ok (.Ok finished)), during), next), reached, rfl⟩
  have fields := RegistrationNativePlatformBundleMetadata.native_bundle coins setup checks representation created source writer index before
    (RegistrationNativeBundleTerminal.after index owner finished.pending scalar during) previous next (.ok (some (TranscriptAuthParts.absSlice finished.encoded))) actual
  have data := related.phase
  simp only [AdapterPublicWrapperState.Phase, stored, phase] at data
  have identifier : AdapterPublicWrapperState.currentId owner = owner.pin.binding.identity_key_id := by
    simp only [AdapterPublicWrapperState.currentId, phase]
  exact pending_material view setup.joint index self owner before during related selected identifier prekey oneTime kem scalar finished fields
    data.2.1 privateView data.2.2.1 (congrArg Prod.snd kept) terminalReady


omit material ed in
theorem failed_fields (index : Nat) (owner : Owner source) (before during : Native) (previous next : Platform)
    (selected : before.beacons[index]? = some owner)
    (reached : ((.ok none, during), next) ∈ support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run before).run previous)) :
    ∃ current, during.beacons[index]? = some current ∧ current.phase = owner.phase ∧ metadata current = metadata owner := by
  have fields := RegistrationNativePlatformBundleMetadata.native_bundle coins setup checks representation created source writer index before during previous next (.ok none) reached
  have shape := RegistrationNativePlatformBundlePhases.native_shape coins setup checks representation created writer index before previous ((.ok none, during), next) reached
  have phases : RegistrationNativeBundlePhases.phases during.beacons = RegistrationNativeBundlePhases.phases before.beacons := by
    rcases shape with same | ⟨bytes, impossible, _same⟩
    · exact same
    · cases impossible
  have found : (during.beacons.map metadata)[index]? = some (metadata owner) := by
    rw [fields, List.getElem?_map, selected]
    rfl
  rw [List.getElem?_map] at found
  obtain ⟨current, currentFound, currentFields⟩ := Option.map_eq_some_iff.mp found
  refine ⟨current, currentFound, ?_, currentFields⟩
  have actual := congrArg (fun values => values[index]?) phases
  simpa only [RegistrationNativeBundlePhases.phases, List.getElem?_map, currentFound, selected,
    Option.map_some, Option.some.injEq] using actual

private theorem unchanged_material (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner current : Owner source) (before during : Native)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (fields : metadata current = metadata owner) (phase : current.phase = owner.phase)
    (kept : RegistrationNativeBundleSafety.Snapshot during = RegistrationNativeBundleSafety.Snapshot before) :
    AdapterPublicWrapperState.Beacon view setup.joint during.pool self current during.server.world.world.1.owners[current.worldOwner]? := by
  have worldOwner : current.worldOwner = owner.worldOwner := congrArg (fun value => value.worldOwner) fields
  have owners : during.server.world.world.1.owners = before.server.world.world.1.owners := congrArg Prod.fst kept
  have pool : during.pool = before.pool := congrArg Prod.snd kept
  rw [worldOwner, owners, pool]
  exact AdapterPublicBundleMaterialLifetime.unchanged view setup.joint before.pool self owner current _ related fields phase

theorem with_coins_failed (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (index : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source) (before during : Native)
    (previous next : Platform)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (selected : before.beacons[index]? = some owner)
    (control failed : pqxdh.BeaconFresh) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (scalar : PqxdhJointGapDh.ScalarBytes) (stored : self.state = .FreshWithCoins control prekey oneTime kem)
    (phase : owner.phase = .freshWithCoins scalar)
    (reached : ((.ok (.Err failed), during), next) ∈ support
      (((RegistrationNativeBundleLifetime.tree coins setup checks representation created writer index owner scalar).run before).run previous)) :
    ∃ current, during.beacons[index]? = some current ∧
      AdapterPublicWrapperState.Beacon view setup.joint during.pool self current during.server.world.world.1.owners[current.worldOwner]? := by
  have ready := RegistrationNativeBundleLifetime.with_coins_ready setup view self owner before related control prekey oneTime kem scalar stored phase
  have actual : ((.ok none, during), next) ∈ support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run before).run previous) := by
    rw [RegistrationNativeBundleLifetime.with_coins coins setup checks representation created writer index owner scalar before previous selected phase ready, support_map]
    exact ⟨((.ok (.Err failed), during), next), reached, rfl⟩
  obtain ⟨current, found, samePhase, fields⟩ := failed_fields coins setup checks representation created writer index owner before during previous next selected actual
  have kept := RegistrationNativeBundleSafety.interpreted_snapshot coins setup checks representation created writer _
    (RegistrationNativeBundleSafety.publication_safe setup index owner scalar) before previous ((.ok (.Err failed), during), next) reached
  exact ⟨current, found, unchanged_material setup view self owner current before during related fields samePhase kept⟩

theorem fresh_failed (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (index : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source) (before during : Native)
    (previous next : Platform)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (selected : before.beacons[index]? = some owner)
    (control failed : pqxdh.BeaconFresh) (prekey : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (scalar : PqxdhJointGapDh.ScalarBytes) (stored : self.state = .Fresh control prekey kem) (phase : owner.phase = .fresh)
    (reached : (((scalar, .ok (.Err failed)), during), next) ∈ support
      (((RegistrationNativeBundleLifetime.fresh_tree coins setup checks representation created writer index owner).run before).run previous)) :
    ∃ current, during.beacons[index]? = some current ∧
      AdapterPublicWrapperState.Beacon view setup.joint during.pool self current during.server.world.world.1.owners[current.worldOwner]? := by
  have ready := RegistrationNativeBundleLifetime.fresh_ready setup view self owner before related control prekey kem stored phase
  have actual : ((.ok none, during), next) ∈ support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run before).run previous) := by
    rw [RegistrationNativeBundleLifetime.fresh coins setup checks representation created writer index owner before previous selected phase ready, support_map]
    exact ⟨(((scalar, .ok (.Err failed)), during), next), reached, rfl⟩
  obtain ⟨current, found, samePhase, fields⟩ := failed_fields coins setup checks representation created writer index owner before during previous next selected actual
  have kept := fresh_snapshot coins setup checks representation created writer index owner before previous (((scalar, .ok (.Err failed)), during), next) reached
  exact ⟨current, found, unchanged_material setup view self owner current before during related fields samePhase kept⟩


def MaterialResult (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (joint : PqxdhJointIdentity.Primitives) (index : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (owner : Owner source) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (scalar : PqxdhJointGapDh.ScalarBytes) (published : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) (during : Native) : Prop :=
  match published with
  | .fail _ | .div => True
  | .ok (.Err _) => ∃ current, during.beacons[index]? = some current ∧
      AdapterPublicWrapperState.Beacon view joint during.pool self current during.server.world.world.1.owners[current.worldOwner]?
  | .ok (.Ok finished) => ∃ current,
      (RegistrationNativeBundleTerminal.after index owner finished.pending scalar during).beacons[index]? = some current ∧
      AdapterPublicWrapperState.Beacon view joint (RegistrationNativeBundleTerminal.after index owner finished.pending scalar during).pool
        {self with state := .InitSent finished.pending prekey oneTime kem} current
        (RegistrationNativeBundleTerminal.after index owner finished.pending scalar during).server.world.world.1.owners[current.worldOwner]?

end BeaconcryptCore.Refinement.AdapterPublicBundleReached

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleReached.pending_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleReached.pending_fields

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleReached.pending_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleReached.pending_material

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleReached.with_coins_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleReached.with_coins_material

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleReached.fresh_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleReached.fresh_snapshot

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleReached.fresh_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleReached.fresh_material

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleReached.failed_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleReached.failed_fields

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleReached.with_coins_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleReached.with_coins_failed

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleReached.fresh_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleReached.fresh_failed
