-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant

/-! Admission guards may inspect a record kernel once before running the existing local compiler. These lemmas account for the read without changing the source state, preserve the compiler invariant when a kernel is cached, and show that caching the returned kernel preserves the entire merged deployment state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborAdmissionPreload
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentCompile (Kernel Local merge peerKernel ownerKernel phaseKernel mergeOwner mergePeer)
open PqxdhDeploymentCompileInvariant (Good)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

theorem owner_merge (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (index : Nat) (kernel : Kernel)
    (selected : ((merge copies native).native.owners[index]?).bind
      (fun owner => phaseKernel owner.beacon.phase) = some kernel) :
    merge { copies with owners := Function.update copies.owners index (some kernel) } native =
      merge copies native := by
  have fixed (cached : Option Kernel) (owner : PqxdhRegistrationSchedule.Owner KemSK)
      (current : phaseKernel (mergeOwner cached owner).beacon.phase = some kernel) :
      mergeOwner (some kernel) owner = mergeOwner cached owner := by
    cases phase : owner.beacon.phase <;> cases cached
    all_goals simp only [mergeOwner, phase, phaseKernel, Option.some.injEq] at current ⊢
    all_goals simp only [← current, ← phase]
  suffices owners :
      native.owners.mapIdx (fun other owner => mergeOwner
        (Function.update copies.owners index (some kernel) other) owner) =
      native.owners.mapIdx (fun other owner => mergeOwner (copies.owners other) owner) by
    simp only [merge, owners]
  apply List.ext_getElem?
  intro other
  simp only [List.getElem?_mapIdx]
  by_cases same : other = index
  case pos =>
    subst other
    cases found : native.owners[index]?
    case some owner =>
      simp only [PqxdhDeploymentCompileRecords.merge_owner, found,
        Option.map_some, Option.bind_some] at selected
      simpa only [Function.update_self, Option.map_some] using
        congrArg some (fixed (copies.owners index) owner selected)
    case none => rfl
  case neg => simp only [Function.update_of_ne same]

theorem peer_merge (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (keyId : Std.U64) (kernel : Kernel)
    (selected : ((merge copies native).native.shared.2.server.server.peers keyId).map
      RawCtxServerRouting.Peer.kernel = some kernel) :
    merge { copies with peers := Function.update copies.peers keyId (some kernel) } native =
      merge copies native := by
  have fixed (cached : Option Kernel) (peer : RawCtxServerRouting.Peer Unit)
      (current : (mergePeer cached peer).kernel = kernel) :
      mergePeer (some kernel) peer = mergePeer cached peer := by
    cases cached
    all_goals simp only [mergePeer] at current ⊢
    all_goals simp only [← current]
  suffices peers :
      (fun other => (native.shared.2.server.server.peers other).map
        (mergePeer (Function.update copies.peers keyId (some kernel) other))) =
      (fun other => (native.shared.2.server.server.peers other).map (mergePeer (copies.peers other))) by
    simp only [merge, peers]
  funext other
  rcases eq_or_ne other keyId with rfl | different
  case inl =>
    cases found : native.shared.2.server.server.peers other
    case some peer =>
      simp only [merge, found, Option.map_some, Option.some.injEq] at selected
      simpa only [Function.update_self, Option.map_some] using
        congrArg some (fixed (copies.peers other) peer selected)
    case none => rfl
  case inr => simp only [Function.update_of_ne different]

theorem peer_read_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (copies : Local)
    (native : PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec copies native)
    (keyId : Std.U64) :
    (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
      (peerKernel copies keyId)).run native =
      pure (((merge copies native).native.shared.2.server.server.peers keyId).map
        RawCtxServerRouting.Peer.kernel, native) := by
  cases cached : copies.peers keyId
  case some current =>
    obtain ⟨peer, found⟩ := Option.ne_none_iff_exists'.mp (good.installed keyId current cached)
    simp only [peerKernel, cached, simulateQ_pure, StateT.run_pure, merge, found,
      Option.map_some, mergePeer]
  case none =>
    simpa only [peerKernel, cached, merge, Option.map_map, Function.comp_def, mergePeer] using
      PqxdhDeploymentCompileRecords.reveal_run setup codec checks seed keyId native

theorem owner_read_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (copies : Local)
    (native : PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec copies native)
    (index : Nat) :
    (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
      (ownerKernel copies index)).run native =
      pure (((merge copies native).native.owners[index]?).bind
        (fun owner => phaseKernel owner.beacon.phase), native) := by
  cases cached : copies.owners index
  case some current =>
    obtain ⟨owner, control, associatedData, old, found, phase⟩ := good.copied index current cached
    simp only [ownerKernel, cached, simulateQ_pure, StateT.run_pure,
      PqxdhDeploymentCompileRecords.merge_owner, found, Option.map_some, Option.bind_some,
      mergeOwner, phase, phaseKernel]
  case none =>
    simpa only [ownerKernel, cached, PqxdhDeploymentCompileRecords.merge_owner,
      Option.bind_map, Function.comp_def, mergeOwner] using
      PqxdhDeploymentCompileRecords.kernel_run setup codec checks seed index native

theorem preload_peer_good (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (good : Good setup codec copies native) (keyId : Std.U64) (kernel : Kernel)
    (present : native.shared.2.server.server.peers keyId ≠ none) :
    Good setup codec { copies with peers := Function.update copies.peers keyId (some kernel) } native := by
  refine ⟨good.keyId, ?_, good.serverVisible, good.count, good.copied, good.owners,
    good.pending, good.accepts⟩
  intro other current cached
  rcases eq_or_ne other keyId with rfl | different
  case inl => exact present
  case inr => exact good.installed other current (by
    simpa only [Function.update_of_ne different] using cached)

theorem preload_owner_good (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (good : Good setup codec copies native) (index : Nat) (kernel : Kernel)
    (present : ∃ owner control associatedData old, native.owners[index]? = some owner ∧
      owner.beacon.phase = .established control associatedData old) :
    Good setup codec { copies with owners := Function.update copies.owners index (some kernel) } native := by
  refine ⟨good.keyId, good.installed, good.serverVisible, good.count, ?_, good.owners,
    good.pending, good.accepts⟩
  intro other current cached
  rcases eq_or_ne other index with rfl | different
  case inl => exact present
  case inr => exact good.copied other current (by
    simpa only [Function.update_of_ne different] using cached)

end BeaconcryptCore.Computational.CborAdmissionPreload

/-- info: 'BeaconcryptCore.Computational.CborAdmissionPreload.owner_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionPreload.owner_merge
/-- info: 'BeaconcryptCore.Computational.CborAdmissionPreload.peer_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionPreload.peer_merge
/-- info: 'BeaconcryptCore.Computational.CborAdmissionPreload.peer_read_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionPreload.peer_read_run
/-- info: 'BeaconcryptCore.Computational.CborAdmissionPreload.owner_read_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionPreload.owner_read_run
/-- info: 'BeaconcryptCore.Computational.CborAdmissionPreload.preload_peer_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionPreload.preload_peer_good
/-- info: 'BeaconcryptCore.Computational.CborAdmissionPreload.preload_owner_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionPreload.preload_owner_good
