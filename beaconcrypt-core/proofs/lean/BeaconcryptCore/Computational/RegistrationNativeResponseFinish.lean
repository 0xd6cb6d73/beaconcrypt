-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeResponseAuthentication

/-! Successful original Beacon completion contains its mandatory pinned-response verification cut and the actual supported continuation to its returned plaintext. The terminal owner is consumed before authentication, with every failure retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeResponseFinish
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (BeaconShell)
open RegistrationNativeBeaconFrontend
open RegistrationNativeMldsaShared (Local lower project)
open RegistrationNativeResponseAuthentication (lower_bind lower_pure)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

noncomputable def afterAuthentication (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (accepted : registration.AuthenticatedResponse) :
    M n KemSK source RegistrationServerRoleBackend.State (RustM (Option Pqxdh.Bytes)) := do
  let agreed ← simulateQ (agreement setup owner oneTime) (RegistrationAgreementExecutor.beacon accepted)
  match agreed with
  | .fail error => abort owner *> pure (.fail error)
  | .div => abort owner *> pure .div
  | .ok (.BeaconComplete completed) => do
    let opened ← simulateQ (record setup wire) (RegistrationBeaconRecordExecutor.begin completed)
    match opened with
    | .fail error => abort owner *> pure (.fail error)
    | .div => abort owner *> pure .div
    | .ok (.Err _) => abort owner *> pure (.ok none)
    | .ok (.Ok established) => do
      let shell : BeaconShell := ⟨owner.pin.binding.identity_key_id, established.control, established.binding.associated_data⟩
      let installed : Bool ← effect (.inr (.installBeacon owner.worldOwner shell (.known established.kernel)))
      if installed then
        updatePhase index (.established ⟨established.control, established.binding, established.application⟩)
        pure (.ok (some (TranscriptAuthParts.absSlice established.application)))
      else abort owner *> pure (.ok none)
  | .ok _ => abort owner *> pure (.ok none)

def consumed (before : Local n KemSK source) (index : Nat) (aborted : pqxdh.BeaconAborted) : Local n KemSK source :=
  (match before.1[index]? with
    | none => before.1
    | some owner => before.1.set index { owner with phase := .aborted aborted }, before.2)

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

private theorem state_get_apply {S : Type} {m : Type → Type} [Monad m]
    (state : S) : (get : StateT S m S) state = pure (state, state) := rfl
private theorem state_modify_apply {S : Type} {m : Type → Type} [Monad m]
    (change : S → S) (state : S) : (modify change : StateT S m Unit) state = pure ((), change state) := rfl

private theorem finish_eq (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) :
    RegistrationNativeBeaconFrontend.finish (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup source wire index packet = (do
      let owners ← get
      match owners[index]? with
      | none => pure (.ok none)
      | some owner => match owner.phase with
        | .initSent pending oneTime => do
          match pending.aborted_state with
          | .fail error => pure (.fail error)
          | .div => pure .div
          | .ok aborted => do
            updatePhase index (.aborted aborted)
            let authenticated ← simulateQ (authentication setup source)
              (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some value => .Some value))
            match authenticated with
            | .fail error => abort owner *> pure (.fail error)
            | .div => abort owner *> pure .div
            | .ok (.Err _) => abort owner *> pure (.ok none)
            | .ok (.Ok accepted) => afterAuthentication setup wire index owner oneTime accepted
        | _ => pure (.ok none)) := rfl

private theorem lower_get (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (before : Local n KemSK source) :
    (lower setup checks representation created (get : M n KemSK source RegistrationServerRoleBackend.State (State source))).run before =
      pure (before.1, before) := by
  simp only [lower, StateT.run, state_get_apply, state_pure_apply, simulateQ_pure, map_pure]

private theorem lower_consume (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (before : Local n KemSK source)
    (index : Nat) (aborted : pqxdh.BeaconAborted) :
    (lower setup checks representation created (updatePhase index (.aborted aborted))).run before =
      pure ((), consumed before index aborted) := by
  simp only [lower, updatePhase, StateT.run, state_modify_apply, state_pure_apply, simulateQ_pure, map_pure, consumed]
  rfl

private theorem terminal (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK source RegistrationServerRoleBackend.State Value)
    (outcome : RustM (Option Pqxdh.Bytes)) (before after : Local n KemSK source) (application : Pqxdh.Bytes)
    (supported : (.ok (some application), after) ∈ support
      ((lower setup checks representation created (work *> pure outcome)).run before)) :
    .ok (some application) = outcome := by
  rw [seqRight_eq_bind, lower_bind] at supported
  rw [lower_pure, StateT.run_bind] at supported
  simp only [StateT.run_pure, bind_pure_comp, support_map] at supported
  obtain ⟨result, _possible, same⟩ := supported
  exact (congrArg Prod.fst same).symm

attribute [local irreducible] afterAuthentication authentication RegistrationResponseExecutor.begin abort

/-- Successful actual completion has a same-run accepted response cut and the literal continuation to its original returned plaintext. -/
theorem cut (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) (before after : Local n KemSK source)
    (application : Pqxdh.Bytes)
    (supported : (.ok (some application), after) ∈ support
      ((lower setup checks representation created
        (RegistrationNativeBeaconFrontend.finish setup source wire index packet)).run before)) :
    ∃ owner pending oneTime aborted accepted middle,
      before.1[index]? = some owner ∧ owner.phase = .initSent pending oneTime ∧ pending.aborted_state = .ok aborted ∧
      (.ok (.Ok accepted), middle) ∈ support
        ((lower setup checks representation created
          (simulateQ (authentication setup source)
            (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some value => .Some value)))).run
              (consumed before index aborted)) ∧
      (.ok (some application), after) ∈ support
        ((lower setup checks representation created
          (afterAuthentication setup wire index owner oneTime accepted)).run middle) := by
  rw [finish_eq, lower_bind, StateT.run_bind, lower_get, pure_bind] at supported
  cases selected : before.1[index]? with
  | none =>
      simp only [selected, lower_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
  | some owner =>
      simp only [selected] at supported
      cases phase : owner.phase with
      | fresh | freshWithCoins _ | established _ | aborted _ =>
          simp only [phase, lower_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          cases supported
      | initSent pending oneTime =>
          simp only [phase] at supported
          cases moved : pending.aborted_state with
          | fail error | div =>
              simp only [moved, lower_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
              cases supported
          | ok aborted =>
              simp only [moved, lower_bind, StateT.run_bind, lower_consume, pure_bind, mem_support_bind_iff] at supported
              obtain ⟨middle, called, continued⟩ := supported
              rcases middle with ⟨reply, middle⟩
              cases reply with
              | fail error | div =>
                  have impossible := terminal setup checks representation created (abort owner) _ middle after application continued
                  cases impossible
              | ok result => cases result with
                | Err aborted =>
                    have impossible := terminal setup checks representation created (abort owner) _ middle after application continued
                    cases impossible
                | Ok accepted => exact ⟨owner, pending, oneTime, aborted, accepted, middle, rfl, phase, moved, called, continued⟩

/-- The whole original successful finish verifies its original pending pin and actual response, and retains that exact unsigned-message hash in the returned global cache. -/
theorem final_receipt (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) (before after : Local n KemSK source)
    (application : Pqxdh.Bytes)
    (supported : (.ok (some application), after) ∈ support
      ((lower setup checks representation created
        (RegistrationNativeBeaconFrontend.finish setup source wire index packet)).run before)) :
    ∃ owner pending oneTime received digest,
      before.1[index]? = some owner ∧ owner.phase = .initSent pending oneTime ∧ packet = some received ∧
      RegistrationResponseExecutor.verification source.verify pending received digest = true ∧
      (project after).2 ((), (RegistrationResponseExecutor.payload pending received).transcript) = some digest := by
  obtain ⟨owner, pending, oneTime, aborted, authenticated, middle, selected, phase, _moved, called, continued⟩ :=
    cut setup checks representation created wire index packet before after application supported
  cases packet with
  | none =>
      rw [RegistrationResponseExecutor.begin_malformed, simulateQ_pure, lower_pure] at called
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at called
      cases called
  | some received =>
      have projected : (.ok (.Ok authenticated), project middle) ∈ support
          ((RegistrationResponseExecutor.execute setup.source.crypto source.verify wire.frameWrite
            (RawCtxSourceHkdf.kdfImpl setup.source) pending (.Some received)).run
              (project (consumed before index aborted))) := by
        rw [RegistrationResponseExecutor.execute,
          ← RegistrationNativeResponseAuthentication.program setup checks representation created wire, support_map]
        exact Set.mem_image_of_mem (Prod.map id project) called
      obtain ⟨digest, _same, verified, _receipts, _earlier, cached⟩ := RegistrationResponseExecutor.accepted_receipt
        setup.source.crypto source.verify wire.frameWrite (RawCtxSourceHkdf.kdfImpl setup.source)
        pending received (project (consumed before index aborted)) (project middle) authenticated projected
      have extension := RegistrationNativeWorldCache.localProgram setup checks representation created
        (afterAuthentication setup wire index owner oneTime authenticated) middle (.ok (some application), after) continued
      exact ⟨owner, pending, oneTime, received, digest, selected, phase, rfl, verified, extension cached⟩

/-- The original complete native finish supplies an ordinary accepted verification trial using its returned cache and literal prior global signing prefix. -/
theorem accepted (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) (before after : Local n KemSK source)
    (application : Pqxdh.Bytes)
    (supported : (.ok (some application), after) ∈ support
      ((lower setup checks representation created
        (RegistrationNativeBeaconFrontend.finish setup source wire index packet)).run before))
    (protectedKey : Bool) (honest : protectedKey = true) :
    ∃ owner pending oneTime received,
      before.1[index]? = some owner ∧ owner.phase = .initSent pending oneTime ∧ packet = some received ∧
      MldsaTranscriptAuth.Accepted (MldsaSharedAuthentication.cacheHash (project after).2) source.verify
        (RegistrationResponseExecutor.trial protectedKey pending received
          (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes pending.binding.server_pin.public_key)
            (project before))) := by
  obtain ⟨owner, pending, oneTime, received, digest, selected, phase, same, verified, cached⟩ :=
    final_receipt setup checks representation created wire index packet before after application supported
  refine ⟨owner, pending, oneTime, received, selected, phase, same, honest, ?_, ?_, ?_⟩
  · simpa only [RegistrationResponseExecutor.trial, PqxdhRefinement.absBytes, List.length_map,
      Std.UScalar.ofNatCore_val_eq] using pending.binding.server_pin.public_key.property
  · simpa only [RegistrationResponseExecutor.trial, PqxdhRefinement.absBytes, List.length_map,
      Std.UScalar.ofNatCore_val_eq] using received.signature.property
  · change source.verify (PqxdhRefinement.absBytes pending.binding.server_pin.public_key)
      Pqxdh.TranscriptAuth.signingContext (Pqxdh.TranscriptAuth.signatureInput .server
        (MldsaSharedAuthentication.cacheHash (project after).2
          (RegistrationResponseExecutor.payload pending received).transcript)) (PqxdhRefinement.absBytes received.signature) = true
    rw [MldsaSharedAuthentication.cache_hash_reconstruct _ _ digest cached]
    exact verified

private theorem source_lower (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK source RegistrationServerRoleBackend.State Value)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    (RegistrationNativeExperiment.beacon setup checks representation created work).run before =
      Prod.map id RegistrationNativeMldsaShared.close <$> (lower setup checks representation created work).run
        (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) := by
  simp only [RegistrationNativeExperiment.beacon, lower, StateT.run,
    bind_pure_comp, Functor.map_map, Prod.map, id_eq, RegistrationNativeMldsaShared.close]

/-- The original typed finish has its same source-derived verification trial, with no private-cut observer or successful-authentication premise. -/
theorem typed_accepted (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (credential : RegistrationNativeMldsa.Credential source)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (before after : RegistrationNativeExperiment.State n KemSK source) (application : Pqxdh.Bytes)
    (supported : (.ok (some application), after) ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential
        (.inr (.finish index packet))).run before)) (protectedKey : Bool) (honest : protectedKey = true) :
    ∃ owner pending oneTime received,
      before.beacons[index]? = some owner ∧ owner.phase = .initSent pending oneTime ∧ packet = some received ∧
      MldsaTranscriptAuth.Accepted
        (MldsaSharedAuthentication.cacheHash after.server.world.world.1.primitive.2) source.verify
        (RegistrationResponseExecutor.trial protectedKey pending received
          (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes pending.binding.server_pin.public_key)
            (RegistrationNativeMldsaShared.nativeProject before))) := by
  change (.ok (some application), after) ∈ support
    ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.finish setup source wire index packet)).run before) at supported
  rw [source_lower, support_map] at supported
  obtain ⟨reached, possible, same⟩ := supported
  have outcome : reached.1 = .ok (some application) := congrArg Prod.fst same
  obtain ⟨owner, pending, oneTime, received, selected, phase, packetSame, trial⟩ :=
    accepted setup checks representation created wire index packet
      (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) reached.2 application
      (outcome ▸ possible) protectedKey honest
  refine ⟨owner, pending, oneTime, received, selected, phase, packetSame, ?_⟩
  have finalCache : (project reached.2).2 = after.server.world.world.1.primitive.2 := by
    rw [← show RegistrationNativeMldsaShared.close reached.2 = after from congrArg Prod.snd same]
    rfl
  rw [finalCache] at trial
  exact trial

/-- The same returned typed success retains the concrete digest and original pending pin used by actual response verification. -/
theorem typed_receipt (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (credential : RegistrationNativeMldsa.Credential source)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (before after : RegistrationNativeExperiment.State n KemSK source) (application : Pqxdh.Bytes)
    (supported : (.ok (some application), after) ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential
        (.inr (.finish index packet))).run before)) :
    ∃ owner pending oneTime received digest,
      before.beacons[index]? = some owner ∧ owner.phase = .initSent pending oneTime ∧ packet = some received ∧
      RegistrationResponseExecutor.verification source.verify pending received digest = true ∧
      after.server.world.world.1.primitive.2 ((), (RegistrationResponseExecutor.payload pending received).transcript) = some digest := by
  change (.ok (some application), after) ∈ support
    ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.finish setup source wire index packet)).run before) at supported
  rw [source_lower, support_map] at supported
  obtain ⟨reached, possible, same⟩ := supported
  have outcome : reached.1 = .ok (some application) := congrArg Prod.fst same
  obtain ⟨owner, pending, oneTime, received, digest, selected, phase, packetSame, verified, cached⟩ :=
    final_receipt setup checks representation created wire index packet
      (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) reached.2 application
      (outcome ▸ possible)
  refine ⟨owner, pending, oneTime, received, digest, selected, phase, packetSame, verified, ?_⟩
  rw [← show RegistrationNativeMldsaShared.close reached.2 = after from congrArg Prod.snd same]
  exact cached

/-- A known pre-call pending owner gives a literal executable response trial, without selecting a private internal authentication result. -/
theorem typed_trial (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (credential : RegistrationNativeMldsa.Credential source)
    (index : Nat) (owner : Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (received : registration.ResponsePacket)
    (before after : RegistrationNativeExperiment.State n KemSK source) (application : Pqxdh.Bytes)
    (selected : before.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (supported : (.ok (some application), after) ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential
        (.inr (.finish index (some received)))).run before)) (protectedKey : Bool) (honest : protectedKey = true) :
    MldsaTranscriptAuth.Accepted
      (MldsaSharedAuthentication.cacheHash after.server.world.world.1.primitive.2) source.verify
      (RegistrationResponseExecutor.trial protectedKey pending received
        (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes pending.binding.server_pin.public_key)
          (RegistrationNativeMldsaShared.nativeProject before))) := by
  obtain ⟨other, otherPending, otherTime, otherPacket, found, reached, packet, trial⟩ :=
    typed_accepted setup checks representation created wire route credential index (some received) before after
      application supported protectedKey honest
  have ownerSame : other = owner := Option.some.inj (found.symm.trans selected)
  subst other
  have phaseSame := reached.symm.trans phase
  cases phaseSame
  cases Option.some.inj packet
  exact trial

/-- An actual original protected-key response outside the prior unsigned signing prefix yields an ordinary weak ML forgery or a reached shared-cache collision. -/
theorem typed_origin_split (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (credential : RegistrationNativeMldsa.Credential source)
    (index : Nat) (owner : Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (received : registration.ResponsePacket)
    (before after : RegistrationNativeExperiment.State n KemSK source) (application : Pqxdh.Bytes)
    (selected : before.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (supported : (.ok (some application), after) ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential
        (.inr (.finish index (some received)))).run before)) (protectedKey : Bool) (honest : protectedKey = true)
    (cached : RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject before))
    (absent : ¬ MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial protectedKey pending received
      (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes pending.binding.server_pin.public_key)
        (RegistrationNativeMldsaShared.nativeProject before)))) :
    MldsaTranscriptAuth.WeakForgery
      (MldsaSharedAuthentication.cacheHash after.server.world.world.1.primitive.2) source.verify
      (RegistrationResponseExecutor.trial protectedKey pending received
        (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes pending.binding.server_pin.public_key)
          (RegistrationNativeMldsaShared.nativeProject before))) ∨ CacheHasCollision after.server.world.world.1.primitive.2 := by
  have trial := typed_trial setup checks representation created wire route credential index owner pending oneTime received
    before after application selected phase supported protectedKey honest
  rcases MldsaTranscriptAuth.origin_failure_split _ _ _ ⟨trial, absent⟩ with forgery | collision
  · exact Or.inl forgery
  · apply Or.inr
    obtain ⟨other, otherPending, otherTime, otherPacket, digest, found, reached, packet, _verified, hashed⟩ :=
      typed_receipt setup checks representation created wire route credential index (some received) before after application supported
    have ownerSame : other = owner := Option.some.inj (found.symm.trans selected)
    subst other
    have phaseSame := reached.symm.trans phase
    cases phaseSame
    cases Option.some.inj packet
    have extension := RegistrationNativeWorldCache.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.finish setup source wire index (some received)) before
      (.ok (some application), after) supported
    apply MldsaSharedAuthentication.transcript_collision_cached _ _ ?_ ⟨digest, hashed⟩ collision
    intro call member
    obtain ⟨value, receipt⟩ := RegistrationSigningShared.history_cached _ _ cached call member
    exact ⟨value, extension receipt⟩

end BeaconcryptCore.Computational.RegistrationNativeResponseFinish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseFinish.cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseFinish.cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseFinish.final_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseFinish.final_receipt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseFinish.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseFinish.accepted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseFinish.typed_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseFinish.typed_accepted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseFinish.typed_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseFinish.typed_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseFinish.typed_trial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseFinish.typed_trial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseFinish.typed_origin_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseFinish.typed_origin_split
