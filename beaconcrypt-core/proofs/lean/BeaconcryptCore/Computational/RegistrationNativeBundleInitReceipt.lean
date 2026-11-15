-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInitTupleCache
import BeaconcryptCore.Computational.RegistrationNativeOwnerFields
import BeaconcryptCore.Computational.RegistrationNativeWorldCache

/-! A successful original native bundle selects its actual reached owner and one-time scalar, executes the original outgoing source in the same state, and stores precisely that publication's pending capability at the same owner position. Shared history and cache effects are retained through the final public lifecycle callback. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBundleInitReceipt
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner Phase M)
open RegistrationNativeMldsaShared (Local lower)
variable {n : Nat} {ι KemSK Value Next : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let middle ← work before; next middle.1 middle.2) := rfl
private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl

private theorem state_get_apply {S : Type} {m : Type → Type} [Monad m]
    (before : S) : (get : StateT S m S) before = pure (before, before) := rfl
private theorem state_modify_apply {S : Type} {m : Type → Type} [Monad m]
    (change : S → S) (before : S) : (modify change : StateT S m Unit) before = pure ((), change before) := rfl

private theorem lower_pure (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (value : Value) :
    lower (n := n) (source := source) setup checks representation created (pure value) = pure value := by
  apply StateT.ext
  intro before
  simp only [lower, StateT.run, state_pure_apply, simulateQ_pure, map_pure]

private theorem lower_bind (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK source RegistrationServerRoleBackend.State Value)
    (next : Value → M n KemSK source RegistrationServerRoleBackend.State Next) :
    lower setup checks representation created (work >>= next) =
      (lower setup checks representation created work >>= fun value => lower setup checks representation created (next value)) := by
  apply StateT.ext
  intro before
  simp only [lower, StateT.run, state_bind_apply, simulateQ_bind, map_bind, bind_map_left]

private theorem lower_get (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (before : Local n KemSK source) :
    (lower setup checks representation created (get : M n KemSK source RegistrationServerRoleBackend.State _)).run before =
      pure (before.1, before) := by
  simp only [lower, StateT.run, state_get_apply, state_pure_apply, simulateQ_pure, map_pure]

private theorem lower_modify (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (change : RegistrationNativeBeaconFrontend.State source → RegistrationNativeBeaconFrontend.State source)
    (before : Local n KemSK source) :
    (lower setup checks representation created (modify change)).run before = pure ((), (change before.1, before.2)) := by
  simp only [lower, StateT.run, state_modify_apply, state_pure_apply, simulateQ_pure, map_pure]

private theorem lower_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK source RegistrationServerRoleBackend.State Value)
    (before : Local n KemSK source) (value : Value) (after : Local n KemSK source)
    (supported : (value, after) ∈ support ((lower setup checks representation created work).run before)) :
    ((value, after.1), after.2.1) ∈ support ((work.run before.1).run before.2.1) := by
  simp only [lower, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  apply OracleComp.support_simulateQ_run'_subset
    (RegistrationNativeExperiment.trusted setup checks representation created source)
    ((work.run before.1).run before.2.1) before.2.2
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst possible

private theorem lower_sample_owners (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (draw : ProbComp Value)
    (before : Local n KemSK source) (value : Value) (after : Local n KemSK source)
    (supported : (value, after) ∈ support ((lower setup checks representation created
      (RegistrationNativeBeaconFrontend.sample draw)).run before)) : after.1 = before.1 := by
  have original := lower_source setup checks representation created (RegistrationNativeBeaconFrontend.sample draw) before value after supported
  rw [RegistrationNativeScalarSource.sample_effects] at original
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map, support_map] at original
  obtain ⟨inner, _possible, same⟩ := original
  exact (congrArg (fun result : (Value × RegistrationNativeBeaconFrontend.State source) ×
    RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State => result.1.2) same).symm

private theorem lower_effect_owners (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain)
    (before : Local n KemSK source) (value : (PqxdhRecordLiftInterface.EnvEffects n).Range query) (after : Local n KemSK source)
    (supported : (value, after) ∈ support ((lower setup checks representation created
      (RegistrationNativeBeaconFrontend.effect query)).run before)) : after.1 = before.1 := by
  have original := lower_source setup checks representation created (RegistrationNativeBeaconFrontend.effect query) before value after supported
  simp only [RegistrationNativeBeaconFrontend.effect, StateT.run_lift, bind_pure_comp, StateT.run_map,
    Functor.map_map, support_map] at original
  obtain ⟨inner, _possible, same⟩ := original
  exact (congrArg (fun result : ((PqxdhRecordLiftInterface.EnvEffects n).Range query × RegistrationNativeBeaconFrontend.State source) ×
    RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State => result.1.2) same).symm

private noncomputable def next (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM (RegistrationBeaconInitExecutor.Result Pqxdh.Bytes)) :
    M n KemSK source RegistrationServerRoleBackend.State (RustM (Option Pqxdh.Bytes)) :=
  match reply with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok published) => do
    RegistrationNativeBeaconFrontend.updatePhase index (.initSent published.pending oneTime)
    let _ ← RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent))
    pure (.ok (some published.encoded))

private noncomputable def bundled (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    M n KemSK source RegistrationServerRoleBackend.State (RustM (Option Pqxdh.Bytes)) := do
  let published ← simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source index owner)
    (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin)
  next index owner oneTime published

private theorem bundled_receipt (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (before after : Local n KemSK source) (bytes : Pqxdh.Bytes) (found : before.1[index]? = some owner)
    (supported : (.ok (some bytes), after) ∈ support
      ((lower setup checks representation created (bundled setup wire index owner oneTime)).run before)) :
    ∃ published outgoingAfter current,
      (.ok (.Ok published), outgoingAfter) ∈ support
        ((lower setup checks representation created
          (simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source index owner)
            (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
              ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin))).run before) ∧
      published.encoded = bytes ∧ outgoingAfter.1[index]? = some current ∧
      RegistrationNativeOwnerFields.metadata current = RegistrationNativeOwnerFields.metadata owner ∧
      after.1 = outgoingAfter.1.set index { current with phase := .initSent published.pending oneTime } ∧
      RegistrationNativeWorldCache.cache outgoingAfter.2.2 ≤ RegistrationNativeWorldCache.cache after.2.2 := by
  simp only [bundled, lower_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨outgoingResult, outgoingSupport, continued⟩ := supported
  cases actual : outgoingResult.1 with
  | fail error => simp [next, actual, lower_pure, StateT.run_pure] at continued
  | div => simp [next, actual, lower_pure, StateT.run_pure] at continued
  | ok result => cases result with
    | Err previous => simp [next, actual, lower_pure, StateT.run_pure] at continued
    | Ok published =>
      have sourceSupport := lower_source setup checks representation created _ before outgoingResult.1 outgoingResult.2 outgoingSupport
      have metadata := RegistrationNativeOwnerFields.outgoing_metadata setup source index owner _ before.1 before.2.1
        ((outgoingResult.1, outgoingResult.2.1), outgoingResult.2.2.1) sourceSupport
      have selected := congrArg (fun roster => roster[index]?) metadata
      simp only [List.getElem?_map, found, Option.map_some] at selected
      obtain ⟨current, currentFound, currentMetadata⟩ := Option.map_eq_some_iff.mp selected
      simp only [next, actual, lower_bind, RegistrationNativeBeaconFrontend.updatePhase, StateT.run_bind,
        lower_modify, pure_bind, currentFound, lower_pure, mem_support_bind_iff] at continued
      obtain ⟨advanced, advancedSupport, returned⟩ := continued
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at returned
      have encoded : published.encoded = bytes := (Option.some.inj (RustM.ok.inj returned.1)).symm
      have ownersSame := lower_effect_owners setup checks representation created (.inr (.advanceOwner owner.worldOwner .initSent))
        _ advanced.1 advanced.2 advancedSupport
      have cache := RegistrationNativeWorldCache.localProgram setup checks representation created
        (RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent))) _ advanced advancedSupport
      refine ⟨published, outgoingResult.2, current, ?_, encoded, currentFound, currentMetadata, ?_, ?_⟩
      · simpa only [← actual, Prod.eta] using outgoingSupport
      · exact (congrArg Prod.fst returned.2).trans ownersSame
      · exact cache.trans_eq (congrArg (fun state : Local n KemSK source => RegistrationNativeWorldCache.cache state.2.2) returned.2.symm)


def Selected (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (before during : Local n KemSK source) : Prop :=
  (owner.phase = .fresh ∧ (oneTime, during) ∈ support ((lower setup checks representation created
    (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar)).run before)) ∨
  (owner.phase = .freshWithCoins oneTime ∧ during = before)

/-- Every successful actual bundle selects its literal old owner and one-time scalar, reaches the full original outgoing source, then stores exactly that publication's pending capability at the same owner slot. -/
theorem local_receipt (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (before after : Local n KemSK source) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some bytes), after) ∈ support
      ((lower setup checks representation created (RegistrationNativeBeaconFrontend.bundle setup source wire index)).run before)) :
    ∃ owner oneTime beforeOutgoing published outgoingAfter current,
      before.1[index]? = some owner ∧ Selected setup checks representation created owner oneTime before beforeOutgoing ∧
      beforeOutgoing.1[index]? = some owner ∧
      (.ok (.Ok published), outgoingAfter) ∈ support
        ((lower setup checks representation created
          (simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source index owner)
            (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
              ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin))).run beforeOutgoing) ∧
      published.encoded = bytes ∧ outgoingAfter.1[index]? = some current ∧
      RegistrationNativeOwnerFields.metadata current = RegistrationNativeOwnerFields.metadata owner ∧
      after.1 = outgoingAfter.1.set index { current with phase := .initSent published.pending oneTime } ∧
      RegistrationNativeWorldCache.cache outgoingAfter.2.2 ≤ RegistrationNativeWorldCache.cache after.2.2 := by
  simp only [RegistrationNativeBeaconFrontend.bundle, lower_bind, StateT.run_bind, lower_get, pure_bind] at supported
  cases found : before.1[index]? with
  | none => simp [found, lower_pure, StateT.run_pure] at supported
  | some owner =>
    rw [found] at supported
    cases phase : owner.phase with
    | fresh =>
      simp only [phase] at supported
      change (.ok (some bytes), after) ∈ support ((lower setup checks representation created
        (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar >>= bundled setup wire index owner)).run before) at supported
      rw [lower_bind] at supported
      simp only [StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨sampled, sampledSupport, continued⟩ := supported
      have sameOwners := lower_sample_owners setup checks representation created PqxdhJointGapDh.sampleScalar before sampled.1 sampled.2 sampledSupport
      have selected : sampled.2.1[index]? = some owner := sameOwners ▸ found
      obtain ⟨published, outgoingAfter, current, called, encoded, currentFound, metadata, stored, cache⟩ :=
        bundled_receipt setup checks representation created wire index owner sampled.1 sampled.2 after bytes selected continued
      exact ⟨owner, sampled.1, sampled.2, published, outgoingAfter, current, rfl,
        Or.inl ⟨phase, sampledSupport⟩, selected, called, encoded, currentFound, metadata, stored, cache⟩
    | freshWithCoins oneTime =>
      simp only [phase] at supported
      change (.ok (some bytes), after) ∈ support ((lower setup checks representation created
        (bundled setup wire index owner oneTime)).run before) at supported
      obtain ⟨published, outgoingAfter, current, called, encoded, currentFound, metadata, stored, cache⟩ :=
        bundled_receipt setup checks representation created wire index owner oneTime before after bytes found supported
      exact ⟨owner, oneTime, before, published, outgoingAfter, current, rfl, Or.inr ⟨phase, rfl⟩,
        found, called, encoded, currentFound, metadata, stored, cache⟩
    | initSent pending oneTime | established completed | aborted control =>
      simp [phase, lower_pure, StateT.run_pure] at supported


/-- Private mathematical source evidence for the exact successful bundle and its stored pending owner. -/
def Receipt (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (before after : RegistrationNativeExperiment.State n KemSK source) (bytes : Pqxdh.Bytes) : Prop :=
  ∃ (owner current : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (pending : registration.BeaconPending)
    (started : pqxdh.BeaconStart) (hashing : registration.BeaconInitHash) (digest : CtxRomAuth.CtxDigest) (view : registration.InitView),
    before.beacons[index]? = some owner ∧ after.beacons[index]? = some current ∧
    current.phase = .initSent pending oneTime ∧
    RegistrationNativeOwnerFields.metadata current = RegistrationNativeOwnerFields.metadata owner ∧
    (owner.phase = .fresh ∨ owner.phase = .freshWithCoins oneTime) ∧
    pqxdh.beacon_start ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ = .ok started ∧
    pqxdh.validate_init_kex started.message = .ok (.Ok {
      beacon_identity_public_key := PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519,
      beacon_prekey_public_key := owner.prekeyPublic,
      beacon_one_time_public_key := PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime),
      beacon_pq_public_key := RegistrationNativeBeaconFrontend.pqArray owner.kemPublic }) ∧
    RegistrationNativeInitTupleSource.Fixed started owner.pin
      (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519)
      hashing.state ∧ RegistrationNativeInitTupleSource.Attached started hashing.state ∧
    RegistrationNativeWorldCache.cache after ((), (RegistrationNativeInitStageContents.sourcePayload hashing.state).transcript) = some digest ∧
    pending.control = hashing.state.started.state ∧ pending.binding.server_pin = hashing.state.server_pin ∧
    pending.binding.init_fields.identity_key = hashing.state.started.message.identity_key ∧
    pending.binding.init_hash = RegistrationAuthenticationShared.digestArray digest ∧
    wire.encodeInit view = .Some bytes ∧
    view.fields = BeaconcryptCore.Refinement.RegistrationSigningContinuations.retainedFields hashing.state ∧
    pending.binding.init_fields = RegistrationNativeInitTupleSource.ownedFields hashing.state

private theorem source_lower (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK source RegistrationServerRoleBackend.State Value)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    (RegistrationNativeExperiment.beacon setup checks representation created work).run before =
      Prod.map id RegistrationNativeMldsaShared.close <$> (lower setup checks representation created work).run
        (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) := by
  simp only [RegistrationNativeExperiment.beacon, lower, StateT.run, bind_pure_comp, Functor.map_map,
    Prod.map, id_eq, RegistrationNativeMldsaShared.close]

/-- The original typed bundle callback derives the complete raw-tuple, one-time scalar, stored InitSent and same-cache preimage receipt from its actual supported execution. -/
theorem typed_receipt (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (index : Nat) (before after : RegistrationNativeExperiment.State n KemSK source) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some bytes), after) ∈ support ((RegistrationNativeExperiment.handler setup checks wire route representation
      created source credential (.inr (.bundle index))).run before)) : Receipt setup wire index before after bytes := by
  change (.ok (some bytes), after) ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
    (RegistrationNativeBeaconFrontend.bundle setup source wire index)).run before) at supported
  rw [source_lower, support_map] at supported
  obtain ⟨localResult, localSupport, same⟩ := supported
  have valueSame : localResult.1 = .ok (some bytes) := congrArg Prod.fst same
  have stateSame : RegistrationNativeMldsaShared.close localResult.2 = after := congrArg Prod.snd same
  have possible : (.ok (some bytes), localResult.2) ∈ support ((lower setup checks representation created
      (RegistrationNativeBeaconFrontend.bundle setup source wire index)).run
        (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before))) := by
    simpa only [← valueSame, Prod.eta] using localSupport
  obtain ⟨owner, oneTime, beforeOutgoing, published, outgoingAfter, current, found, selected,
    beforeFound, outgoingSupport, encoded, currentFound, metadata, stored, extension⟩ :=
    local_receipt setup checks representation created wire index _ localResult.2 bytes possible
  obtain ⟨started, pending, hashing, atHash, digest, view, startedRun, validated, _leading, fixed, attached,
    _cut, cached, initHash, control, pin, identity, encodedView, fields, retainedFields⟩ :=
    RegistrationNativeInitTupleCache.outgoing setup checks representation created wire index owner oneTime
      published beforeOutgoing outgoingAfter outgoingSupport
  have reached : localResult.2.1[index]? = some { current with phase := .initSent published.pending oneTime } := by
    rw [stored]
    exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp currentFound).1
  have closed : after.beacons[index]? = some { current with phase := .initSent published.pending oneTime } := by
    rw [← stateSame]
    exact reached
  have retained := extension cached
  have finalCache : RegistrationNativeWorldCache.cache after
      ((), (RegistrationNativeInitStageContents.sourcePayload hashing.state).transcript) = some digest := by
    rw [← stateSame]
    exact retained
  refine ⟨owner, { current with phase := .initSent published.pending oneTime }, oneTime, published.pending,
    started, hashing, digest, view, found, closed, rfl, ?_, ?_, startedRun, validated, fixed, attached,
    finalCache, control, pin, identity, initHash, ?_, fields, retainedFields⟩
  · exact metadata
  · rcases selected with ⟨phase, _⟩ | ⟨phase, _⟩
    · exact Or.inl phase
    · exact Or.inr phase
  · simpa only [encoded] using encodedView

end BeaconcryptCore.Computational.RegistrationNativeBundleInitReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleInitReceipt.local_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleInitReceipt.local_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleInitReceipt.typed_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleInitReceipt.typed_receipt
