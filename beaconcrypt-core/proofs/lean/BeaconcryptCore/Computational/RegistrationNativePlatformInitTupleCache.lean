-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInitWriterFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicationReplay
import BeaconcryptCore.Computational.RegistrationNativePlatformRawFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
import BeaconcryptCore.Computational.RegistrationNativeInitTupleCache

/-! The actual effectful source Init publication retains its original tagged tuple and exact unsigned preimage/digest in the same final cache. The terminal writer is retained at its actual reached cut; no static wire encoder or completed partner premise is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInitTupleCache
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner M)
open RegistrationNativeMldsaShared (Local lower project)
open RegistrationNativePlatformSourceSealTrace (joint)
variable {n : Nat} {E Platform Value Next ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem joint_pure {S : Type} (value : Value) :
    joint (pure value : StateT S (StateT Platform ProbComp) Value) = pure value := by
  funext before
  simp only [joint, StateT.run_pure, map_pure]
  rfl
private theorem joint_bind {S : Type} (work : StateT S (StateT Platform ProbComp) Value)
    (next : Value → StateT S (StateT Platform ProbComp) Next) :
    joint (work >>= next) = (joint work >>= fun value => joint (next value)) := by
  funext before
  simp only [joint, StateT.run, StateT.monad_bind_def, StateT.bind, map_bind, bind_map_left]
private theorem joint_hom {S : Type} :
    Cslib.IsMonadHom (StateT S (StateT Platform ProbComp)) (StateT (S × Platform) ProbComp) joint :=
  .mk' joint_pure joint_bind
private theorem joint_simulate {I S : Type} {spec : OracleSpec I}
    (impl : QueryImpl spec (StateT S (StateT Platform ProbComp))) (work : OracleComp spec Value) :
    joint (simulateQ impl work) = simulateQ (fun query => joint (impl query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, joint_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, joint_bind, ih]

private theorem lower_simulate {I : Type} {spec : OracleSpec I}
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (impl : QueryImpl spec (M n KemSK source RegistrationServerRoleBackend.State)) (work : OracleComp spec Value) :
    lower setup checks representation created (simulateQ impl work) =
      simulateQ (fun query => lower setup checks representation created (impl query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, RegistrationNativeResponseAuthentication.lower_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeResponseAuthentication.lower_bind, ih]

private theorem native_program {I : Type} {spec : OracleSpec I}
    (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (impl : QueryImpl spec (M n KemSK source RegistrationServerRoleBackend.State)) (work : OracleComp spec Value)
    (before after : Local n KemSK source) (previous next : Platform) (value : Value)
    (supported : ((value, after), next) ∈ support (((simulateQ (fun query => RegistrationNativePlatformBundleLower.native coins setup checks
      representation created (impl query)) work).run before).run previous)) :
    (value, after) ∈ support ((lower setup checks representation created (simulateQ impl work)).run before) := by
  let nativeImpl : QueryImpl spec (StateT (Local n KemSK source) ProbComp) := fun query => lower setup checks representation created (impl query)
  change ((value, after), next) ∈ support (((simulateQ
    (fun query => RegistrationNativePlatformInterpret.state coins (nativeImpl query)) work).run before).run previous) at supported
  rw [← RegistrationNativePlatformInterpret.state_simulate] at supported
  have actual : (value, after) ∈ support ((simulateQ nativeImpl work).run before) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous next supported
  rw [lower_simulate]
  exact actual

noncomputable def program (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    StateT (Local n KemSK source) (StateT Platform ProbComp) (RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) :=
  RegistrationNativePlatformBeaconPublication.begin
    (fun query => RegistrationNativePlatformBundleLower.native coins setup checks representation created
      (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
    (RegistrationNativePlatformInitWriterFrame.encoder writer) ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
    ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin


/-- Literal effectful source success derives the complete original public tuple, exact pending digest and cached unsigned preimage at the actual source final state. -/
theorem outgoing (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (published : registration.PublishedBeaconInit (alloc.vec.Vec U8)) (before after : Local n KemSK source) (previous next : Platform)
    (supported : ((.ok (.Ok published), after), next) ∈ support
      (((program (n := n) coins setup checks representation created writer index owner oneTime).run before).run previous)) :
    ∃ started pending hashing atHash digest, ∃ signedView : registration.InitView,
      ∃ encodedView : registration.InitView, ∃ atWriter : Platform,
      pqxdh.beacon_start ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ = .ok started ∧
      pqxdh.validate_init_kex started.message = .ok (.Ok {
        beacon_identity_public_key := PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519,
        beacon_prekey_public_key := owner.prekeyPublic,
        beacon_one_time_public_key := PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime),
        beacon_pq_public_key := RegistrationNativeBeaconFrontend.pqArray owner.kemPublic }) ∧
      RegistrationNativeInitTupleSource.EdLead (RegistrationNativeMldsaShared.implementation setup owner)
        pending (project before) hashing atHash ∧
      RegistrationNativeInitTupleSource.Fixed started owner.pin
        (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519) hashing.state ∧
      RegistrationNativeInitTupleSource.Attached started hashing.state ∧
      RegistrationNativeInitTupleSource.HashCut (RegistrationNativeMldsaShared.implementation setup owner)
        (fun _ => .Some published.encoded) hashing atHash published (project after) ∧
      (project after).2 ((), (RegistrationNativeInitStageContents.sourcePayload hashing.state).transcript) = some digest ∧
      published.pending.binding.init_hash = RegistrationAuthenticationShared.digestArray digest ∧
      published.pending.control = hashing.state.started.state ∧ published.pending.binding.server_pin = hashing.state.server_pin ∧
      published.pending.binding.init_fields.identity_key = hashing.state.started.message.identity_key ∧
      signedView.fields = RegistrationSigningContinuations.retainedFields hashing.state ∧
      published.pending.binding.init_fields = RegistrationNativeInitTupleSource.ownedFields hashing.state ∧
      ((.ok (some published.encoded), after), next) ∈ support
        (((RegistrationNativePlatformInitWriterFrame.encoder writer encodedView).run after).run atWriter) := by
  let impl : QueryImpl RegistrationBeaconInitExecutor.Spec (StateT (Local n KemSK source) (StateT Platform ProbComp)) := fun query =>
    RegistrationNativePlatformBundleLower.native coins setup checks representation created
      (RegistrationNativeBeaconFrontend.outgoing setup source index owner query)
  have member := (RegistrationNativePlatformRawFrame.joint_support
    (program (n := n) coins setup checks representation created writer index owner oneTime) (.ok (.Ok published) : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) before after previous next).mpr supported
  unfold program at member
  rw [RegistrationNativePlatformBeaconMap.begin joint_hom] at member
  obtain ⟨atEncoder, replay, encodedView, encoded⟩ := RegistrationNativePlatformPublicationReplay.begin_replay
    (fun query => joint (impl query)) (fun view => joint (RegistrationNativePlatformInitWriterFrame.encoder writer view))
      ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin published
      (before, previous) (after, next) member
  rw [← joint_simulate] at replay
  have nested := (RegistrationNativePlatformRawFrame.joint_support _ (.ok (.Ok published) : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) before atEncoder.1 previous atEncoder.2).mp replay
  have native := native_program coins setup checks representation created
    (RegistrationNativeBeaconFrontend.outgoing setup source index owner)
    (RegistrationBeaconInitExecutor.begin (fun _ => .Some published.encoded) ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin)
    before atEncoder.1 previous atEncoder.2 (.ok (.Ok published)) nested
  have writerSupport := (RegistrationNativePlatformRawFrame.joint_support _ (.ok (some published.encoded) : RustM (Option (alloc.vec.Vec U8))) atEncoder.1 after atEncoder.2 next).mp encoded
  have framed := writerSupport
  rw [RegistrationNativePlatformInitWriterFrame.encoder_frame] at framed
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at framed
  obtain ⟨raw, _called, same⟩ := framed
  have afterEq : after = atEncoder.1 := (congrArg (fun result => result.1.2) same).symm
  have projected : (.ok (.Ok published), project atEncoder.1) ∈ support
      ((simulateQ (RegistrationNativeMldsaShared.implementation setup owner)
        (RegistrationBeaconInitExecutor.begin (fun _ => .Some published.encoded) ⟨owner.pin.binding⟩
          (RegistrationNativeBeaconFrontend.inputs setup owner) ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩
          owner.pin)).run (project before)) := by
    rw [← RegistrationNativeMldsaShared.program setup checks representation created index owner _ before, support_map]
    exact ⟨(.ok (.Ok published), atEncoder.1), native, rfl⟩
  rw [← afterEq] at projected
  obtain ⟨started, pending, hashing, atHash, began, validated, _requested, leading, fixed, attached, cut⟩ :=
    RegistrationNativeInitTupleSource.begin_receipt (RegistrationNativeMldsaShared.implementation setup owner) (fun _ => .Some published.encoded)
      ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin published
      (project before) (project after) projected
  obtain ⟨digest, signedView, cached, initHash, control, pin, identity, _encode, fields, retained⟩ :=
    RegistrationNativeInitTupleCache.hash_cached setup owner (fun _ => .Some published.encoded) hashing atHash published (project after) cut
  refine ⟨started, pending, hashing, atHash, digest, signedView, encodedView, atEncoder.2,
    began, validated, leading, fixed, attached, cut, cached, initHash, control, pin, identity, fields, retained, ?_⟩
  simpa only [afterEq] using writerSupport

end BeaconcryptCore.Computational.RegistrationNativePlatformInitTupleCache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInitTupleCache.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInitTupleCache.outgoing
