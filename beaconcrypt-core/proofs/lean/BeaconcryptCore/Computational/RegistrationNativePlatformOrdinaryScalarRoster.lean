-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperiment
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetadata
import BeaconcryptCore.Computational.RegistrationNativePlatformFinishMetadata
import BeaconcryptCore.Computational.RegistrationNativeScalarRoster
/-! The actual corrected shared-platform runtime changes owner count only at successful source creation. Dynamic Init/response and ordinary writers, assigned-ID finish, reservation refusal and all other callbacks preserve the literal roster length. These are source receipts for eager selected-scalar sampling, independent of key uniqueness or protocol success. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarRoster
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeExperiment (State)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {Platform E Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private def responseBytes (result : RustM (Option (U64 × alloc.vec.Vec U8))) : RustM (Option (U64 × Pqxdh.Bytes)) := do
  let optional ← result
  .ok (optional.map fun value => (value.1, TranscriptAuthParts.absSlice value.2))

private theorem server_frame (work : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Value)
    (before after : State n KemSK source) (previous next : Platform) (reply : Value)
    (present : ((reply, after), next) ∈ support (((RegistrationNativePlatformExperiment.server work).run before).run previous)) :
    after.beacons = before.beacons := by
  simp only [RegistrationNativePlatformExperiment.server, StateT.run, state_map_apply, support_map] at present
  obtain ⟨inner, _called, same⟩ := present
  exact (congrArg (fun result => result.1.2.beacons) same).symm

private theorem world_frame (work : RegistrationNativePlatformOrdinaryWorld.M n Platform Value)
    (before after : State n KemSK source) (previous next : Platform) (reply : Value)
    (present : ((reply, after), next) ∈ support (((RegistrationNativePlatformOrdinaryExperiment.world work).run before).run previous)) :
    after.beacons = before.beacons := by
  simp only [RegistrationNativePlatformOrdinaryExperiment.world, StateT.run, state_map_apply, support_map] at present
  obtain ⟨inner, _called, same⟩ := present
  exact (congrArg (fun result => result.1.2.beacons) same).symm

private theorem record_frame (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (route : RawCtxServerRouting.SenderDecoder)
    (query : PqxdhRecordLiftInterface.RecordQuery) (before after : State n KemSK source) (previous next : Platform)
    (reply : (PqxdhRecordLiftInterface.RecordSpec .O).Range query)
    (present : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route query source).run before).run previous)) :
    after.beacons = before.beacons := by
  cases query with
  | inl query => exact world_frame _ before after previous next reply present
  | inr query => rcases query with ⟨index, query⟩; cases query with
    | inl plaintext =>
      simp only [RegistrationNativePlatformOrdinaryExperiment.record, StateT.run] at present
      cases found : before.beacons[index]? with
      | none =>
        simp only [found] at present
        cases present
        rfl
      | some owner =>
        simp only [found] at present
        exact world_frame _ before after previous next reply present
    | inr raw =>
      simp only [RegistrationNativePlatformOrdinaryExperiment.record, StateT.run] at present
      cases found : before.beacons[index]? with
      | none =>
        simp only [found] at present
        cases present
        rfl
      | some owner =>
        simp only [found] at present
        exact world_frame _ before after previous next reply present

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "ordinary" => RegistrationNativePlatformOrdinaryExperiment.handler (n := n) setup checks wire route representation created source credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer

/-- The actual constructor retains every failed prefix or appends exactly its one new owner. -/
theorem create_shape (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before after : State n KemSK source) (previous next : Platform) (reply : RustM (Option Nat))
    (present : ((reply, after), next) ∈ support (((ordinary (.inr (.create edPin mlPin keyId))).run before).run previous)) :
    RegistrationNativeKemBirthCreateShape.Shape before.beacons reply after.beacons := by
  exact RegistrationNativeScalarRoster.create_shape setup checks representation created edPin mlPin keyId before (reply, after)
    (RegistrationNativePlatformHashReceipt.native_support RegistrationNativePlatformMldsaProgram.coins _ _ previous next present)

attribute [local irreducible] RegistrationNativePlatformSourceAccept.accept RegistrationNativePlatformSourceSeal.build

/-- Every actual corrected non-creation callback retains the original source owner count, including dynamic writer failures. -/
theorem noncreate_length (query : TypedSpec.Domain)
    (notCreate : ∀ edPin mlPin keyId, query ≠ .inr (.create edPin mlPin keyId))
    (before after : State n KemSK source) (previous next : Platform) (reply : TypedSpec.Range query)
    (present : ((reply, after), next) ∈ support (((ordinary query).run before).run previous)) :
    after.beacons.length = before.beacons.length := by
  have old (same : ordinary query = RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins
      (RegistrationNativeExperiment.handler setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created source credential query)) :
      after.beacons.length = before.beacons.length := by
    rw [same] at present
    exact RegistrationNativeScalarRoster.noncreate_length setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      route representation created credential query notCreate before (reply, after)
      (RegistrationNativePlatformHashReceipt.native_support RegistrationNativePlatformMldsaProgram.coins _ _ previous next present)
  cases query with
  | inl coin => exact old rfl
  | inr command => cases command with
    | create edPin mlPin keyId => exact False.elim (notCreate edPin mlPin keyId rfl)
    | bundle index =>
      have metadata := RegistrationNativePlatformBundleMetadata.native_bundle RegistrationNativePlatformMldsaProgram.coins
        setup checks representation created source writer index before after previous next reply present
      simpa only [List.length_map] using congrArg List.length metadata
    | finish index packet =>
      have metadata := RegistrationNativePlatformFinishMetadata.native_metadata RegistrationNativePlatformMldsaProgram.coins
        setup checks representation created (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) index packet
        before after previous next reply present
      simpa only [List.length_map] using congrArg List.length metadata
    | accept packet =>
      change ((reply, after), next) ∈ support
        (((RegistrationNativePlatformExperiment.server
          (RegistrationNativePlatformSourceAccept.accept RegistrationNativePlatformMldsaProgram.coins setup
            (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) checks reserveRegistration
            route source.verify representation created packet)).run
          {before with parsedAccepts := before.parsedAccepts + 1}).run previous) at present
      exact congrArg List.length (server_frame
        (RegistrationNativePlatformSourceAccept.accept RegistrationNativePlatformMldsaProgram.coins setup
          (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) checks reserveRegistration
          route source.verify representation created packet)
        {before with parsedAccepts := before.parsedAccepts + 1} after previous next reply present)
    | build handle application =>
      change ((reply, after), next) ∈ support (((responseBytes <$>
        RegistrationNativePlatformExperiment.server
          (RegistrationNativePlatformSourceSeal.build RegistrationNativePlatformMldsaProgram.coins setup
            (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) view failure allocation erased reservePeer
            (RegistrationNativeMldsa.owned source credential) helper writer handle application)).run before).run previous) at present
      rw [StateT.run_map, StateT.run_map, support_map] at present
      obtain ⟨⟨⟨raw, current⟩, platform⟩, called, same⟩ := present
      have stateEq : current = after := congrArg (fun result => result.1.2) same
      cases stateEq
      have platformEq : platform = next := congrArg Prod.snd same
      cases platformEq
      exact congrArg List.length (server_frame _ before after previous next raw called)
    | serverSend keyId plaintext => exact congrArg List.length (record_frame setup wire reserveFrame route (.inl (.inl (plaintext, keyId))) before after previous next reply present)
    | serverRaw raw => exact congrArg List.length (record_frame setup wire reserveFrame route (.inl (.inr raw)) before after previous next reply present)
    | beaconSend index plaintext => exact congrArg List.length (record_frame setup wire reserveFrame route (.inr (index, .inl plaintext)) before after previous next reply present)
    | beaconRaw index raw => exact congrArg List.length (record_frame setup wire reserveFrame route (.inr (index, .inr raw)) before after previous next reply present)
    | hmac key bytes | hash bytes => exact old rfl

/-- Every actual step grows the roster by at most one and never removes an earlier owner. -/
theorem step_lengths (query : TypedSpec.Domain) (before after : State n KemSK source) (previous next : Platform)
    (reply : TypedSpec.Range query)
    (present : ((reply, after), next) ∈ support (((ordinary query).run before).run previous)) :
    before.beacons.length ≤ after.beacons.length ∧ after.beacons.length ≤ before.beacons.length + 1 := by
  by_cases createdNow : ∃ edPin mlPin keyId, query = .inr (.create edPin mlPin keyId)
  · obtain ⟨edPin, mlPin, keyId, rfl⟩ := createdNow
    have shape := create_shape setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer edPin mlPin keyId before after previous next reply present
    cases actual : reply with
    | fail error | div =>
      simp only [RegistrationNativeKemBirthCreateShape.Shape, actual] at shape
      rw [shape]
      omega
    | ok selected => cases selected with
      | none =>
        simp only [RegistrationNativeKemBirthCreateShape.Shape, actual] at shape
        rw [shape]
        omega
      | some index =>
        simp only [RegistrationNativeKemBirthCreateShape.Shape, actual] at shape
        obtain ⟨_index, owner, afterEq⟩ := shape
        rw [afterEq]
        simp only [List.length_append, List.length_singleton]
        omega
  · push Not at createdNow
    rw [noncreate_length setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query createdNow before after previous next reply present]
    omega

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarRoster

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarRoster.create_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarRoster.create_shape

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarRoster.noncreate_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarRoster.noncreate_length

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarRoster.step_lengths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarRoster.step_lengths
