-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentNative

/-! Dynamic ordinary-record state with the exact existing Server and Beacon source programs. The primitive interpreter is a parameter and keeps one shared cache and auxiliary state. The native specialization has exact put-back equations, retaining every omitted registration field. This module supplies no hidden-slot interpreter, initialization, candidate receive, freshness or security theorem. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftRoles
open PqxdhServerAuthExperiment
open PqxdhDeploymentInterface (FrameTag)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Auxiliary Reader Response : Type}

/-- The dynamic source objects, raw-attempt ghosts, produced frames and complete shared primitive state. Whole owner values retain inactive source fields; no finite role index is imposed. -/
structure State (KemSK Auxiliary : Type) where
  server : RawCtxServerRouting.State Unit Unit
  owners : List (PqxdhRegistrationSchedule.Owner KemSK)
  ownerRaw : Nat → Nat
  produced : List (FrameTag × RawCtxReceive.DecodedFrame)
  primitive : RawCtxSharedPrimitive.SharedState Auxiliary

/-- Forget only the native fields untouched by ordinary record commands. -/
def project (state : PqxdhDeploymentNative.State KemSK) : State KemSK Unit :=
  ⟨PqxdhDeploymentNative.serverView state, state.native.owners, state.ownerRaw, state.produced,
    ((), state.native.shared.2.ctx)⟩

/-- Reinstall record fields while retaining the original registration state, Extract cache, pending tokens, consumed IDs, control, Server key ID and other native fields. -/
def putback (state : PqxdhDeploymentNative.State KemSK) (records : State KemSK Unit) :
    PqxdhDeploymentNative.State KemSK :=
  { state with
    native := { state.native with
      shared := (state.native.shared.1, { state.native.shared.2 with
        ctx := records.primitive.2
        server := { state.native.shared.2.server with server := records.server.server } })
      owners := records.owners }
    serverRaw := records.server.rawAttempts
    ownerRaw := records.ownerRaw
    produced := records.produced }

/-- Append exactly the native frame-log update on the projected produced field. -/
def produce (tag : FrameTag) (frames : List RawCtxReceive.DecodedFrame)
    (state : State KemSK Auxiliary) : State KemSK Auxiliary :=
  { state with produced := state.produced ++ frames.map fun frame => (tag, frame) }

/-- Projecting and putting back an unchanged native record state is the identity. -/
theorem putback_project (state : PqxdhDeploymentNative.State KemSK) :
    putback state (project state) = state := rfl

/-- The projected coordinates are exactly the coordinates reinstalled by put-back. -/
theorem project_putback (state : PqxdhDeploymentNative.State KemSK) (records : State KemSK Unit) :
    project (putback state records) = records := rfl

/-- A later put-back replaces only record coordinates, preserving the original omitted fields. -/
theorem putback_putback (state : PqxdhDeploymentNative.State KemSK) (first second : State KemSK Unit) :
    putback (putback state first) second = putback state second := rfl

/-- The projected production update is precisely the existing native production update. -/
theorem putback_produce (state : PqxdhDeploymentNative.State KemSK) (records : State KemSK Unit)
    (tag : FrameTag) (frames : List RawCtxReceive.DecodedFrame) :
    putback state (produce tag frames records) = PqxdhDeploymentNative.produce tag frames (putback state records) := rfl

/-- The Server sender ID is not a mutable record coordinate. -/
theorem putback_sender (state : PqxdhDeploymentNative.State KemSK) (records : State KemSK Unit) :
    (putback state records).native.shared.2.server.identityKeyId = state.native.shared.2.server.identityKeyId := rfl

/-- Every native coordinate omitted from the record state is retained verbatim by put-back. -/
theorem putback_fields (state : PqxdhDeploymentNative.State KemSK) (records : State KemSK Unit) :
    let result := putback state records
    result.native.shared.1 = state.native.shared.1 ∧
      result.native.shared.2.server.identityKeyId = state.native.shared.2.server.identityKeyId ∧
      result.native.shared.2.server.control = state.native.shared.2.server.control ∧
      result.native.shared.2.server.consumed = state.native.shared.2.server.consumed ∧
      result.native.shared.2.pending = state.native.shared.2.pending ∧
      result.native.shared.2.beacon = state.native.shared.2.beacon ∧
      result.native.shared.2.sessions = state.native.shared.2.sessions ∧
      result.native.shared.2.ghost = state.native.shared.2.ghost :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The existing complete Server source operation with its exact logging wrapper and a shared primitive interpreter. -/
noncomputable def serverStep
    (primitive : QueryImpl RawCtxMixedOwner.NativeSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (sender : Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) :
    StateT (State KemSK Auxiliary) ProbComp (RawCtxServerMixed.SourceSpec.Range query) := fun state => do
  let result ← (simulateQ primitive (PqxdhDeploymentNative.logged
    ((RawCtxServerMixed.serverImpl (fun _ => sender) route decode query).run state.server))).run state.primitive
  pure (result.1.1.1, produce (PqxdhDeploymentNative.serverTag query) result.1.2
    { state with server := result.1.1.2, primitive := result.2 })

/-- The existing complete Beacon source operation at a dynamic list index, including absent-owner rejection and exact produced-frame logging. -/
noncomputable def beaconStep
    (primitive : QueryImpl RawCtxMixedOwner.NativeSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (index : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain) :
    StateT (State KemSK Auxiliary) ProbComp (RawCtxMixedOwner.SourceSpec.Range query) := fun state =>
  match state.owners[index]? with
  | none => pure (PqxdhDeploymentNative.absent query, state)
  | some owner => do
      let result ← (simulateQ primitive (PqxdhDeploymentNative.logged
        ((RawCtxBeaconLifecycle.beaconImpl decode query).run ⟨owner.beacon, state.ownerRaw index⟩))).run state.primitive
      pure (result.1.1.1, produce (PqxdhDeploymentNative.beaconTag index) result.1.2
        { state with
          owners := state.owners.set index { owner with beacon := result.1.1.2.beacon }
          ownerRaw := Function.update state.ownerRaw index result.1.1.2.rawAttempts
          primitive := result.2 })

/-- A Beacon query retains its dynamic owner index and the existing source reply type. -/
abbrev OwnerSpec : OracleSpec (Nat × RawCtxMixedOwner.SourceSpec.Domain) :=
  fun query => RawCtxMixedOwner.SourceSpec.Range query.2

/-- Both source record interfaces, with dynamic Server routing and dynamic owner addressing. -/
abbrev Spec := RawCtxServerMixed.SourceSpec + OwnerSpec

/-- Adaptive ordinary records share the same source objects, counters, production log and primitive state. -/
noncomputable def handler
    (primitive : QueryImpl RawCtxMixedOwner.NativeSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (sender : Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl Spec (StateT (State KemSK Auxiliary) ProbComp)
  | .inl query => serverStep primitive sender route decode query
  | .inr (index, query) => beaconStep primitive decode index query

/-- The same ordinary-record sum interpreted by the unchanged native deployment steps. -/
noncomputable def nativeHandler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl Spec (StateT (PqxdhDeploymentNative.State KemSK) ProbComp)
  | .inl query => PqxdhDeploymentNative.serverStep setup codec route query
  | .inr (index, query) => PqxdhDeploymentNative.beaconStep setup codec index query

/-- Reinstalling the projected Server step is exactly the complete native Server step, including every original non-record field. -/
theorem server_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : PqxdhDeploymentNative.State KemSK) :
    (fun result => (result.1, putback state result.2)) <$>
      (serverStep (PqxdhDeploymentNative.primitives setup codec)
        state.native.shared.2.server.identityKeyId route codec.frameRead query).run (project state) =
      (PqxdhDeploymentNative.serverStep setup codec route query).run state := by
  unfold PqxdhDeploymentNative.serverStep
  simp only [PqxdhDeploymentNative.record_run]
  simp only [serverStep, StateT.run, bind_pure_comp, Functor.map_map, putback, project, produce,
    PqxdhDeploymentNative.produce, PqxdhDeploymentNative.withServer,
    PqxdhDeploymentNative.serverView]
  rfl

/-- Reinstalling the projected Beacon step is exactly the complete native Beacon step, including missing and inactive owners and all retained registration fields. -/
theorem beacon_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : PqxdhDeploymentNative.State KemSK) :
    (fun result => (result.1, putback state result.2)) <$>
      (beaconStep (PqxdhDeploymentNative.primitives setup codec) codec.frameRead index query).run (project state) =
      (PqxdhDeploymentNative.beaconStep setup codec index query).run state := by
  unfold beaconStep PqxdhDeploymentNative.beaconStep
  simp only [PqxdhDeploymentNative.record_run]
  cases found : state.native.owners[index]? <;>
    simp only [project, StateT.run, found, map_pure, bind_pure_comp, Functor.map_map,
      putback, produce, PqxdhDeploymentNative.produce, PqxdhDeploymentNative.serverView]

/-- Each command of the dynamic sum preserves the complete native result after putting record state back. -/
theorem handler_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : Spec.Domain)
    (state : PqxdhDeploymentNative.State KemSK) :
    (fun result => (result.1, putback state result.2)) <$>
      (handler (PqxdhDeploymentNative.primitives setup codec)
        state.native.shared.2.server.identityKeyId route codec.frameRead query).run (project state) =
      (nativeHandler setup codec route query).run state := by
  cases query with
  | inl query => exact server_native setup codec route query state
  | inr query => exact beacon_native setup codec query.1 query.2 state

/-- One command works under any prior projected record state, retaining the same omitted native fields. -/
theorem handler_putback (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : Spec.Domain)
    (state : PqxdhDeploymentNative.State KemSK) (records : State KemSK Unit) :
    (fun result => (result.1, putback state result.2)) <$>
      (handler (PqxdhDeploymentNative.primitives setup codec)
        state.native.shared.2.server.identityKeyId route codec.frameRead query).run records =
      (nativeHandler setup codec route query).run (putback state records) := by
  simpa only [project_putback, putback_putback, putback_sender] using
    handler_native setup codec route query (putback state records)

/-- Every adaptive ordinary-record schedule has exactly the native replies and final state after put-back. The schedule may alternate both directions and dynamically choose every peer ID and owner index. -/
theorem schedule_native {X : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp Spec X)
    (state : PqxdhDeploymentNative.State KemSK) :
    (fun result => (result.1, putback state result.2)) <$>
      (simulateQ (handler (PqxdhDeploymentNative.primitives setup codec)
        state.native.shared.2.server.identityKeyId route codec.frameRead) work).run (project state) =
      (simulateQ (nativeHandler setup codec route) work).run state := by
  simpa only [putback_project, Prod.map_def, id_eq] using
    map_run_simulateQ_eq_of_query_map_eq
      (handler (PqxdhDeploymentNative.primitives setup codec)
        state.native.shared.2.server.identityKeyId route codec.frameRead)
      (nativeHandler setup codec route) (putback state)
      (fun query records => handler_putback setup codec route query state records) work (project state)

end BeaconcryptCore.Computational.PqxdhRecordLiftRoles

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRoles.putback_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRoles.putback_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRoles.project_putback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRoles.project_putback

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRoles.putback_putback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRoles.putback_putback

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRoles.putback_produce' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRoles.putback_produce

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRoles.putback_sender' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRoles.putback_sender

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRoles.putback_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRoles.putback_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRoles.server_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRoles.server_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRoles.beacon_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRoles.beacon_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRoles.handler_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRoles.handler_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRoles.handler_putback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRoles.handler_putback

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRoles.schedule_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRoles.schedule_native
