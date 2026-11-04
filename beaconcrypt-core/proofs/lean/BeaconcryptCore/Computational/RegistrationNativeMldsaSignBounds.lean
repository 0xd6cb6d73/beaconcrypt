-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaSignSyntax

/-! Actual free native ML capability bills. Only the complete bundle and response-build callbacks can attempt ML signing; each has one slot, including every failed optional reply, writer and installation path. Ordinary sampling and named generation have no signing slot. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds
attribute [local irreducible] RegistrationNativeExperiment.handler
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaProgram (Spec liftState)
variable {n : Nat} {ι KemSK State Value Next : Type} {base : OracleSpec ι}
variable {source : Source}

def IsSign : (Spec source).Domain → Prop
  | .inr (.sign _ _) => True
  | _ => False
instance : DecidablePred (IsSign (source := source)) := fun query => by
  rcases query with coin | call
  · exact instDecidableFalse
  · cases call <;> first | exact instDecidableFalse | exact instDecidableTrue

private def Bound (work : StateT State (OracleComp (Spec source)) Value) (count : Nat) : Prop :=
  ∀ before, (work.run before).IsQueryBoundP IsSign count

private theorem bind_bound (work : StateT State (OracleComp (Spec source)) Value)
    (next : Value → StateT State (OracleComp (Spec source)) Next) (firstCount restCount : Nat)
    (first : Bound work firstCount) (rest : ∀ value, Bound (next value) restCount) :
    Bound (work >>= next) (firstCount + restCount) := by
  intro before
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (first before) (fun result _ => rest result.1 result.2)

private theorem pure_bound (value : Value) (count : Nat) :
    Bound (pure value : StateT State (OracleComp (Spec source)) Value) count := fun _ => by trivial

private theorem ordinary (work : ProbComp Value) :
    (RegistrationNativeMldsaProgram.lift (source := source) work).IsQueryBoundP IsSign 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_of_step
  all_goals simp [RegistrationNativeMldsaProgram.ordinary, IsSign, isQueryBoundP_query_iff]

private theorem lifted (work : StateT State ProbComp Value) :
    Bound (liftState (source := source) work) 0 := fun before => ordinary (work.run before)

private theorem signed (credential : Credential source)
    (accounting : RegistrationNativeMldsaCapability.Accounting) (request : registration.MldsaSigningRequest)
    (before : PqxdhRecordLiftWorld.State n) :
    ((RegistrationNativeMldsaProgram.call accounting (.sign credential request)).run before).IsQueryBoundP IsSign 1 := by
  simp [RegistrationNativeMldsaProgram.call, StateT.run, IsSign]

namespace Server
variable (source : Source) (credential : Credential source)

theorem outgoing (query : RegistrationSigningShared.Spec.Domain) (before : RegistrationWorldSigning.State n) :
    ((RegistrationNativeMldsaServer.outgoing source credential query).run before).IsQueryBoundP IsSign
      (if RegistrationNativeMldsaSignSyntax.Server.IsSign query then 1 else 0) := by
  cases query with
  | hash request => exact lifted _ before
  | sign request payload digest =>
      simpa only [RegistrationNativeMldsaServer.outgoing, StateT.run, isQueryBoundP_map_iff,
        RegistrationNativeMldsaSignSyntax.Server.IsSign, ite_true] using
        signed credential .native request before.1

private theorem signing {Auxiliary Encoded : Type}
    (encode : registration.SignedResponseView → core.option.Option Encoded) (pending : registration.ServerResponseHash) :
    Bound (RegistrationNativeMldsaServer.signing (n := n) (Auxiliary := Auxiliary) source credential encode pending) 1 := by
  intro before
  simpa only [RegistrationNativeMldsaServer.signing, StateT.run, isQueryBoundP_map_iff] using
    (RegistrationNativeMldsaSignSyntax.Server.program encode pending).simulateQ_run_StateT_of_step
      (outgoing (n := n) source credential) before.world

private theorem publish {Auxiliary Encoded : Type}
    (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (pending : registration.ServerResponseHash) :
    Bound (RegistrationNativeMldsaServer.publish (n := n) (Auxiliary := Auxiliary) source credential encode control pending) 1 := by
  unfold RegistrationNativeMldsaServer.publish
  apply bind_bound _ _ 1 0 (signing source credential encode pending)
  intro result
  cases result with
  | fail error | div => exact pure_bound _ _
  | ok answer => cases answer with
    | Err previous => exact pure_bound _ _
    | Ok published => exact lifted _

private theorem completionFromInitial {Auxiliary Encoded Reader Response : Type}
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (pending : registration.ServerInitialKdf) :
    Bound (RegistrationNativeMldsaServer.completionFromInitial (n := n) (Auxiliary := Auxiliary)
      source credential setup codec encode control pending) 1 := by
  unfold RegistrationNativeMldsaServer.completionFromInitial
  apply bind_bound _ _ 0 1 (lifted _)
  intro result
  cases result with
  | fail error | div => exact pure_bound _ _
  | ok answer => cases answer with
    | Err previous => exact pure_bound _ _
    | Ok pending => exact publish source credential encode control pending

private theorem world (work : StateT (RegistrationServerRootCompiler.Local n)
    (OracleComp (Spec source)) Value) (count : Nat) (bounded : Bound work count) :
    Bound (RegistrationNativeMldsaServer.world source work) count := by
  intro before
  simpa only [RegistrationNativeMldsaServer.world, StateT.run, isQueryBoundP_map_iff] using bounded before.world

private theorem fromInitial {Reader Response : Type} (setup : Setup base KemSK) (codec : Codec Reader Response)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes) (control : pqxdh.ServerState)
    (pending : registration.ServerInitialKdf) :
    Bound (RegistrationNativeMldsaServer.fromInitial (n := n) source credential setup codec encode control pending) 1 := by
  unfold RegistrationNativeMldsaServer.fromInitial
  exact bind_bound _ _ 1 0
    (world source _ _ (completionFromInitial source credential setup codec encode control pending))
    (fun _ => lifted _)

private theorem afterOccupancy {Reader Response : Type} (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes) (control : pqxdh.ServerState)
    (lookup : peer.CompletionLookup) (occupied : Bool) :
    Bound (RegistrationNativeMldsaServer.afterOccupancy (n := n) source credential setup codec checks encode control lookup occupied) 1 := by
  unfold RegistrationNativeMldsaServer.afterOccupancy
  cases lookup.resume occupied with
  | fail error | div => exact pure_bound _ _
  | ok result => cases result with
    | Err previous => exact pure_bound _ _
    | Ok pending =>
        simp only
        split
        · exact fromInitial source credential setup codec encode control pending
        · exact pure_bound _ _

private theorem complete {Reader Response : Type} (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    Bound (RegistrationNativeMldsaServer.complete (n := n) source credential setup codec checks encode token application) 1 := by
  intro before
  simp only [RegistrationNativeMldsaServer.complete, StateT.run]
  cases peer.begin_completion_lookup before.control before.pin token application with
  | fail error | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok lookup =>
        simp only
        cases lookup.request with
        | fail error | div => trivial
        | ok keyId =>
            simp only
            split
            · exact isQueryBoundP_bind (world source _ 0 (lifted _) before)
                (fun result _ => afterOccupancy source credential setup codec checks encode before.control lookup result.1 result.2)
            · trivial

/-- The complete moved-handle response build has one ML signing slot on every source path. -/
theorem build {Reader Response : Type} (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes) (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationServerFrontendCompiler.State n) :
    ((RegistrationNativeMldsaServer.build source credential setup codec checks encode handle application).run before).IsQueryBoundP IsSign 1 := by
  simp only [RegistrationNativeMldsaServer.build, StateT.run]
  cases RegistrationServerSdkSource.take handle before with
  | mk found current => cases found with
    | none => trivial
    | some token => cases application with
      | none => trivial
      | some application => exact complete source credential setup codec checks encode token application current
end Server

namespace Bundle
open RegistrationNativeMldsaShared (Local)
open RegistrationNativeBeaconFrontend (Owner)
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit)

private theorem native (work : RegistrationNativeBeaconFrontend.M n KemSK source
    RegistrationServerRoleBackend.State Value) :
    Bound (RegistrationNativeMldsaBundle.native setup checks representation created work) 0 := lifted _

theorem outgoing (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) (before : Local n KemSK source) :
    ((RegistrationNativeMldsaBundle.outgoing setup checks representation created index owner query).run before).IsQueryBoundP IsSign
      (if RegistrationNativeMldsaSignSyntax.Beacon.IsSign query then 1 else 0) := by
  cases query with
  | inl query => cases query with
    | hash request => exact native setup checks representation created _ before
    | sign request payload digest =>
        simp only [RegistrationNativeMldsaBundle.outgoing, StateT.run,
          RegistrationNativeMldsaSignSyntax.Beacon.IsSign, ite_true]
        exact isQueryBoundP_bind (m := 0) (signed owner.mldsa .environment request before.2.2.server.world.world.1)
          (fun _ _ => isQueryBoundP_pure _ _ _)
  | inr request => exact native setup checks representation created _ before

private theorem afterPublished (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (published : RustM (RegistrationBeaconInitExecutor.Result Pqxdh.Bytes)) :
    Bound (RegistrationNativeMldsaBundle.afterPublished (n := n) setup checks representation created index owner oneTime published) 0 := by
  cases published with
  | fail error | div => exact pure_bound _ _
  | ok answer => cases answer with
    | Err previous => exact pure_bound _ _
    | Ok completed =>
        exact bind_bound _ _ 0 0 (native setup checks representation created _)
          (fun _ => bind_bound _ _ 0 0 (native setup checks representation created _)
            (fun _ => pure_bound _ _))

private theorem native_get (before : Local n KemSK source) :
    (RegistrationNativeMldsaBundle.native setup checks representation created get).run before = pure (before.1, before) := rfl

/-- The complete source bundle has exactly one available ML signing slot, regardless of later publication failure. -/
theorem bundle (wire : RegistrationNativeWire.Wire) (index : Nat) (before : Local n KemSK source) :
    ((RegistrationNativeMldsaBundle.bundle setup checks wire representation created index).run before).IsQueryBoundP IsSign 1 := by
  simp only [RegistrationNativeMldsaBundle.bundle, StateT.run_bind, native_get setup checks representation created, pure_bind]
  cases found : before.1[index]? with
  | none => trivial
  | some owner =>
      have continuation (oneTime : PqxdhJointGapDh.ScalarBytes) (current : Local n KemSK source) :
          ((do
            let published ← simulateQ (RegistrationNativeMldsaBundle.outgoing setup checks representation created index owner)
              (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩
                (RegistrationNativeBeaconFrontend.inputs setup owner)
                ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey)
            RegistrationNativeMldsaBundle.afterPublished setup checks representation created index owner oneTime published).run current).IsQueryBoundP IsSign 1 := by
        rw [StateT.run_bind]
        apply isQueryBoundP_bind (m := 0)
        · exact (RegistrationNativeMldsaSignSyntax.Beacon.begin_bound wire.encodeInit _ _ _ _ _).simulateQ_run_StateT_of_step
            (outgoing setup checks representation created index owner) current
        · intro result _
          exact afterPublished setup checks representation created index owner oneTime result.1 result.2
      cases phase : owner.phase <;> simp only [phase]
      all_goals first
        | trivial
        | exact continuation _ before
        | exact isQueryBoundP_bind (native setup checks representation created _ before)
            (fun result _ => continuation result.1 result.2)

/-- The native-state lens retains the bundle's literal ML signing bound. -/
theorem sourceBundle (wire : RegistrationNativeWire.Wire) (index : Nat)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    ((RegistrationNativeMldsaBundle.sourceBundle setup checks wire representation created index).run before).IsQueryBoundP IsSign 1 := by
  simpa only [RegistrationNativeMldsaBundle.sourceBundle, StateT.run, isQueryBoundP_map_iff] using
    bundle setup checks representation created wire index _
end Bundle

private theorem generated (accounting : RegistrationNativeMldsaCapability.Accounting) (before : PqxdhRecordLiftWorld.State n) :
    ((RegistrationNativeMldsaProgram.call (source := source) accounting .generate).run before).IsQueryBoundP IsSign 0 := by
  simp [RegistrationNativeMldsaProgram.call, StateT.run, IsSign]

/-- Actual create generates a key but makes no ML signing request. -/
theorem create (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    ((RegistrationNativeMldsaCreation.create setup checks representation created edPin mlPin keyId).run before).IsQueryBoundP IsSign 0 := by
  simp only [RegistrationNativeMldsaCreation.create, StateT.run_bind]
  apply isQueryBoundP_bind (n := 0) (m := 0)
  · simpa only [RegistrationNativeMldsaCreation.world, StateT.run, isQueryBoundP_map_iff] using
      generated (source := source) .environment before.server.world.world.1
  · intro middle _
    exact lifted _ middle.2

/-- Every startup outcome is ML signing-free, including constructor and generation failures. -/
theorem start (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64) :
    (RegistrationNativeMldsaCreation.start (n := n) (source := source) setup ensureInit identityIndex serverKid).IsQueryBoundP IsSign 0 := by
  unfold RegistrationNativeMldsaCreation.start
  apply isQueryBoundP_bind (n := 0) (m := 0) (ordinary _)
  intro constructed _
  cases selected : constructed.1.1 with
  | none => trivial
  | some created =>
    apply isQueryBoundP_bind (n := 0) (m := 0) (generated .native constructed.2)
    intro generated _
    cases generated.1 with
    | none => trivial
    | some credential =>
      apply isQueryBoundP_bind (n := 0) (m := 0) (ordinary _)
      intro initialized _
      cases initialized.1 <;> try trivial
      rename_i answer
      cases answer <;> trivial

def IsSigningCallback (query : RegistrationNativeRawAdapter.TypedSpec.Domain) : Prop :=
  RegistrationNativeRawAdapter.kind query = (2 : Fin 12) ∨ RegistrationNativeRawAdapter.kind query = (4 : Fin 12)
instance : DecidablePred IsSigningCallback := fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Exactly bundle and build have an ML signing allowance; every other original callback is signing-free. -/
theorem handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : RegistrationNativeExperiment.State n KemSK source) :
    ((RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query).run before).IsQueryBoundP
      IsSign (if IsSigningCallback query then 1 else 0) := by
  cases query with
  | inl coin => exact lifted _ before
  | inr query => cases query with
    | create edPin mlPin keyId => exact create setup checks representation created edPin mlPin keyId before
    | bundle index => exact Bundle.sourceBundle setup checks representation created wire index before
    | build index application =>
      change ((fun result => (result.1, { before with server := result.2 })) <$>
        (RegistrationNativeMldsaServer.build source credential setup (RegistrationNativeWire.ledgerCodec wire) checks wire.encodeResponse index application).run before.server).IsQueryBoundP IsSign 1
      simpa only [isQueryBoundP_map_iff] using
        Server.build source credential setup (RegistrationNativeWire.ledgerCodec wire) checks wire.encodeResponse index application before.server
    | _ => exact lifted _ before

/-- Adaptive typed programs inherit the literal combined bundle/build callback cap. -/
theorem program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : Credential source)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (cap : Nat)
    (bounded : work.IsQueryBoundP IsSigningCallback cap) (before : RegistrationNativeExperiment.State n KemSK source) :
    ((simulateQ (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential) work).run before).IsQueryBoundP IsSign cap :=
  bounded.simulateQ_run_StateT_of_step
    (handler setup checks wire route representation created credential) before

/-- First-candidate stopping preserves the actual signing-slot cap for arbitrary fixed post-stop replies. -/
theorem stopped {Candidate : Type} (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : Credential source)
    (observe : RegistrationNativeMldsaStop.Observer (spec := RegistrationNativeRawAdapter.TypedSpec)
      (State := RegistrationNativeExperiment.State n KemSK source) (Candidate := Candidate))
    (defaultReply : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (cap : Nat)
    (bounded : work.IsQueryBoundP IsSigningCallback cap)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Option Candidate) :
    ((simulateQ (RegistrationNativeMldsaStop.freeze
      (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential) observe defaultReply)
      work).run (before, previous)).IsQueryBoundP IsSign cap := by
  have step (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
      (current : RegistrationNativeExperiment.State n KemSK source × Option Candidate) :
      ((RegistrationNativeMldsaStop.freeze
        (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential) observe defaultReply query).run current).IsQueryBoundP
          IsSign (if IsSigningCallback query then 1 else 0) := by
    rcases current with ⟨current, previous⟩
    cases previous with
    | none =>
        simpa only [RegistrationNativeMldsaStop.freeze, RegistrationNativeMldsaStop.monitor, StateT.run,
          bind_pure_comp, isQueryBoundP_map_iff] using
          handler setup checks wire route representation created credential query current
    | some candidate => trivial
  exact bounded.simulateQ_run_StateT_of_step step (before, previous)
end BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds.Server.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds.Server.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds.Server.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds.Server.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds.Bundle.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds.Bundle.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds.Bundle.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds.Bundle.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds.Bundle.sourceBundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds.Bundle.sourceBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds.create

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds.start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds.start

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds.stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignBounds.stopped
