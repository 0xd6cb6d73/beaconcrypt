-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerFrontend
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerKnown
import BeaconcryptCore.Computational.RegistrationServerMaterialFrontend

/-! The traced actual Server completion and moved-handle build controllers have the same complete outcomes under known108 and public44 material frontends. Both interpretations call the same independent key service once at the actual demand position. Native occupancy, preflight, signature, writer and insertion failures retain their full states, and no cache or unused-role condition is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerFinite
open RegistrationNativeG3MaterializedTracedServerFrontend (ServiceSpec State known thin materialize known_common thin_common)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativePairedServerService (Common PublicSpec knownInstall knownInstall_native knownAfter knownStage publicBranch publicAdmitted)
open RegistrationNativeG3KnownWorldFrameCommon (Allowed EffectAllowed)
open RegistrationNativeHiddenAllocationCore (simulation)
variable {n : Nat} {KeyState Encoded Value : Type}

private theorem every {Index : Type} {spec : OracleSpec Index} (work : OracleComp spec Value) :
    AllQueriesSatisfy work (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact ⟨trivial, ih⟩

private theorem known_install (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded) :
    AllQueriesSatisfy (knownInstall (n := n) control published) EffectAllowed := by
  cases prepared : peer.begin_peer_insert control published with
  | fail error => simp only [knownInstall, prepared]; trivial
  | div => simp only [knownInstall, prepared]; trivial
  | ok reply => cases reply with
    | Err previous => simp only [knownInstall, prepared]; trivial
    | Ok pending =>
        rw [knownInstall_native control published pending prepared]
        exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr
          (by simp [EffectAllowed, RegistrationNativeSeedDelayFrames.ReadsSeed])) (fun _ => trivial)

private theorem known_after (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    AllQueriesSatisfy (knownAfter (n := n) control published) EffectAllowed := by
  cases published with
  | fail error => trivial
  | div => trivial
  | ok reply => cases reply with
    | Err previous => trivial
    | Ok published => exact known_install control published

private theorem known_stage (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) (seeds : Seeds n) :
    simulateQ (RegistrationNativeG3MaterializedTracedServerCommon.handler true seeds source writer sign) (knownStage encode control initial output) =
      simulateQ (RegistrationNativeG3MaterializedTracedServerCommon.handler false seeds source writer sign) (knownStage encode control initial output) := by
  apply RegistrationNativeG3MaterializedTracedServerKnown.common_program
  unfold knownStage
  apply allQueriesSatisfy_bind
  · exact simulation RegistrationHiddenInstall.publicationLift (fun _ => True) Allowed
      (fun _ _ => (allQueriesSatisfy_query_iff _ _).mpr trivial) _ (every _)
  · intro published
    exact simulation RegistrationHiddenInstall.effectLift EffectAllowed Allowed
      (fun _ allowed => (allQueriesSatisfy_query_iff _ _).mpr allowed) _ (known_after control published)

private theorem branch_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (seeds : Seeds n) (choice : RegistrationNativePairedChoice.Choice n) (before : RegistrationNativeG3MaterializedTracedServerCommon.State n) :
    (simulateQ (RegistrationNativeG3MaterializedTracedServerCommon.handler true seeds source writer sign)
      (publicBranch encode control initial (materialize seeds choice))).run before =
      (simulateQ (RegistrationNativeG3MaterializedTracedServerCommon.handler false seeds source writer sign)
        (publicBranch encode control initial choice)).run before := by
  cases choice with
  | known output => exact congrArg (fun action => action.run before) (known_stage source writer sign encode control initial output seeds)
  | hidden reference => exact RegistrationNativeG3MaterializedTracedServerCommon.stage source writer sign encode control reference.slot initial reference.material seeds before

/-- The actual admitted Server material request retains the same key-service poststate, native result, receipts and entire World. -/
theorem admitted_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : RegistrationNativeRelatedFamily.Message) (seeds : Seeds n)
    (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp)) (before : State n KeyState) :
    (simulateQ (known source writer sign seeds service) (publicAdmitted encode control initial message)).run before =
      (simulateQ (thin source writer sign seeds service) (publicAdmitted encode control initial message)).run before := by
  simp only [publicAdmitted, simulateQ_bind, simulateQ_spec_query, known, thin, StateT.run_bind,
    bind_map_left]
  apply bind_congr
  intro result
  cases selected : result.1 with
  | none => simp only [Option.map_none, simulateQ_pure, StateT.run_pure]
  | some choice =>
      simp only [Option.map_some, known_common, thin_common]
      exact congrArg (fun distribution => (fun reached => (reached.1, (result.2.1, reached.2))) <$> distribution)
        (branch_source source writer sign encode control initial seeds choice result.2.2)

private theorem finish_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (reply : RustM (RegistrationNativePairedServerService.Result Pqxdh.Bytes)) (control : RegistrationServerMaterialFrontend.State) :
    simulateQ (known source writer sign seeds service) ((RegistrationServerMaterialFrontend.finish reply).run control) =
      simulateQ (thin source writer sign seeds service) ((RegistrationServerMaterialFrontend.finish reply).run control) := by
  cases reply with
  | fail error => rfl
  | div => rfl
  | ok reply => cases reply <;> rfl

private theorem peer_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp)) (keyId : U64) :
    known source writer sign seeds service (.inr (.inr (.inr (.peerPresent keyId)))) =
      thin source writer sign seeds service (.inr (.inr (.inr (.peerPresent keyId)))) := rfl

theorem adHash_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp)) (pending : registration.ServerAdHash) :
    simulateQ (known source writer sign seeds service) (RegistrationServerMaterialFrontend.adHash pending) =
      simulateQ (thin source writer sign seeds service) (RegistrationServerMaterialFrontend.adHash pending) := by
  cases requested : pending.request <;> simp only [RegistrationServerMaterialFrontend.adHash, requested] <;> rfl

attribute [local irreducible] known thin publicAdmitted

/-- Actual completion preflight and occupancy precede the same service demand, and every native failure retains the same full state. -/
theorem complete_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (reservePeer : Bool) (ready : RegistrationServerReferenceRoot.Ready) (application : Slice U8)
    (control : RegistrationServerMaterialFrontend.State) (before : State n KeyState) :
    (simulateQ (known source wire.frameWrite sign seeds service)
      ((RegistrationServerMaterialFrontend.complete wire reservePeer ready application).run control)).run before =
      (simulateQ (thin source wire.frameWrite sign seeds service)
        ((RegistrationServerMaterialFrontend.complete wire reservePeer ready application).run control)).run before := by
  simp only [RegistrationServerMaterialFrontend.complete, StateT.run]
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  simp only [simulateQ_bind, RegistrationServerMaterialFrontend.effect, simulateQ_spec_query]
  rw [peer_source]
  change (StateT.run _ before) = StateT.run _ before
  rw [StateT.run_bind, StateT.run_bind]
  apply bind_congr
  intro occupied
  split <;> try rfl
  simp only [simulateQ_bind]
  rw [StateT.run_bind, StateT.run_bind, adHash_source]
  apply bind_congr
  intro hashed
  cases hashResult : hashed.1 with
  | fail error | div => rfl
  | ok reply => cases reply with
    | Err previous => rfl
    | Ok initial =>
      dsimp only
      split
      · simp only [simulateQ_bind]
        rw [StateT.run_bind, StateT.run_bind, admitted_source]
        apply bind_congr
        intro published
        exact congrArg (fun action => action.run published.2)
          (finish_source source wire.frameWrite sign seeds service published.1 control)
      · rfl

/-- Moved-handle build retains the exact current native control and cancellation semantics before the identical complete stage. -/
theorem build_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (reservePeer : Bool) (handle : Nat) (application : Option (Slice U8))
    (control : RegistrationServerMaterialFrontend.State) (before : State n KeyState) :
    (simulateQ (known source wire.frameWrite sign seeds service)
      ((RegistrationServerMaterialFrontend.build wire reservePeer handle application).run control)).run before =
      (simulateQ (thin source wire.frameWrite sign seeds service)
        ((RegistrationServerMaterialFrontend.build wire reservePeer handle application).run control)).run before := by
  simp only [RegistrationServerMaterialFrontend.build, StateT.run]
  cases taken : RegistrationServerMaterialFrontend.take handle control with
  | mk selected current => cases selected with
    | none => rfl
    | some ready => cases application with
      | none => rfl
      | some application => exact complete_source source wire sign seeds service reservePeer ready application current before


end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerFinite

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerFinite.admitted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerFinite.admitted_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerFinite.complete_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerFinite.complete_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerFinite.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerFinite.build_source


/--
info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerFinite.adHash_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerFinite.adHash_source
