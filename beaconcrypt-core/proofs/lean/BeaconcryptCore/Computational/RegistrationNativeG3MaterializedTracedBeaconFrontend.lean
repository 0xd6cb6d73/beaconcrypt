-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerKnown
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerFrontend
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconCommon

/-! The actual Beacon material service runs against the same independently stateful key provider in its known108 and public44 interpretations. The finite first-open, installation and all failures retain their complete result, key state, chronological receipts and World. No hidden-cache, unused-role or desired-source condition is a caller premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconFrontend
open RegistrationNativeG3MaterializedTracedServerFrontend (ServiceSpec State known thin keys materialize known_common thin_common)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeG3KnownWorldFrameCommon (Allowed EffectAllowed)
open RegistrationNativePairedServerService (publicCommon)
variable {n : Nat} {KeyState Value : Type}

private theorem every {Index : Type} {spec : OracleSpec Index} (work : OracleComp spec Value) :
    AllQueriesSatisfy work (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private theorem raw_allowed (work : OracleComp RegistrationRawSealBridge.Spec Value) :
    AllQueriesSatisfy (simulateQ (RegistrationNativePairedBeaconService.rawLift (n := n)) work) Allowed :=
  RegistrationNativeHiddenAllocationCore.simulation RegistrationNativePairedBeaconService.rawLift (fun _ => True) Allowed
    (fun _ _ => (allQueriesSatisfy_query_iff _ _).mpr trivial) work (every work)

private theorem after_allowed (owner : Nat) (sender : U64) (reply : RustM RegistrationBeaconRecordExecutor.Result) :
    AllQueriesSatisfy (RegistrationNativePairedBeaconService.after (n := n) owner sender (fun completed => .known completed.kernel) reply)
      EffectAllowed := by
  cases reply with
  | fail error => trivial
  | div => trivial
  | ok reply => cases reply with
    | Err aborted => trivial
    | Ok completed => exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr
        (by simp [EffectAllowed, RegistrationNativeSeedDelayFrames.ReadsSeed])) (fun _ => trivial)

private theorem stage_allowed (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (output : PqxdhServerAuthKeySchedule.Output) :
    AllQueriesSatisfy (RegistrationNativePairedBeaconService.knownStage (n := n) source owner sender descriptor output) Allowed := by
  unfold RegistrationNativePairedBeaconService.knownStage
  exact allQueriesSatisfy_bind (raw_allowed _) (fun reply =>
    RegistrationNativeHiddenAllocationCore.simulation RegistrationHiddenInstall.effectLift EffectAllowed Allowed
      (fun _ allowed => (allQueriesSatisfy_query_iff _ _).mpr allowed) _ (after_allowed owner sender reply))

/-- Actual nonselected known-output Beacon work retains every complete mutable field under the fixed-table interpreter. -/
theorem known_stage (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (output : PqxdhServerAuthKeySchedule.Output) :
    simulateQ (RegistrationNativeG3MaterializedTracedServerCommon.handler true seeds source writer sign)
        (RegistrationNativePairedBeaconService.knownStage source owner sender descriptor output) =
      simulateQ (RegistrationNativeG3MaterializedTracedServerCommon.handler false seeds source writer sign)
        (RegistrationNativePairedBeaconService.knownStage source owner sender descriptor output) :=
  RegistrationNativeG3MaterializedTracedServerKnown.common_program seeds source writer sign _ (stage_allowed source owner sender descriptor output)

/-- Each actual selected or ordinary material reply gives the same Beacon continuation with its exact full Common state. -/
theorem branch (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (choice : RegistrationNativePairedChoice.Choice n) (before : RegistrationNativeG3MaterializedTracedServerCommon.State n) :
    (simulateQ (RegistrationNativeG3MaterializedTracedServerCommon.handler true seeds source writer sign)
      (RegistrationNativePairedBeaconService.publicBranch source owner sender descriptor (materialize seeds choice))).run before =
      (simulateQ (RegistrationNativeG3MaterializedTracedServerCommon.handler false seeds source writer sign)
        (RegistrationNativePairedBeaconService.publicBranch source owner sender descriptor choice)).run before := by
  cases choice with
  | known output => exact congrArg (fun work => work.run before) (known_stage source writer sign seeds owner sender descriptor output)
  | hidden reference => exact RegistrationNativeG3MaterializedTracedBeaconCommon.stage source writer sign owner sender reference.slot descriptor reference.material seeds before

/-- The full actual Beacon admission uses the same independently stateful material provider, retaining every reached key/receipt/World field across all failure branches. -/
theorem admitted (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (message : RegistrationNativeRelatedFamily.Message) (before : State n KeyState) :
    (simulateQ (known source writer sign seeds service)
      (RegistrationNativePairedBeaconService.admitted source owner sender descriptor message)).run before =
      (simulateQ (thin source writer sign seeds service)
        (RegistrationNativePairedBeaconService.admitted source owner sender descriptor message)).run before := by
  simp only [RegistrationNativePairedBeaconService.admitted, simulateQ_bind, simulateQ_spec_query,
    known, thin, StateT.run_bind, bind_map_left]
  apply bind_congr
  intro reached
  rcases reached with ⟨none | choice, after⟩
  · simp only [Option.map_none, simulateQ_pure, StateT.run_pure]
  · simp only [Option.map_some, known_common, thin_common]
    rw [branch source writer sign seeds owner sender descriptor choice after.2]

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconFrontend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconFrontend.known_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconFrontend.known_stage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconFrontend.branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconFrontend.branch
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconFrontend.admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconFrontend.admitted
