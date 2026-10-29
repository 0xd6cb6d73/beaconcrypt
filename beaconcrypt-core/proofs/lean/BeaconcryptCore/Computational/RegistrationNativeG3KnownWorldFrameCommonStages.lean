-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommon

/-! The actual known Server and Beacon common stages use only native publication primitives and known-kernel installation. Their complete receipt/World input-view equations therefore follow from their concrete ASTs, without a supplied allowed-query, cache, role-use or source-simulation condition. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommonStages
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativePairedServerService (Common knownInstall knownAfter knownInstall_native)
open RegistrationNativeG3Common (State handler)
open RegistrationNativeG3KnownWorldFrameCommon (Allowed EffectAllowed view program_input)
open RegistrationNativeHiddenAllocationCore (simulation)
variable {n : Nat} {Encoded Value : Type}

private theorem every {Index : Type} {spec : OracleSpec Index} (work : OracleComp spec Value) :
    AllQueriesSatisfy work (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private theorem publication_allowed (work : OracleComp RegistrationBoundPublication.Spec Value) :
    AllQueriesSatisfy (simulateQ (RegistrationHiddenInstall.publicationLift (n := n)) work) Allowed :=
  simulation RegistrationHiddenInstall.publicationLift (fun _ => True) Allowed
    (fun _ _ => (allQueriesSatisfy_query_iff _ _).mpr trivial) work (every work)

private theorem effects_allowed (work : OracleComp (EnvEffects n) Value) (safe : AllQueriesSatisfy work EffectAllowed) :
    AllQueriesSatisfy (simulateQ RegistrationHiddenInstall.effectLift work) Allowed :=
  simulation RegistrationHiddenInstall.effectLift EffectAllowed Allowed
    (fun _ allowed => (allQueriesSatisfy_query_iff _ _).mpr allowed) work safe

private theorem known_install (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded) :
    AllQueriesSatisfy (knownInstall (n := n) control published) EffectAllowed := by
  cases prepared : peer.begin_peer_insert control published with
  | fail error => simp only [knownInstall, prepared]; trivial
  | div => simp only [knownInstall, prepared]; trivial
  | ok reply => cases reply with
    | Err previous => simp only [knownInstall, prepared]; trivial
    | Ok pending =>
        rw [knownInstall_native control published pending prepared]
        exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr (by simp [EffectAllowed, RegistrationNativeSeedDelayFrames.ReadsSeed])) (fun _ => trivial)

private theorem known_after (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    AllQueriesSatisfy (knownAfter (n := n) control published) EffectAllowed := by
  cases published with
  | fail error => trivial
  | div => trivial
  | ok reply => cases reply with
    | Err previous => trivial
    | Ok published => exact known_install control published

private theorem server_allowed (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) :
    AllQueriesSatisfy (RegistrationNativePairedServerService.knownStage (n := n) encode control initial output) Allowed := by
  unfold RegistrationNativePairedServerService.knownStage
  exact allQueriesSatisfy_bind (publication_allowed _) (fun published => effects_allowed _ (known_after control published))

private theorem raw_allowed (work : OracleComp RegistrationRawSealBridge.Spec Value) :
    AllQueriesSatisfy (simulateQ (RegistrationNativePairedBeaconService.rawLift (n := n)) work) Allowed :=
  simulation RegistrationNativePairedBeaconService.rawLift (fun _ => True) Allowed
    (fun _ _ => (allQueriesSatisfy_query_iff _ _).mpr trivial) work (every work)

private theorem beacon_after (owner : Nat) (sender : U64) (reply : RustM RegistrationBeaconRecordExecutor.Result) :
    AllQueriesSatisfy (RegistrationNativePairedBeaconService.after (n := n) owner sender (fun completed => .known completed.kernel) reply)
      EffectAllowed := by
  cases reply with
  | fail error => trivial
  | div => trivial
  | ok reply => cases reply with
    | Err aborted => trivial
    | Ok completed => exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr (by simp [EffectAllowed, RegistrationNativeSeedDelayFrames.ReadsSeed])) (fun _ => trivial)

private theorem beacon_allowed (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (output : PqxdhServerAuthKeySchedule.Output) :
    AllQueriesSatisfy (RegistrationNativePairedBeaconService.knownStage (n := n) source owner sender descriptor output) Allowed := by
  unfold RegistrationNativePairedBeaconService.knownStage
  exact allQueriesSatisfy_bind (raw_allowed _) (fun reply => effects_allowed _ (beacon_after owner sender reply))

/-- The actual complete known Server stage retains its native outcome, all chronological signing receipts and every semantic World field under the bilateral G3 input view. -/
theorem server_input (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) (before : State n) :
    Prod.map id view <$>
      (simulateQ (handler source writer sign) (RegistrationNativePairedServerService.knownStage encode control initial output)).run before =
      Prod.map id view <$>
        (simulateQ (handler source writer sign) (RegistrationNativePairedServerService.knownStage encode control initial output)).run (view before) :=
  program_input source writer sign _ (server_allowed encode control initial output) before

/-- The actual complete known Beacon first-open stage retains its native outcome, signing receipts and every semantic World field under the same bilateral G3 view. -/
theorem beacon_input (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (output : PqxdhServerAuthKeySchedule.Output) (before : State n) :
    Prod.map id view <$>
      (simulateQ (handler source writer sign) (RegistrationNativePairedBeaconService.knownStage source owner sender descriptor output)).run before =
      Prod.map id view <$>
        (simulateQ (handler source writer sign) (RegistrationNativePairedBeaconService.knownStage source owner sender descriptor output)).run (view before) :=
  program_input source writer sign _ (beacon_allowed source owner sender descriptor output) before

end BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommonStages
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommonStages.server_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommonStages.server_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommonStages.beacon_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommonStages.beacon_input
