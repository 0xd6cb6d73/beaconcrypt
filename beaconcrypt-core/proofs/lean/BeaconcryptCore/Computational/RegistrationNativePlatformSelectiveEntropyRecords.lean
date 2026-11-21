-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEffects
/-! Literal ongoing sends close to the same World record request followed by the actual shared public reservation. Rejection preserves the already reached private World effects and changes only the optional delivered result and platform state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyRecords
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (WorldSpec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePlatformSelectiveEntropyEnvironment (State)
open RegistrationNativePlatformSelectiveEntropyEffects (close close_run bind_source gateWork gate_source liftPlatform record_leaf)
variable {n : Nat} {I KemSK ProviderState Platform Failure : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

private theorem bind_apply {S V W : Type} {m : Type → Type} [Monad m]
    (work : StateT S m V) (next : V → StateT S m W) (before : S) :
    (work >>= next) before = work before >>= fun result => next result.1 result.2 := rfl
private theorem map_apply {S V W : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : V → W) (work : StateT S m V) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem lift_apply {S V : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m V) (before : S) :
    (StateT.lift work : StateT S m V) before = (fun value => (value, before)) <$> work := by
  simpa only [StateT.run, bind_pure_comp] using (StateT.run_lift work before)

def sendLeaf (request : U64 ⊕ Nat) (plaintext : Pqxdh.Bytes) :
    OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK) (Option RawCtxSourceSend.Encrypted) :=
  match request with
  | .inl keyId => RegistrationNativePlatformPublicFrontend.old (.inr (.inl (.inl (plaintext, keyId))))
  | .inr owner => RegistrationNativePlatformPublicFrontend.old (.inr (.inr (owner, .inl plaintext)))
def worldLeaf (request : U64 ⊕ Nat) (plaintext : Pqxdh.Bytes) :
    OracleComp (WorldSpec n) (Option RawCtxSourceSend.Encrypted) :=
  match request with
  | .inl keyId => (WorldSpec n).query (.inr (.inr (.inl (.inl (plaintext, keyId)))))
  | .inr owner => (WorldSpec n).query (.inr (.inr (.inr (owner, .inl plaintext))))
def sendWork (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (request : U64 ⊕ Nat) (plaintext : Pqxdh.Bytes) :
    RegistrationNativePlatformPublicFrontend.M n KemSK Platform source (Option RawCtxSourceSend.Encrypted) := do
  let output ← StateT.lift (sendLeaf request plaintext)
  gateWork reserve (fun value => value.ciphertext.length) output
def worldSend (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (request : U64 ⊕ Nat) (plaintext : Pqxdh.Bytes) :
    StateT (State n KemSK ProviderState Platform source) (OracleComp (WorldSpec n)) (Option RawCtxSourceSend.Encrypted) := do
  let output ← StateT.lift (worldLeaf request plaintext)
  RegistrationNativePlatformGatedRecordInterface.closed
    (RegistrationNativePlatformOrdinaryGate.gate (fun amount => liftPlatform (reserve amount))
      (fun value => value.ciphertext.length) output)

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)

/-- Closing the literal send prefix and public gate retains the complete common source/private state. -/
theorem send_source (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (request : U64 ⊕ Nat) (plaintext : Pqxdh.Bytes) :
    close setup wire sign seed scalar candidate provider (sendWork (n := n) (KemSK := KemSK) (source := source) reserve request plaintext) =
      worldSend reserve request plaintext := by
  unfold sendWork worldSend
  rw [bind_source]
  have first : close (source := source) (Platform := Platform) setup wire sign seed scalar candidate provider
      (StateT.lift (sendLeaf (n := n) (KemSK := KemSK) request plaintext)) = StateT.lift (worldLeaf request plaintext) := by
    funext before
    cases request with
    | inl keyId => exact record_leaf setup wire sign seed scalar candidate provider (.inl (.inl (plaintext,keyId))) before
    | inr owner => exact record_leaf setup wire sign seed scalar candidate provider (.inr (owner,.inl plaintext)) before
  rw [first]
  congr 1
  funext output
  exact gate_source setup wire sign seed scalar candidate provider reserve _ output

private theorem server_body (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (keyId : U64) (plaintext : Pqxdh.Bytes) :
    RegistrationNativePlatformPublicFrontend.record (n := n) (KemSK := KemSK) (source := source) reserve (.inl (.inl (plaintext,keyId))) =
      sendWork reserve (.inl keyId) plaintext := by
  funext before
  simp only [RegistrationNativePlatformPublicFrontend.record, sendWork, sendLeaf, gateWork,
    StateT.run, bind_apply, lift_apply, bind_map_left, bind_pure_comp]
  rfl

/-- Actual Server send uses the literal World request before its actual capacity gate. -/
theorem server_send (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (keyId : U64) (plaintext : Pqxdh.Bytes) :
    close setup wire sign seed scalar candidate provider
      (RegistrationNativePlatformPublicFrontend.record (n := n) (KemSK := KemSK) (source := source) reserve (.inl (.inl (plaintext,keyId)))) =
      worldSend reserve (.inl keyId) plaintext := by
  rw [server_body]
  exact send_source setup wire sign seed scalar candidate provider reserve (.inl keyId) plaintext

private theorem beacon_body (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (index : Nat) (plaintext : Pqxdh.Bytes) (owner : RegistrationNativePublicOwners.Owner source)
    (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (found : before.1.beacons[index]? = some owner) :
    (RegistrationNativePlatformPublicFrontend.record (n := n) (KemSK := KemSK) reserve (.inr (index,.inl plaintext))).run before =
      (sendWork reserve (.inr owner.view.worldOwner) plaintext).run before := by
  simp only [RegistrationNativePlatformPublicFrontend.record, StateT.run, found, sendWork, sendLeaf, gateWork,
    bind_apply, lift_apply, bind_map_left, bind_pure_comp]
  rfl

/-- Existing Beacon sends retain the actual stored physical owner and the complete post-send platform gate. -/
theorem beacon_send (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (index : Nat) (plaintext : Pqxdh.Bytes) (owner : RegistrationNativePublicOwners.Owner source)
    (before : State n KemSK ProviderState Platform source)
    (found : before.1.1.beacons[index]? = some owner) :
    (close setup wire sign seed scalar candidate provider
      (RegistrationNativePlatformPublicFrontend.record reserve (.inr (index,.inl plaintext)))).run before =
      (worldSend reserve (.inr owner.view.worldOwner) plaintext).run before := by
  have actual := congrArg (fun action => action.run before)
    (send_source setup wire sign seed scalar candidate provider (source := source) reserve (.inr owner.view.worldOwner) plaintext)
  rw [close_run, beacon_body reserve index plaintext owner before.1 found]
  exact actual

/-- Server raw receive uses the same literal World request and preserves the complete local state. -/
theorem server_raw (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (raw : Pqxdh.Bytes) (before : State n KemSK ProviderState Platform source) :
    (close setup wire sign seed scalar candidate provider
      (RegistrationNativePlatformPublicFrontend.record reserve (.inl (.inr raw)))).run before =
      (fun result => (result, before)) <$>
        ((WorldSpec n).query (.inr (.inr (.inl (.inr raw)))) : OracleComp (WorldSpec n) _) := by
  have actual := record_leaf setup wire sign seed scalar candidate provider (.inl (.inr raw)) before
  rw [close_run] at actual ⊢
  simp only [RegistrationNativePlatformPublicFrontend.record, StateT.run, lift_apply] at actual ⊢
  convert actual using 1; rfl

/-- Beacon raw receive uses the actual stored physical owner with no platform reservation. -/
theorem beacon_raw (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (index : Nat) (raw : Pqxdh.Bytes) (owner : RegistrationNativePublicOwners.Owner source)
    (before : State n KemSK ProviderState Platform source)
    (found : before.1.1.beacons[index]? = some owner) :
    (close setup wire sign seed scalar candidate provider
      (RegistrationNativePlatformPublicFrontend.record reserve (.inr (index,.inr raw)))).run before =
      (fun result => (result, before)) <$>
        ((WorldSpec n).query (.inr (.inr (.inr (owner.view.worldOwner,.inr raw)))) : OracleComp (WorldSpec n) _) := by
  have actual := record_leaf setup wire sign seed scalar candidate provider (.inr (owner.view.worldOwner,.inr raw)) before
  rw [close_run] at actual ⊢
  simp only [RegistrationNativePlatformPublicFrontend.record, StateT.run, lift_apply, found] at actual ⊢
  convert actual using 1; rfl

/-- A missing source Beacon sends nothing and performs no reservation or World operation. -/
theorem send_missing (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (index : Nat) (plaintext : Pqxdh.Bytes) (before : State n KemSK ProviderState Platform source)
    (missing : before.1.1.beacons[index]? = none) :
    (close setup wire sign seed scalar candidate provider
      (RegistrationNativePlatformPublicFrontend.record reserve (.inr (index,.inl plaintext)))).run before = pure (none,before) := by
  rw [close_run]
  simp only [RegistrationNativePlatformPublicFrontend.record, StateT.run, missing, simulateQ_pure]
  rfl

/-- A missing source Beacon receives nothing and retains all local state without a World operation. -/
theorem raw_missing (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (index : Nat) (raw : Pqxdh.Bytes) (before : State n KemSK ProviderState Platform source)
    (missing : before.1.1.beacons[index]? = none) :
    (close setup wire sign seed scalar candidate provider
      (RegistrationNativePlatformPublicFrontend.record reserve (.inr (index,.inr raw)))).run before = pure (.None,before) := by
  rw [close_run]
  simp only [RegistrationNativePlatformPublicFrontend.record, StateT.run, missing, simulateQ_pure]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyRecords

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyRecords.send_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyRecords.send_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyRecords.server_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyRecords.server_send

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyRecords.beacon_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyRecords.beacon_send

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyRecords.server_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyRecords.server_raw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyRecords.beacon_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyRecords.beacon_raw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyRecords.send_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyRecords.send_missing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyRecords.raw_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyRecords.raw_missing
